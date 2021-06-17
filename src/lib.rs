use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

mod private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for u16 {}
}

thread_local! {
    static CURRENT_TAG_U8: Cell<u8> = Cell::new(u8::default());
    static CURRENT_TAG_U16: Cell<u16> = Cell::new(u16::default());
}

pub trait Tag: Copy + Into<usize> + private::Sealed + Sized {
    type Array: AsRef<[TagCounters]> + Sized;
    const ARRAY: <Self as Tag>::Array;
    const LAYOUT: Layout;

    unsafe fn read(ptr: *const u8) -> Self;

    unsafe fn write(&self, ptr: *mut u8);

    fn get() -> Self;

    fn set(tag: Self) -> Self;
}

impl Tag for u8 {
    type Array = [TagCounters; 2usize.pow(Self::BITS)];
    const ARRAY: <Self as Tag>::Array =
        unsafe { std::mem::transmute([0u8; std::mem::size_of::<<Self as Tag>::Array>()]) };
    const LAYOUT: Layout = Layout::new::<[u8; std::mem::size_of::<Self>()]>();

    #[inline]
    unsafe fn read(ptr: *const u8) -> Self {
        Self::from_ne_bytes(std::ptr::read_unaligned(ptr as *const _))
    }

    #[inline]
    unsafe fn write(&self, ptr: *mut u8) {
        std::ptr::write_unaligned(ptr as *mut _, self.to_ne_bytes());
    }

    #[inline]
    fn get() -> Self {
        CURRENT_TAG_U8.with(|current| current.get())
    }

    #[inline]
    fn set(tag: Self) -> Self {
        CURRENT_TAG_U8.with(|current| current.replace(tag))
    }
}

impl Tag for u16 {
    type Array = [TagCounters; 2usize.pow(Self::BITS)];
    const ARRAY: <Self as Tag>::Array =
        unsafe { std::mem::transmute([0u8; std::mem::size_of::<<Self as Tag>::Array>()]) };
    const LAYOUT: Layout = Layout::new::<[u8; std::mem::size_of::<Self>()]>();

    #[inline]
    unsafe fn read(ptr: *const u8) -> Self {
        Self::from_ne_bytes(std::ptr::read_unaligned(ptr as *const _))
    }

    #[inline]
    unsafe fn write(&self, ptr: *mut u8) {
        std::ptr::write_unaligned(ptr as *mut _, self.to_ne_bytes());
    }

    #[inline]
    fn get() -> Self {
        CURRENT_TAG_U16.with(|current| current.get())
    }

    #[inline]
    fn set(tag: Self) -> Self {
        CURRENT_TAG_U16.with(|current| current.replace(tag))
    }
}

#[derive(Debug)]
pub struct TagCounters {
    cummulated_wrapped_count: AtomicUsize,
    cummulated_memory_size: AtomicUsize,
    live_memory_size: AtomicUsize,
    allocations_count: AtomicUsize,
    deallocations_count: AtomicUsize,
}

impl TagCounters {
    #[inline]
    fn add(&self, size: usize) {
        let old = self
            .cummulated_memory_size
            .fetch_add(size, Ordering::Relaxed);
        if old.overflowing_add(size).1 {
            let old = self
                .cummulated_wrapped_count
                .fetch_add(1, Ordering::Relaxed);
            let _ = old + 1;
        }
        let old = self.live_memory_size.fetch_add(size, Ordering::Relaxed);
        let _ = old + size;
        let old = self.allocations_count.fetch_add(1, Ordering::Relaxed);
        let _ = old + 1;
    }

    #[inline]
    fn sub(&self, size: usize) {
        let old = self.live_memory_size.fetch_sub(size, Ordering::Relaxed);
        let _ = old - size;
        let old = self.deallocations_count.fetch_add(1, Ordering::Relaxed);
        let _ = old + 1;
    }

    #[inline]
    pub fn cummulated_memory(&self) -> (usize, usize) {
        (
            self.cummulated_wrapped_count.load(Ordering::Relaxed),
            self.cummulated_memory_size.load(Ordering::Relaxed),
        )
    }

    #[inline]
    pub fn live_memory(&self) -> usize {
        self.live_memory_size.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn allocations(&self) -> usize {
        self.allocations_count.load(Ordering::Relaxed)
    }

    #[inline]
    pub fn deallocations(&self) -> usize {
        self.deallocations_count.load(Ordering::Relaxed)
    }
}

#[derive(Debug)]
pub struct TrackingAllocator<T: Tag, A = System> {
    inner: A,
    counters: T::Array,
}

impl TrackingAllocator<u8, System> {
    #[inline]
    pub const fn new() -> Self {
        Self::with_allocator(System)
    }
}

impl TrackingAllocator<u16, System> {
    #[inline]
    pub const fn new() -> Self {
        Self::with_allocator(System)
    }
}

impl<A> TrackingAllocator<u8, A> {
    #[inline]
    pub const fn with_allocator(inner: A) -> Self {
        Self {
            inner,
            counters: u8::ARRAY,
        }
    }
}

impl<A> TrackingAllocator<u16, A> {
    #[inline]
    pub const fn with_allocator(inner: A) -> Self {
        Self {
            inner,
            counters: u16::ARRAY,
        }
    }
}

impl<T: Tag, A> TrackingAllocator<T, A> {
    #[inline]
    pub fn get_counters(&self, tag: T) -> &TagCounters {
        let tag: usize = tag.into();
        unsafe { self.counters.as_ref().get_unchecked(tag) }
    }

    #[inline]
    pub fn total_live_memory(&self) -> usize {
        let mut total = 0;
        for counter in self.counters.as_ref() {
            let counter = counter.live_memory();
            total += counter;
        }
        total
    }

    #[inline]
    pub fn with<R, F: FnOnce() -> R>(&self, tag: T, f: F) -> R {
        let tag = T::set(tag);
        let val = f();
        T::set(tag);
        val
    }
}

unsafe impl<T: Tag, A: GlobalAlloc> GlobalAlloc for TrackingAllocator<T, A> {
    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let (layout, offset) = match layout.extend(T::LAYOUT) {
            Ok((layout, offset)) => (layout, offset),
            Err(_) => return std::ptr::null_mut(),
        };
        let ptr = self.inner.alloc_zeroed(layout);
        if !ptr.is_null() {
            let tag = T::get();
            tag.write(ptr.add(offset));
            self.get_counters(tag).add(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let (layout, offset) = match layout.extend(T::LAYOUT) {
            Ok((layout, offset)) => (layout, offset),
            Err(_) => return std::ptr::null_mut(),
        };
        let ptr = self.inner.alloc(layout);
        if !ptr.is_null() {
            let tag = T::get();
            tag.write(ptr.add(offset));
            self.get_counters(tag).add(layout.size());
        }
        ptr
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        assert_ne!(ptr, std::ptr::null_mut());
        let (layout, offset) = match layout.extend(T::LAYOUT) {
            Ok((layout, offset)) => (layout, offset),
            Err(_) => unreachable!(),
        };
        let tag = T::read(ptr.add(offset));
        self.inner.dealloc(ptr, layout);
        self.get_counters(tag).sub(layout.size());
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let (tagged_layout, offset) = match layout.extend(T::LAYOUT) {
            Ok((layout, offset)) => (layout, offset),
            Err(_) => return std::ptr::null_mut(),
        };
        let old_tag = T::read(ptr.add(offset));
        let old_size = tagged_layout.size();

        let (new_layout, offset) =
            match Layout::from_size_align_unchecked(new_size, layout.align()).extend(T::LAYOUT) {
                Ok((layout, offset)) => (layout, offset),
                Err(_) => return std::ptr::null_mut(),
            };
        debug_assert_eq!(
            new_layout,
            // System::realloc will compute this layout
            Layout::from_size_align_unchecked(new_layout.size(), tagged_layout.align())
        );
        let ptr = self.inner.realloc(ptr, tagged_layout, new_layout.size());
        if !ptr.is_null() {
            let new_tag = T::get();
            self.get_counters(old_tag).sub(old_size);
            new_tag.write(ptr.add(offset));
            self.get_counters(new_tag).add(new_layout.size());
        }
        ptr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[global_allocator]
    static ALLOCATOR: TrackingAllocator<u8> = TrackingAllocator::<u8>::new();

    #[test]
    fn layout_of_tag() {
        assert_eq!(u8::LAYOUT.align(), 1);
        assert_eq!(u8::LAYOUT.size(), 1);
        assert_eq!(u16::LAYOUT.align(), 1);
        assert_eq!(u16::LAYOUT.size(), 2);
    }

    #[test]
    fn size_of_allocator() {
        assert_eq!(std::mem::size_of::<TrackingAllocator<u8>>(), 10240);
        assert_eq!(std::mem::size_of::<TrackingAllocator<u16>>(), 2621440);
    }

    #[test]
    fn allocate_box() {
        const TAG: u8 = 1;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Box::new(42usize));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 9);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }

    #[test]
    fn allocate_rc() {
        use std::rc::Rc;

        const TAG: u8 = 2;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Rc::new(42usize));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 25);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }

    #[test]
    fn allocate_arc() {
        use std::sync::Arc;

        const TAG: u8 = 3;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Arc::new(42usize));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 25);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }

    #[test]
    fn allocate_boxed_slice() {
        const TAG: u8 = 4;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Box::<[usize]>::from(vec![42usize]));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 9);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }

    #[test]
    fn allocate_rced_slice() {
        use std::rc::Rc;

        const TAG: u8 = 5;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Rc::<[usize]>::from(vec![42usize]));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 25);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }

    #[test]
    fn allocate_arced_slice() {
        use std::sync::Arc;

        const TAG: u8 = 6;

        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 0);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
        let val = ALLOCATOR.with(TAG, || Arc::<[usize]>::from(vec![42usize]));
        println!("val: {:#?}", val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 1);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 25);
        drop(val);
        assert_eq!(ALLOCATOR.get_counters(TAG).allocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).deallocations(), 2);
        assert_eq!(ALLOCATOR.get_counters(TAG).live_memory(), 0);
    }
}
