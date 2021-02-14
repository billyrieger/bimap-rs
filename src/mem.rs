use alloc::rc::Rc;
use core::borrow::Borrow;
use core::ops::{Bound, Deref};

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ref<T> {
    ptr: Rc<T>,
}

impl<T> Ref<T> {
    pub fn new(value: T) -> (Self, Self) {
        let ptr = Rc::new(value);
        (Self { ptr: ptr.clone() }, Self { ptr })
    }

    pub fn join(l: Self, r: Self) -> T {
        assert!(Rc::ptr_eq(&l.ptr, &r.ptr));
        drop(r);
        Rc::try_unwrap(l.ptr).ok().unwrap()
    }
}

impl<T> Deref for Ref<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.ptr
    }
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Wrapper<T: ?Sized>(T);

impl<T: ?Sized> Wrapper<T> {
    pub fn wrap(value: &T) -> &Self {
        // SAFETY: Wrapper<T> is #[repr(transparent)].
        unsafe { &*(value as *const T as *const Self) }
    }

    pub fn wrap_bound(bound: Bound<&T>) -> Bound<&Self> {
        match bound {
            Bound::Included(t) => Bound::Included(Self::wrap(t)),
            Bound::Excluded(t) => Bound::Excluded(Self::wrap(t)),
            Bound::Unbounded => Bound::Unbounded,
        }
    }
}

impl<K, Q> Borrow<Wrapper<Q>> for Ref<K>
where
    K: Borrow<Q>,
    Q: ?Sized,
{
    fn borrow(&self) -> &Wrapper<Q> {
        // Rc<K>: Borrow<K> from the standard library
        let k: &K = self.ptr.borrow();
        // K: Borrow<Q> from the impl bounds
        let q: &Q = k.borrow();

        Wrapper::wrap(q)
    }
}
