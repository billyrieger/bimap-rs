use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

/// A bijective map backed by `std::collections::HashMap`.
struct BiHashMap<L, R> {
    left2right: HashMap<Rc<L>, Rc<R>>,
    right2left: HashMap<Rc<R>, Rc<L>>,
}

impl<L, R> Clone for BiHashMap<L, R>
where
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> BiHashMap<L, R> {
        BiHashMap {
            left2right: self.left2right.clone(),
            right2left: self.right2left.clone(),
        }
    }
}

impl<L, R> PartialEq for BiHashMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn eq(&self, other: &BiHashMap<L, R>) -> bool {
        self.left2right == other.left2right && self.right2left == other.right2left
    }
}

impl<L, R> Eq for BiHashMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
}

impl<L, R> BiHashMap<L, R> {}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
