use std::collections::HashMap;
use std::rc::Rc;

/// A bijective map backed by `std::collections::HashMap`.
struct BiHashMap<L, R> {
    left2right: HashMap<Rc<L>, Rc<R>>,
    right2left: HashMap<Rc<R>, Rc<L>>,
}

impl<L, R> BiHashMap<L, R> {}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
