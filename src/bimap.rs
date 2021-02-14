use core::marker::PhantomData;

use crate::mem::Ref;
use crate::traits::*;

pub enum Overwritten<L, R> {
    Zero,
    One((L, R)),
    Two((L, R), (L, R)),
}

/// A generic bidirectional map.
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BiMap<LMap, RMap> {
    lmap: LMap,
    rmap: RMap,
}

impl<L, R, LMap, RMap> BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    pub fn new() -> Self {
        Self {
            lmap: LMap::new(),
            rmap: RMap::new(),
        }
    }

    pub fn iter_left<'a>(&'a self) -> IterLeft<'a, LMap::MapIter<'a, L, R>> {
        IterLeft {
            iter: self.lmap.map_iter(),
            marker: PhantomData,
        }
    }

    pub fn iter_right<'a>(&'a self) -> IterRight<'a, RMap::MapIter<'a, R, L>> {
        IterRight {
            iter: self.rmap.map_iter(),
            marker: PhantomData,
        }
    }

    pub fn contains_left<Q: ?Sized>(&self, l: &Q) -> bool
    where
        LMap: Contains<Q>,
    {
        self.lmap.contains(l)
    }

    pub fn contains_right<Q: ?Sized>(&self, r: &Q) -> bool
    where
        RMap: Contains<Q>,
    {
        self.rmap.contains(r)
    }

    pub fn get_left<Q: ?Sized>(&self, l: &Q) -> Option<&R>
    where
        LMap: Get<Q>,
    {
        self.lmap.get(l).map(|r| &**r)
    }

    pub fn get_right<Q: ?Sized>(&self, r: &Q) -> Option<&L>
    where
        RMap: Get<Q>,
    {
        self.rmap.get(r).map(|l| &**l)
    }

    pub fn remove_left<Q: ?Sized>(&mut self, l: &Q) -> Option<(L, R)>
    where
        LMap: Remove<Q>,
    {
        self.lmap.remove(l).map(|(l0, r0)| {
            let (r1, l1) = self.rmap.remove(&r0).unwrap();
            (Ref::join(l0, l1), Ref::join(r0, r1))
        })
    }

    pub fn remove_right<Q: ?Sized>(&mut self, r: &Q) -> Option<(L, R)>
    where
        RMap: Remove<Q>,
    {
        self.rmap.remove(r).map(|(r0, l0)| {
            let (l1, r1) = self.lmap.remove(&l0).unwrap();
            (Ref::join(l0, l1), Ref::join(r0, r1))
        })
    }

    pub fn insert(&mut self, l: L, r: R) -> Overwritten<L, R> {
        let overwritten = match (self.remove_left(&l), self.remove_right(&r)) {
            (None, None) => Overwritten::Zero,
            (Some(pair), None) | (None, Some(pair)) => Overwritten::One(pair),
            (Some(lpair), Some(rpair)) => Overwritten::Two(lpair, rpair),
        };
        unsafe {
            self.insert_unchecked(l, r);
        }
        overwritten
    }

    pub fn try_insert(&mut self, l: L, r: R) -> Result<(), (L, R)> {
        if self.lmap.contains(&l) || self.rmap.contains(&r) {
            Err((l, r))
        } else {
            unsafe {
                self.insert_unchecked(l, r);
            }
            Ok(())
        }
    }

    pub unsafe fn insert_unchecked(&mut self, l: L, r: R) {
        let (l0, l1) = Ref::new(l);
        let (r0, r1) = Ref::new(r);
        self.lmap.insert(l0, r0);
        self.rmap.insert(r1, l1);
    }
}

impl<L, R, LMap, RMap> Clone for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        let mut new = Self {
            lmap: LMap::new(),
            rmap: RMap::new(),
        };
        for (l, r) in self.lmap.map_iter() {
            unsafe {
                new.insert_unchecked((*l).clone(), (*r).clone());
            }
        }
        new
    }
}

#[derive(Clone, Debug)]
pub struct IterLeft<'a, I> {
    iter: I,
    marker: PhantomData<&'a ()>,
}

impl<'a, L: 'a, R: 'a, I> Iterator for IterLeft<'a, I>
where
    I: Iterator<Item = (&'a L, &'a R)>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Clone, Debug)]
pub struct IterRight<'a, I> {
    iter: I,
    marker: PhantomData<&'a ()>,
}

impl<'a, L: 'a, R: 'a, I> Iterator for IterRight<'a, I>
where
    I: Iterator<Item = (&'a R, &'a L)>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(r, l)| (l, r))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use crate::btree_map::BTreeKind;
    use crate::hash_map::HashKind;
    use crate::Generic;

    #[test]
    fn two_kinds() {
        let mut a = Generic::<_, _, HashKind, BTreeKind>::new();

        a.insert('a', 10);
        a.insert('b', 5);
        a.insert('c', 20);
        a.insert('z', 40);

        println!("iterating left");
        for (l, r) in a.iter_left() {
            println!("{:?}", (l, r));
        }

        println!("iterating right");
        for (l, r) in a.iter_right() {
            println!("{:?}", (l, r));
        }
    }
}
