#![doc = include_str!("../README.md")]

mod pair;
pub use pair::{Pair};

mod vs;
pub use vs::{Vs, VsPosition};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Iter<T> {
    state: Option<(T, Option<T>)>,
}

impl<T> Iter<T> {
    fn new(a: T, b: T) -> Self {
        Self {
            state: Some((b, Some(a))),
        }
    }
}

impl<T> Iterator for Iter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, ref mut inner @ Some(_))) = self.state {
            inner.take()
        } else if self.state.is_some() {
            self.state.take().map(|slot| slot.0)
        } else {
            None
        }
    }
}
