use std::iter;
use std::marker::PhantomData;
use std::ops::{Index};
use std::borrow::Borrow;
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::cmp::Ordering;

use fixedbitset::{Ones, FixedBitSet};

use super::IntegerId;

#[derive(Clone)]
pub struct IdSet<T: IntegerId> {
    handle: FixedBitSet,
    len: usize,
    marker: PhantomData<T>
}
impl<T: IntegerId> IdSet<T> {
    #[inline]
    pub fn new() -> IdSet<T> {
        IdSet::with_capacity(0)
    }
    #[inline]
    pub fn with_capacity(indexes: usize) -> IdSet<T> {
        IdSet {
            handle: FixedBitSet::with_capacity(indexes),
            len: 0,
            marker: PhantomData
        }
    }
    /// Inserts the specified element into the set,
    /// returning `true` if it was already in the set and `false` if it wasn't.
    #[inline]
    pub fn insert<Q: Borrow<T>>(&mut self, value: Q) -> bool {
        let value = value.borrow();
        let id = value.id() as usize;
        if id < self.handle.len() {
            let was_present = self.handle.put(id);
            self.len += !was_present as usize;
            was_present
        } else {
            self.insert_fallback(id);
            false
        }
    }
    #[inline(never)] #[cold]
    fn insert_fallback(&mut self, id: usize) {
        assert!(id >= self.handle.len());
        let old_len = self.handle.len();
        self.handle.grow((id + 1).max(old_len * 2));
        debug_assert!(!self.handle.contains(id));
        self.handle.insert(id);
        self.len += 1

    }
    /// Remove the specified value from the set if it is present,
    /// returning whether or not it was present.
    #[inline]
    pub fn remove<Q: Borrow<T>>(&mut self, value: Q) -> bool {
        let value = value.borrow();
        if self.handle.contains(value.id() as usize) {
            self.handle.set(value.id() as usize, false);
            self.len -= 1;
            true
        } else {
            false
        }
    }
    /// Check if this set contains the specified value
    #[inline]
    pub fn contains<Q: Borrow<T>>(&self, value: Q) -> bool {
        let value = value.borrow();
        self.handle.contains(value.id() as usize)
    }
    #[inline]
    pub fn iter(&self) -> Iter<T> {
        Iter {
            len: self.len,
            handle: self.handle.ones(),
            marker: PhantomData
        }
    }
    #[inline]
    pub fn clear(&mut self) {
        self.handle.clear();
        self.len = 0;
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut func: F) {
        let mut removed = 0;
        for (word_index, word) in self.handle.as_mut_slice().iter_mut().enumerate() {
            let (updated_word, word_removed) = retain_word(*word, |bit| {
                let id = (word_index * 32) as u64 + (bit as u64);
                let key = T::from_id(id);
                func(&key)
            });
            *word = updated_word;
            removed += word_removed as usize;
        }
        assert!(removed <= self.len);
        self.len -= removed;
    }
}
#[inline]
fn retain_word<F: FnMut(u32) -> bool>(original_word: u32, mut func: F) -> (u32, u32) {
    let mut remaining = original_word;
    let mut result = original_word;
    let mut removed = 0;
    while remaining != 0 {
        let bit = remaining.trailing_zeros();
        let mask = 1u32 << bit;
        debug_assert_ne!(result & mask, 0);
        if !func(bit) {
            result &= !mask;
            removed += 1;
        }
        remaining &= !mask;
    }
    debug_assert!(removed <= 32);
    (result, removed)
}
impl<T: IntegerId> Default for IdSet<T> {
    #[inline]
    fn default() -> Self {
        IdSet::new()
    }
}
impl<T: IntegerId + PartialEq> PartialEq for IdSet<T> {
    #[inline]
    fn eq(&self, other: &IdSet<T>) -> bool {
        self.len == other.len && self.handle == other.handle
    }
}
impl<T: IntegerId + Eq> Eq for IdSet<T> {}
impl<T: IntegerId> Debug for IdSet<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}
impl<'a, T: IntegerId + 'a> iter::Extend<&'a T> for IdSet<T> {
    #[inline]
    fn extend<I: IntoIterator<Item=&'a T>>(&mut self, iter: I) {
        for value in iter.into_iter() {
            self.insert(value);
        }
    }
}
impl<T: IntegerId> iter::Extend<T> for IdSet<T> {
    #[inline]
    fn extend<I: IntoIterator<Item=T>>(&mut self, iter: I) {
        for value in iter.into_iter() {
            self.insert(value);
        }
    }
}
impl<T: IntegerId> iter::FromIterator<T> for IdSet<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut result = IdSet::with_capacity(iter.size_hint().1.unwrap_or(0));
        result.extend(iter);
        result
    }
}

impl<'a, T: IntegerId + 'a> iter::FromIterator<&'a T> for IdSet<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item=&'a T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut result = IdSet::with_capacity(iter.size_hint().1.unwrap_or(0));
        result.extend(iter);
        result
    }
}

impl<'a, T: IntegerId + 'a> IntoIterator for &'a IdSet<T> {
    type Item = T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, T: IntegerId + 'a> Index<&'a T> for IdSet<T> {
    type Output = bool;

    #[inline]
    fn index(&self, index: &'a T) -> &Self::Output {
        &self.handle[index.id() as usize]
    }
}
impl<'a, T: IntegerId + 'a> Index<T> for IdSet<T> {
    type Output = bool;

    #[inline]
    fn index(&self, index: T) -> &Self::Output {
        &self.handle[index.id() as usize]
    }
}
impl<T: IntegerId + Hash> Hash for IdSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        for value in self.iter() {
            value.hash(state);
        }
    }
}
impl<T: IntegerId + PartialOrd> PartialOrd for IdSet<T> {
    #[inline]
    fn partial_cmp(&self, other: &IdSet<T>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}
impl<T: IntegerId + Ord> Ord for IdSet<T> {
    #[inline]
    fn cmp(&self, other: &IdSet<T>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

pub struct Iter<'a, T: IntegerId + 'a> {
    len: usize,
    handle: Ones<'a>,
    marker: PhantomData<&'a T>
}
impl<'a, T: IntegerId + 'a> Iterator for Iter<'a, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.handle.next() {
            Some(index) => {
                self.len -= 1;
                Some(T::from_id(index as u64))
            },
            None => {
                debug_assert_eq!(self.len, 0);
                None
            }
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
    #[inline]
    fn count(self) -> usize where Self: Sized {
        self.len
    }
}
impl<'a, T: IntegerId + 'a> iter::ExactSizeIterator for Iter<'a, T> {}
impl<'a, T: IntegerId + 'a> iter::FusedIterator for Iter<'a, T> {}

