//! A Non-empty growable vector.
//!
//! # Examples
//!
//! ```
//! use nonempty::NonEmpty;
//!
//! let mut l = NonEmpty::from((42, vec![36, 58]));
//!
//! assert_eq!(l.first(), &42);
//!
//! l.push(9001);
//!
//! assert_eq!(l.last(), &9001);
//!
//! let v: Vec<i32> = l.into();
//! assert_eq!(v, vec![42, 36, 58, 9001]);
//! ```
use std::cmp::Ordering;
use std::mem;
use std::{iter, vec};

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NonEmpty<T>(T, Vec<T>);

impl<T> NonEmpty<T> {
    /// Alias for [`NonEmpty::singleton`].
    pub const fn new(e: T) -> Self {
        Self::singleton(e)
    }

    /// Create a new non-empty list with an initial element.
    pub const fn singleton(e: T) -> Self {
        NonEmpty(e, Vec::new())
    }

    /// Always returns false.
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Get the first element. Never fails.
    pub const fn first(&self) -> &T {
        &self.0
    }

    /// Get the mutable reference to the first element. Never fails.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::new(42);
    /// let head = non_empty.first_mut();
    /// *head += 1;
    /// assert_eq!(non_empty.first(), &43);
    ///
    /// let mut non_empty = NonEmpty::from((1, vec![4, 2, 3]));
    /// let head = non_empty.first_mut();
    /// *head *= 42;
    /// assert_eq!(non_empty.first(), &42);
    /// ```
    pub fn first_mut(&mut self) -> &mut T {
        &mut self.0
    }

    /// Get the possibly-empty tail of the list.
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new(42);
    /// assert_eq!(non_empty.tail(), &[]);
    ///
    /// let non_empty = NonEmpty::from((1, vec![4, 2, 3]));
    /// assert_eq!(non_empty.tail(), &[4, 2, 3]);
    /// ```
    pub fn tail(&self) -> &[T] {
        &self.1
    }

    /// Push an element to the end of the list.
    pub fn push(&mut self, e: T) {
        self.1.push(e)
    }

    /// Pop an element from the end of the list.
    pub fn pop(&mut self) -> Option<T> {
        self.1.pop()
    }

    /// Inserts an element at position index within the vector, shifting all elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if index > len.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::from((1, vec![2, 3]));
    /// non_empty.insert(1, 4);
    /// assert_eq!(non_empty, NonEmpty::from((1, vec![4, 2, 3])));
    /// non_empty.insert(4, 5);
    /// assert_eq!(non_empty, NonEmpty::from((1, vec![4, 2, 3, 5])));
    /// non_empty.insert(0, 42);
    /// assert_eq!(non_empty, NonEmpty::from((42, vec![1, 4, 2, 3, 5])));
    /// ```
    pub fn insert(&mut self, index: usize, element: T) {
        let len = self.len();
        assert!(index <= len);

        if index == 0 {
            let head = mem::replace(&mut self.0, element);
            self.1.insert(0, head);
        } else {
            self.1.insert(index - 1, element);
        }
    }

    /// Get the length of the list.
    pub fn len(&self) -> usize {
        self.1.len() + 1
    }

    /// Get the last element. Never fails.
    pub fn last(&self) -> &T {
        match self.1.last() {
            None => &self.0,
            Some(e) => e,
        }
    }

    /// Get the last element mutably.
    pub fn last_mut(&mut self) -> &mut T {
        match self.1.last_mut() {
            None => &mut self.0,
            Some(e) => e,
        }
    }

    /// Check whether an element is contained in the list.
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut l = NonEmpty::from((42, vec![36, 58]));
    ///
    /// assert!(l.contains(&42));
    /// assert!(!l.contains(&101));
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|e| e == x)
    }

    /// Get an element by index.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            Some(&self.0)
        } else {
            self.1.get(index - 1)
        }
    }

    /// Get an element by index, mutably.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index == 0 {
            Some(&mut self.0)
        } else {
            self.1.get_mut(index - 1)
        }
    }

    /// Truncate the list to a certain size. Must be greater than `0`.
    pub fn truncate(&mut self, len: usize) {
        assert!(len >= 1);
        self.1.truncate(len - 1);
    }

    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut l = NonEmpty::from((42, vec![36, 58]));
    ///
    /// let mut l_iter = l.iter();
    ///
    /// assert_eq!(l_iter.next(), Some(&42));
    /// assert_eq!(l_iter.next(), Some(&36));
    /// assert_eq!(l_iter.next(), Some(&58));
    /// assert_eq!(l_iter.next(), None);
    /// ```
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &T> + 'a {
        iter::once(&self.0).chain(self.1.iter())
    }

    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut l = NonEmpty::new(42);
    /// l.push(36);
    /// l.push(58);
    ///
    /// for i in l.iter_mut() {
    ///     *i *= 10;
    /// }
    ///
    /// let mut l_iter = l.iter();
    ///
    /// assert_eq!(l_iter.next(), Some(&420));
    /// assert_eq!(l_iter.next(), Some(&360));
    /// assert_eq!(l_iter.next(), Some(&580));
    /// assert_eq!(l_iter.next(), None);
    /// ```
    pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = &mut T> + 'a {
        iter::once(&mut self.0).chain(self.1.iter_mut())
    }

    /// Often we have a `Vec` (or slice `&[T]`) but want to ensure that it is `NonEmpty` before
    /// proceeding with a computation. Using `from_slice` will give us a proof
    /// that we have a `NonEmpty` in the `Some` branch, otherwise it allows
    /// the caller to handle the `None` case.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty_vec = NonEmpty::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(non_empty_vec, Some(NonEmpty::from((1, vec![2, 3, 4, 5]))));
    ///
    /// let empty_vec: Option<NonEmpty<&u32>> = NonEmpty::from_slice(&[]);
    /// assert!(empty_vec.is_none());
    /// ```
    pub fn from_slice(slice: &[T]) -> Option<NonEmpty<T>>
    where
        T: Clone,
    {
        slice
            .split_first()
            .map(|(h, t)| NonEmpty(h.clone(), t.into()))
    }

    /// Deconstruct a `NonEmpty` into its head and tail.
    /// This operation never fails since we are guranteed
    /// to have a head element.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::from((1, vec![2, 3, 4, 5]));
    ///
    /// // Guaranteed to have the head and we also get the tail.
    /// assert_eq!(non_empty.split_first(), (&1, &[2, 3, 4, 5][..]));
    ///
    /// let non_empty = NonEmpty::new(1);
    ///
    /// // Guaranteed to have the head element.
    /// assert_eq!(non_empty.split_first(), (&1, &[][..]));
    /// ```
    pub fn split_first(&self) -> (&T, &[T]) {
        (&self.0, &self.1)
    }

    /// Deconstruct a `NonEmpty` into its first, last, and
    /// middle elements, in that order.
    ///
    /// If there is only one element then first == last.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::from((1, vec![2, 3, 4, 5]));
    ///
    /// // Guaranteed to have the last element and the elements
    /// // preceding it.
    /// assert_eq!(non_empty.split(), (&1, &[2, 3, 4][..], &5));
    ///
    /// let non_empty = NonEmpty::new(1);
    ///
    /// // Guaranteed to have the last element.
    /// assert_eq!(non_empty.split(), (&1, &[][..], &1));
    /// ```
    pub fn split(&self) -> (&T, &[T], &T) {
        match self.1.split_last() {
            None => (&self.0, &[], &self.0),
            Some((last, middle)) => (&self.0, middle, last),
        }
    }

    /// Append a `Vec` to the tail of the `NonEmpty`.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::new(1);
    /// let mut vec = vec![2, 3, 4, 5];
    /// non_empty.append(&mut vec);
    ///
    /// let mut expected = NonEmpty::from((1, vec![2, 3, 4, 5]));
    ///
    /// assert_eq!(non_empty, expected);
    /// ```
    pub fn append(&mut self, other: &mut Vec<T>) {
        self.1.append(other)
    }

    /// A structure preserving `map`. This is useful for when
    /// we wish to keep the `NonEmpty` structure guaranteeing
    /// that there is at least one element. Otherwise, we can
    /// use `nonempty.iter().map(f)`.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::from((1, vec![2, 3, 4, 5]));
    ///
    /// let squares = non_empty.map(|i| i * i);
    ///
    /// let expected = NonEmpty::from((1, vec![4, 9, 16, 25]));
    ///
    /// assert_eq!(squares, expected);
    /// ```
    pub fn map<U, F>(&self, f: F) -> NonEmpty<U>
    where
        F: Fn(&T) -> U,
    {
        NonEmpty(f(&self.0), self.1.iter().map(f).collect())
    }

    /// Binary searches this sorted non-empty vector for a given element.
    ///
    /// If the value is found then Result::Ok is returned, containing the index of the matching element.
    /// If there are multiple matches, then any one of the matches could be returned.
    ///
    /// If the value is not found then Result::Err is returned, containing the index where a
    /// matching element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::from((0, vec![1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]));
    /// assert_eq!(non_empty.binary_search(&0),   Ok(0));
    /// assert_eq!(non_empty.binary_search(&13),  Ok(9));
    /// assert_eq!(non_empty.binary_search(&4),   Err(7));
    /// assert_eq!(non_empty.binary_search(&100), Err(13));
    /// let r = non_empty.binary_search(&1);
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    ///
    /// If you want to insert an item to a sorted non-empty vector, while maintaining sort order:
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let mut non_empty = NonEmpty::from((0, vec![1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]));
    /// let num = 42;
    /// let idx = non_empty.binary_search(&num).unwrap_or_else(|x| x);
    /// non_empty.insert(idx, num);
    /// assert_eq!(non_empty, NonEmpty::from((0, vec![1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55])));
    /// ```
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|p| p.cmp(x))
    }

    /// Binary searches this sorted non-empty with a comparator function.
    ///
    /// The comparator function should implement an order consistent with the sort order of the underlying slice,
    /// returning an order code that indicates whether its argument is Less, Equal or Greater the desired target.
    ///
    /// If the value is found then Result::Ok is returned, containing the index of the matching element.
    /// If there are multiple matches, then any one of the matches could be returned.
    /// If the value is not found then Result::Err is returned, containing the index where a matching element could be
    ///	inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements. The first is found, with a uniquely determined
    /// position; the second and third are not found; the fourth could match any position in [1,4].
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::from((0, vec![1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]));
    /// let seek = 0;
    /// assert_eq!(non_empty.binary_search_by(|probe| probe.cmp(&seek)), Ok(0));
    /// let seek = 13;
    /// assert_eq!(non_empty.binary_search_by(|probe| probe.cmp(&seek)), Ok(9));
    /// let seek = 4;
    /// assert_eq!(non_empty.binary_search_by(|probe| probe.cmp(&seek)), Err(7));
    /// let seek = 100;
    /// assert_eq!(non_empty.binary_search_by(|probe| probe.cmp(&seek)), Err(13));
    /// let seek = 1;
    /// let r = non_empty.binary_search_by(|probe| probe.cmp(&seek));
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        match f(&self.0) {
            Ordering::Equal => Ok(0),
            Ordering::Greater => Err(0),
            Ordering::Less => self
                .1
                .binary_search_by(f)
                .map(|index| index + 1)
                .map_err(|index| index + 1),
        }
    }

    /// Binary searches this sorted non-empty vector with a key extraction function.
    ///
    /// Assumes that the vector is sorted by the key.
    ///
    /// If the value is found then Result::Ok is returned, containing the index of the matching element. If there are multiple matches,
    /// then any one of the matches could be returned. If the value is not found then Result::Err is returned,
    /// containing the index where a matching element could be inserted while maintaining sorted order.
    ///
    /// # Examples
    ///
    /// Looks up a series of four elements in a non-empty vector of pairs sorted by their second elements.
    /// The first is found, with a uniquely determined position; the second and third are not found;
    /// the fourth could match any position in [1, 4].
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::from((
    ///     (0, 0),
    ///     vec![(2, 1), (4, 1), (5, 1), (3, 1),
    ///          (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
    ///          (1, 21), (2, 34), (4, 55)]
    /// ));
    ///
    /// assert_eq!(non_empty.binary_search_by_key(&0, |&(a,b)| b),  Ok(0));
    /// assert_eq!(non_empty.binary_search_by_key(&13, |&(a,b)| b),  Ok(9));
    /// assert_eq!(non_empty.binary_search_by_key(&4, |&(a,b)| b),   Err(7));
    /// assert_eq!(non_empty.binary_search_by_key(&100, |&(a,b)| b), Err(13));
    /// let r = non_empty.binary_search_by_key(&1, |&(a,b)| b);
    /// assert!(match r { Ok(1..=4) => true, _ => false, });
    /// ```
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
    where
        B: Ord,
        F: FnMut(&'a T) -> B,
    {
        self.binary_search_by(|k| f(k).cmp(b))
    }

    /// Returns the maximum element in the non-empty vector.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new(42);
    /// assert_eq!(non_empty.maximum(), &42);
    ///
    /// let non_empty = NonEmpty::from((1, vec![-34, 42, 76, 4, 5]));
    /// assert_eq!(non_empty.maximum(), &76);
    /// ```
    pub fn maximum(&self) -> &T
    where
        T: Ord,
    {
        self.maximum_by(|i, j| i.cmp(j))
    }

    /// Returns the minimum element in the non-empty vector.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new(42);
    /// assert_eq!(non_empty.minimum(), &42);
    ///
    /// let non_empty = NonEmpty::from((1, vec![-34, 42, 76, 4, 5]));
    /// assert_eq!(non_empty.minimum(), &-34);
    /// ```
    pub fn minimum(&self) -> &T
    where
        T: Ord,
    {
        self.minimum_by(|i, j| i.cmp(j))
    }

    /// Returns the element that gives the maximum value with respect to the specified comparison function.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new((0, 42));
    /// assert_eq!(non_empty.maximum_by(|(k, _), (l, _)| k.cmp(l)), &(0, 42));
    ///
    /// let non_empty = NonEmpty::from(((2, 1), vec![(2, -34), (4, 42), (0, 76), (1, 4), (3, 5)]));
    /// assert_eq!(non_empty.maximum_by(|(k, _), (l, _)| k.cmp(l)), &(4, 42));
    /// ```
    pub fn maximum_by<F>(&self, compare: F) -> &T
    where
        F: Fn(&T, &T) -> Ordering,
    {
        let mut max = &self.0;
        for i in self.1.iter() {
            max = match compare(&max, &i) {
                Ordering::Equal => max,
                Ordering::Less => &i,
                Ordering::Greater => max,
            };
        }
        max
    }

    /// Returns the element that gives the minimum value with respect to the specified comparison function.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new((0, 42));
    /// assert_eq!(non_empty.minimum_by(|(k, _), (l, _)| k.cmp(l)), &(0, 42));
    ///
    /// let non_empty = NonEmpty::from(((2, 1), vec![(2, -34), (4, 42), (0, 76), (1, 4), (3, 5)]));
    /// assert_eq!(non_empty.minimum_by(|(k, _), (l, _)| k.cmp(l)), &(0, 76));
    /// ```
    pub fn minimum_by<F>(&self, compare: F) -> &T
    where
        F: Fn(&T, &T) -> Ordering,
    {
        self.maximum_by(|a, b| compare(a, b).reverse())
    }

    /// Returns the element that gives the maximum value with respect to the specified function.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new((0, 42));
    /// assert_eq!(non_empty.maximum_by_key(|(k, _)| k), &(0, 42));
    ///
    /// let non_empty = NonEmpty::from(((2, 1), vec![(2, -34), (4, 42), (0, 76), (1, 4), (3, 5)]));
    /// assert_eq!(non_empty.maximum_by_key(|(k, _)| k), &(4, 42));
    /// ```
    pub fn maximum_by_key<U, F>(&self, f: F) -> &T
    where
        U: Ord,
        F: Fn(&T) -> &U,
    {
        self.maximum_by(|i, j| f(i).cmp(f(j)))
    }

    /// Returns the element that gives the minimum value with respect to the specified function.
    ///
    /// This will return the first item in the vector if the tail is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty = NonEmpty::new((0, 42));
    /// assert_eq!(non_empty.minimum_by_key(|(k, _)| k), &(0, 42));
    ///
    /// let non_empty = NonEmpty::from(((2, 1), vec![(2, -34), (4, 42), (0, 76), (1, 4), (3, 5)]));
    /// assert_eq!(non_empty.minimum_by_key(|(k, _)| k), &(0, 76));
    /// ```
    pub fn minimum_by_key<U, F>(&self, f: F) -> &T
    where
        U: Ord,
        F: Fn(&T) -> &U,
    {
        self.minimum_by(|i, j| f(i).cmp(f(j)))
    }
}

impl<T> Into<Vec<T>> for NonEmpty<T> {
    /// Turns a non-empty list into a Vec.
    fn into(self) -> Vec<T> {
        iter::once(self.0).chain(self.1).collect()
    }
}

impl<T> From<(T, Vec<T>)> for NonEmpty<T> {
    /// Turns a pair of an element and a Vec into
    /// a NonEmpty.
    fn from((head, tail): (T, Vec<T>)) -> Self {
        NonEmpty(head, tail)
    }
}

impl<T> IntoIterator for NonEmpty<T> {
    type Item = T;
    type IntoIter = iter::Chain<iter::Once<T>, vec::IntoIter<Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        iter::once(self.0).chain(self.1)
    }
}

#[cfg(test)]
mod tests {
    use crate::NonEmpty;

    #[test]
    fn test_from_conversion() {
        let result = NonEmpty::from((1, vec![2, 3, 4, 5]));
        let expected = NonEmpty(1, vec![2, 3, 4, 5]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_into_iter() {
        let nonempty = NonEmpty::from((0, vec![1, 2, 3]));
        for (i, n) in nonempty.into_iter().enumerate() {
            assert_eq!(i as i32, n);
        }
    }
}
