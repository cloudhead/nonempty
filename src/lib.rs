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

    /// Get the possibly-empty tail of the list.
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
    /// ```
    pub fn insert(&mut self, index: usize, element: T)
    where
        T: Clone,
    {
        let len = self.len();
        assert!(index <= len);

        if index == 0 {
            let head = self.0.clone();
            let tail = &mut self.1;
            tail.insert(0, head);
            self.0 = element;
            self.1 = tail.clone();
        } else {
            let tail = &mut self.1;
            tail.insert(index - 1, element);
            self.1 = tail.clone();
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
        std::iter::once(&self.0).chain(self.1.iter())
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
        std::iter::once(&mut self.0).chain(self.1.iter_mut())
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
}

impl<T> Into<Vec<T>> for NonEmpty<T> {
    /// Turns a non-empty list into a Vec.
    fn into(self) -> Vec<T> {
        std::iter::once(self.0).chain(self.1).collect()
    }
}

impl<T> From<(T, Vec<T>)> for NonEmpty<T> {
    /// Turns a pair of an element and a Vec into
    /// a NonEmpty.
    fn from((head, tail): (T, Vec<T>)) -> Self {
        NonEmpty(head, tail)
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
}
