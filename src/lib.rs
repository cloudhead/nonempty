//! A Non-empty growable vector.
//!
//! # Examples
//!
//! ```
//! use nonempty::NonEmpty;
//!
//! let mut l = NonEmpty::new(42);
//!
//! assert_eq!(l.first(), &42);
//!
//! l.push(36);
//! l.push(58);
//!
//! let v: Vec<i32> = l.into();
//! assert_eq!(v, vec![42, 36, 58]);
//! ```
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
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

    /// Push an element to the end of the list.
    pub fn push(&mut self, e: T) {
        self.1.push(e)
    }

    /// Pop an element from the end of the list.
    pub fn pop(&mut self) -> Option<T> {
        self.1.pop()
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
    /// let mut l = NonEmpty::new(42);
    /// l.push(36);
    /// l.push(58);
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
}

impl<T> Into<Vec<T>> for NonEmpty<T> {
    /// Turns a non-empty list into a Vec.
    fn into(self) -> Vec<T> {
        std::iter::once(self.0).chain(self.1).collect()
    }
}
