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
#[derive(Clone, Debug)]
pub struct NonEmpty<T>(T, Vec<T>);

impl<T> NonEmpty<T> {
    pub const fn new(e: T) -> Self {
        Self::singleton(e)
    }

    pub const fn singleton(e: T) -> Self {
        NonEmpty(e, Vec::new())
    }

    pub const fn is_empty(&self) -> bool {
        false
    }

    pub const fn first(&self) -> &T {
        &self.0
    }

    pub fn push(&mut self, e: T) {
        self.1.push(e)
    }

    pub fn pop(&mut self) -> Option<T> {
        self.1.pop()
    }

    pub fn len(&self) -> usize {
        self.1.len() + 1
    }

    pub fn last(&self) -> &T {
        match self.1.last() {
            None => &self.0,
            Some(e) => e,
        }
    }

    pub fn last_mut(&mut self) -> &mut T {
        match self.1.last_mut() {
            None => &mut self.0,
            Some(e) => e,
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index == 0 {
            Some(&self.0)
        } else {
            self.1.get(index - 1)
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index == 0 {
            Some(&mut self.0)
        } else {
            self.1.get_mut(index - 1)
        }
    }

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

    /// Often we have a `Vec` but want to ensure that it is `NonEmpty` before
    /// proceeding with a computation. Using `from_vec` will give us a proof
    /// that we have a `NonEmpty` in the `Some` branch, otherwise it allows
    /// the caller to handle the `None` case.
    ///
    /// # Example Use
    ///
    /// ```
    /// use nonempty::NonEmpty;
    ///
    /// let non_empty_vec = NonEmpty::from_vec(vec!([1, 2, 3, 4, 5]));
    /// assert!(non_empty_vec.is_some());
    ///
    /// let empty_vec: Option<NonEmpty<u32>> = NonEmpty::from_vec(Vec::new());
    /// assert!(empty_vec.is_none());
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Option<NonEmpty<T>> {
        let mut vec = vec;
        let head = vec.pop();
        match head {
            Some(t) => {
                let mut result = NonEmpty::new(t);
                for u in vec {
                    result.push(u)
                }
                Some(result)
            }
            None => None,
        }
    }
}

impl<T> Into<Vec<T>> for NonEmpty<T> {
    /// Turns a non-empty list into a Vec.
    fn into(self) -> Vec<T> {
        std::iter::once(self.0).chain(self.1).collect()
    }
}
