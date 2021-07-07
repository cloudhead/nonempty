use std::num::NonZeroUsize;

/// A non-empty list which statically guarantees certain operations
/// cannot return zero, using [`std::num::NonZeroUsize`].
///
/// *Experimental*
///
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NonEmpty<T>(super::NonEmpty<T>);

impl<T> NonEmpty<T> {
    /// Get the length of the list.
    pub fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.0.tail.len() + 1) }
    }

    /// Get the capacity of the list.
    pub fn capacity(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.0.tail.capacity() + 1) }
    }

    /// Truncate the list to a certain size.
    pub fn truncate(&mut self, len: NonZeroUsize) {
        self.tail.truncate(usize::from(len) - 1);
    }
}

impl<T> From<super::NonEmpty<T>> for NonEmpty<T> {
    fn from(other: super::NonEmpty<T>) -> NonEmpty<T> {
        NonEmpty(other)
    }
}

impl<T> std::ops::Deref for NonEmpty<T> {
    type Target = super::NonEmpty<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> std::ops::DerefMut for NonEmpty<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::nonzero;
    use crate::NonEmpty;

    use std::convert::TryInto;

    #[test]
    fn test_nonzero() {
        let nonempty: nonzero::NonEmpty<_> = NonEmpty::from((0, vec![1, 2, 3])).into();

        assert_eq!(nonempty.len(), 4.try_into().unwrap());
        assert_eq!(nonempty.capacity(), 4.try_into().unwrap());
    }
}
