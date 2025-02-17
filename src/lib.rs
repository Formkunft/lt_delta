//! A type representing a source element, a target element, or both a source and a target element.
//!
//! This type represents an inclusive OR relation:
//! Either a source element is available, or a target element is available, or both are available.
//! `Delta` behaves similar to `Option`, but instead of representing 0 or 1 elements, it represents 1 or 2 elements.
//!
//! The source and target are described as the two sides of a delta.
//! Both sides are accessible via optional `source` and `target` methods.
//! Convenient methods like `resolve` and `merge` also provide access to the elements.
//!
//! Transform a `Delta` value to a different `Delta` value using `map`, `map_any`, or `map_all`.

/// The `Delta` type. See the module level documentation for more.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Delta<T> {
    /// A source element.
    ///
    /// Conceptually, this case represents a value where the element was deleted and thus no target element is available.
    Source(T),
    /// A target element.
    ///
    /// Conceptually, this case represents a value where the element was added and thus no source element is available.
    Target(T),
    /// The combination of a source element and a target element.
    ///
    /// Conceptually, this case represents a value where an element was modified or kept the same and thus both a source and a target element are available.
    Transition(T, T),
}

impl<T> Delta<T> {
    /// Creates a transition delta.
    pub fn new(source: T, target: T) -> Self {
        Self::Transition(source, target)
    }

    /// Creates a target delta if `source` is `None`; otherwise, creates a transition delta.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert!(matches!(Delta::from_option_source(None, 5), Delta::Target(5)));
    /// assert!(matches!(Delta::from_option_source(Some(3), 5), Delta::Transition(3, 5)));
    /// ```
    pub fn from_option_source(source: Option<T>, target: T) -> Self {
        match source {
            Some(source) => Self::Transition(source, target),
            None => Self::Target(target),
        }
    }

    /// Creates a source delta if `target` is `None`; otherwise, creates a transition delta.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert!(matches!(Delta::from_option_target(3, None), Delta::Source(3)));
    /// assert!(matches!(Delta::from_option_target(3, Some(5)), Delta::Transition(3, 5)));
    /// ```
    pub fn from_option_target(source: T, target: Option<T>) -> Self {
        match target {
            Some(target) => Self::Transition(source, target),
            None => Self::Source(source),
        }
    }

    /// Creates a delta when one or both elements are non-`None`; otherwise, returns `None`.
    ///
    /// - If both the source and target are non-`None`, creates a transition delta.
    /// - Else, if the source is non-`None`, creates a source delta.
    /// - Else, if the target is non-`None`, creates a target delta.
    /// - Otherwise, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert!(matches!(Delta::<i32>::from_options(None, None), None));
    /// assert!(matches!(Delta::from_options(Some(3), None), Some(Delta::Source(3))));
    /// assert!(matches!(Delta::from_options(None, Some(5)), Some(Delta::Target(5))));
    /// assert!(matches!(Delta::from_options(Some(3), Some(5)), Some(Delta::Transition(3, 5))));
    /// ```
    pub fn from_options(source: Option<T>, target: Option<T>) -> Option<Self> {
        match (source, target) {
            (Some(source), Some(target)) => Some(Self::Transition(source, target)),
            (Some(source), None) => Some(Self::Source(source)),
            (None, Some(target)) => Some(Self::Target(target)),
            (None, None) => None,
        }
    }

    /// The source element, if available; otherwise, `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(5);
    /// assert_eq!(delta.source(), Some(&5));
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.source(), None);
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(delta.source(), Some(&3));
    /// ```
    pub fn source(&self) -> Option<&T> {
        match self {
            Delta::Source(source) => Some(source),
            Delta::Target(_) => None,
            Delta::Transition(source, _) => Some(source),
        }
    }

    /// The target element, if available; otherwise, `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(5);
    /// assert_eq!(delta.target(), None);
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.target(), Some(&5));
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(delta.target(), Some(&5));
    /// ```
    pub fn target(&self) -> Option<&T> {
        match self {
            Delta::Source(_) => None,
            Delta::Target(target) => Some(target),
            Delta::Transition(_, target) => Some(target),
        }
    }

    /// Returns a delta containing the results of mapping the given closure over the delta’s elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(3);
    /// assert_eq!(delta.map(|x| x + 20), Delta::Source(23));
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.map(|x| x + 20), Delta::Target(25));
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(delta.map(|x| x + 20), Delta::Transition(23, 25));
    /// ```
    pub fn map<U, F: FnMut(T) -> U>(self, mut transform: F) -> Delta<U> {
        match self {
            Delta::Source(source) => Delta::Source(transform(source)),
            Delta::Target(target) => Delta::Target(transform(target)),
            Delta::Transition(source, target) => {
                Delta::Transition(transform(source), transform(target))
            }
        }
    }

    /// Returns a delta containing the results of mapping the given closure over the delta’s elements, or `None`, if the closure returns `None` for all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(3);
    /// assert_eq!(delta.map_any(|x| Some(x + 20)), Some(Delta::Source(23)));
    /// assert_eq!(delta.map_any(|_| None::<i32>), None);
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.map_any(|x| Some(x + 20)), Some(Delta::Target(25)));
    /// assert_eq!(delta.map_any(|_| None::<i32>), None);
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(
    ///     delta.map_any(|x| if x >= 2 { Some(x + 20) } else { None }),
    ///     Some(Delta::Transition(23, 25))
    /// );
    /// assert_eq!(
    ///     delta.map_any(|x| if x <= 4 { Some(x + 20) } else { None }),
    ///     Some(Delta::Source(23))
    /// );
    /// assert_eq!(
    ///     delta.map_any(|x| if x >= 4 { Some(x + 20) } else { None }),
    ///     Some(Delta::Target(25))
    /// );
    /// assert_eq!(
    ///     delta.map_any(|x| if x >= 6 { Some(x + 20) } else { None }),
    ///     None
    /// );
    /// ```
    pub fn map_any<U, F: FnMut(T) -> Option<U>>(self, mut transform: F) -> Option<Delta<U>> {
        match self {
            Delta::Source(source) => transform(source).map(Delta::Source),
            Delta::Target(target) => transform(target).map(Delta::Target),
            Delta::Transition(source, target) => {
                let source = transform(source);
                let target = transform(target);
                if let Some(source) = source {
                    if let Some(target) = target {
                        Some(Delta::Transition(source, target))
                    } else {
                        Some(Delta::Source(source))
                    }
                } else {
                    target.map(Delta::Target)
                }
            }
        }
    }

    /// Returns a delta containing the results of mapping the given closure over the delta’s elements, or `None`, if the closure returns `None` for any element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(3);
    /// assert_eq!(delta.map_all(|x| Some(x + 20)), Some(Delta::Source(23)));
    /// assert_eq!(delta.map_all(|_| None::<i32>), None);
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.map_all(|x| Some(x + 20)), Some(Delta::Target(25)));
    /// assert_eq!(delta.map_all(|_| None::<i32>), None);
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(delta.map_all(|x| if x >= 2 { Some(x + 20) } else { None }), Some(Delta::Transition(23, 25)));
    /// assert_eq!(delta.map_all(|x| if x <= 4 { Some(x + 20) } else { None }), None);
    /// assert_eq!(delta.map_all(|x| if x >= 4 { Some(x + 20) } else { None }), None);
    /// assert_eq!(delta.map_all(|x| if x >= 6 { Some(x + 20) } else { None }), None);
    pub fn map_all<U, F: FnMut(T) -> Option<U>>(self, mut transform: F) -> Option<Delta<U>> {
        match self {
            Delta::Source(source) => transform(source).map(Delta::Source),
            Delta::Target(target) => transform(target).map(Delta::Target),
            Delta::Transition(source, target) => {
                let source = transform(source);
                let target = transform(target);
                if let Some(source) = source {
                    target.map(|target| Delta::Transition(source, target))
                } else {
                    None
                }
            }
        }
    }

    /// Resolves the delta to a single element, favoring the element on the given side.
    ///
    /// If the favored element is not available, the other element is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::{Delta, Side};
    /// let delta = Delta::Source(3);
    /// assert_eq!(delta.resolve(Side::Source), 3);
    /// assert_eq!(delta.resolve(Side::Target), 3);
    ///
    /// let delta = Delta::Target(5);
    /// assert_eq!(delta.resolve(Side::Source), 5);
    /// assert_eq!(delta.resolve(Side::Target), 5);
    ///
    /// let delta = Delta::Transition(3, 5);
    /// assert_eq!(delta.resolve(Side::Source), 3);
    /// assert_eq!(delta.resolve(Side::Target), 5);
    /// ```
    pub fn resolve(self, side: Side) -> T {
        match side {
            Side::Source => match self {
                Delta::Source(source) => source,
                Delta::Target(target) => target,
                Delta::Transition(source, _) => source,
            },
            Side::Target => match self {
                Delta::Source(source) => source,
                Delta::Target(target) => target,
                Delta::Transition(_, target) => target,
            },
        }
    }

    /// Resolves the delta to a single element, favoring the source element.
    ///
    /// Returns the source element, if available; otherwise, returns the target element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert_eq!(Delta::Source(3).first(), 3);
    /// assert_eq!(Delta::Target(5).first(), 5);
    /// assert_eq!(Delta::Transition(3, 5).first(), 3);
    /// ```
    pub fn first(self) -> T {
        self.resolve(Side::Source)
    }

    /// Resolves the delta to a single element, favoring the target element.
    ///
    /// Returns the target element, if available; otherwise, returns the source element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert_eq!(Delta::Source(3).last(), 3);
    /// assert_eq!(Delta::Target(5).last(), 5);
    /// assert_eq!(Delta::Transition(3, 5).last(), 5);
    /// ```
    pub fn last(self) -> T {
        self.resolve(Side::Target)
    }

    /// Resolves the delta to a single element, coalescing the source and target elements in the transition case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert_eq!(Delta::Source(3).merge(|s, t| s + t), 3);
    /// assert_eq!(Delta::Target(5).merge(|s, t| s + t), 5);
    /// assert_eq!(Delta::Transition(3, 5).merge(|s, t| s + t), 8);
    /// ```
    pub fn merge<F: FnOnce(T, T) -> T>(self, coalesce: F) -> T {
        match self {
            Delta::Source(source) => source,
            Delta::Target(target) => target,
            Delta::Transition(source, target) => coalesce(source, target),
        }
    }

    /// Returns a transition delta where both the source and target share the same element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::identity(5);
    /// ```
    pub fn identity(element: T) -> Self
    where
        T: Copy,
    {
        Delta::Transition(element, element)
    }

    /// Returns whether the delta is of the transition case and a predicate is true given the source and target elements.
    ///
    /// A source delta or target delta always returns `false` without invoking `predicate`.
    ///
    /// - Parameter predicate: The return value of this function is returned by `isIdentity(by:)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::identity(5);
    /// assert!(delta.is_identity_by(|s, t| s == t));
    ///
    /// let delta = Delta::Transition(-5, 5);
    /// assert!(delta.is_identity_by(|s, t| i32::abs(*s) == i32::abs(*t)));
    ///
    /// let delta = Delta::Source(5);
    /// assert!(!delta.is_identity_by(|s, t| s == t));
    /// ```
    pub fn is_identity_by<F: FnOnce(&T, &T) -> bool>(self, predicate: F) -> bool {
        match self {
            Delta::Source(_) => false,
            Delta::Target(_) => false,
            Delta::Transition(source, target) => predicate(&source, &target),
        }
    }

    /// Returns whether the delta is of the transition case and the source and target elements are equal.
    ///
    /// A source delta or target delta always returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// assert!(!Delta::Source(3).is_identity());
    /// assert!(!Delta::Target(5).is_identity());
    /// assert!(Delta::identity(5).is_identity());
    /// assert!(Delta::Transition(5, 5).is_identity());
    /// assert!(!Delta::Transition(3, 5).is_identity());
    pub fn is_identity(self) -> bool
    where
        T: PartialEq,
    {
        self.is_identity_by(|s, t| s == t)
    }

    /// Converts from `&Delta<T>` to `Delta<&T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let text: Delta<String> = Delta::Source("Hello!".to_string());
    /// let text_length: Delta<usize> = text.as_ref().map(|s| s.len());
    /// println!("still can print text: {text:?}");
    /// ```
    pub const fn as_ref(&self) -> Delta<&T> {
        match *self {
            Delta::Source(ref source) => Delta::Source(source),
            Delta::Target(ref target) => Delta::Target(target),
            Delta::Transition(ref source, ref target) => Delta::Transition(source, target),
        }
    }

    /// Converts from `&mut Delta<T>` to `Delta<&mut T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let mut x = Delta::Source(3);
    /// match x.as_mut() {
    ///     Delta::Source(v) => *v = 23,
    ///    _ => {},
    /// }
    /// assert_eq!(x, Delta::Source(23));
    /// ```
    pub const fn as_mut(&mut self) -> Delta<&mut T> {
        match *self {
            Delta::Source(ref mut source) => Delta::Source(source),
            Delta::Target(ref mut target) => Delta::Target(target),
            Delta::Transition(ref mut source, ref mut target) => Delta::Transition(source, target),
        }
    }

    /// Converts from `Delta<T>` (or `&Delta<T>`) to `Delta<&T::Target>`.
    ///
    /// Leaves the original delta in place, creating a new one with a reference to the original one, additionally coercing the contents via `Deref`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let x = Delta::Source("hey".to_owned());
    /// assert_eq!(x.as_deref(), Delta::Source("hey"));
    /// ```
    pub fn as_deref(&self) -> Delta<&T::Target>
    where
        T: std::ops::Deref,
    {
        self.as_ref().map(|x| x.deref())
    }

    /// Converts from `Delta<T>` (or `&mut Delta<T>`) to `Delta<&mut T::Target>`.
    ///
    /// Leaves the original delta in place, creating a new one containing a mutable reference to the inner type’s `Deref::Target` type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let mut x = Delta::Source("hey".to_owned());
    /// assert_eq!(x.as_deref_mut().map(|x| {
    ///     x.make_ascii_uppercase();
    ///     x
    /// }), Delta::Source("HEY".to_owned().as_mut_str()));
    /// ```
    pub fn as_deref_mut(&mut self) -> Delta<&mut T::Target>
    where
        T: std::ops::DerefMut,
    {
        self.as_mut().map(|x| x.deref_mut())
    }
}

impl<T> Delta<&mut T> {
    /// Maps a `Delta<&mut T>` to a `Delta<T>` by copying the contents of the delta.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let mut x = 5;
    /// let delta_x = Delta::Target(&mut x);
    /// assert_eq!(delta_x, Delta::Target(&mut 5));
    /// let copied = delta_x.copied();
    /// assert_eq!(copied, Delta::Target(5));
    /// ```
    pub const fn copied(self) -> Delta<T>
    where
        T: Copy,
    {
        match self {
            Delta::Source(&mut source) => Delta::Source(source),
            Delta::Target(&mut target) => Delta::Target(target),
            Delta::Transition(&mut source, &mut target) => Delta::Transition(source, target),
        }
    }

    /// Maps a `Delta<&mut T>` to a `Delta<T>` by cloning the contents of the delta.
    ///
    /// # Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let mut x = 5;
    /// let delta_x = Delta::Target(&mut x);
    /// assert_eq!(delta_x, Delta::Target(&mut 5));
    /// let cloned = delta_x.cloned();
    /// assert_eq!(cloned, Delta::Target(5));
    /// ```
    pub fn cloned(self) -> Delta<T>
    where
        T: Clone,
    {
        match self {
            Delta::Source(source) => Delta::Source(source.clone()),
            Delta::Target(target) => Delta::Target(target.clone()),
            Delta::Transition(source, target) => Delta::Transition(source.clone(), target.clone()),
        }
    }
}

/// A description of the two sides of a delta.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    /// The source side of a delta.
    ///
    /// This side is perferred when accessing the first element of a delta.
    Source,
    /// The target side of a delta.
    ///
    /// This side is perferred when accessing the last element of a delta.
    Target,
}
