/// A type representing a source element, a target element, or both a source and a target element.
///
/// This type represents an inclusive OR relation:
/// Either a source element is available, or a target element is available, or both are available.
/// `Delta` behaves similar to `Option`, but instead of representing 0 or 1 elements, it represents 1 or 2 elements.
///
/// The source and target are described as the two sides of a delta.
/// Both sides are accessible via optional `source` and `target` methods.
/// Convenient methods like `resolve` and `merge` also provide access to the elements.
///
/// Transform a `Delta` value to a different `Delta` value using `map`, `map_any`, or `map_all`.
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
    /// ### Examples
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
    /// ### Examples
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
    /// ### Examples
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
}

impl<T> Delta<T> {
    /// The source element, if available; otherwise, `None`.
    ///
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let d1 = Delta::Source(5);
    /// assert_eq!(d1.source(), Some(&5));
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.source(), None);
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(d3.source(), Some(&3));
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
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let d1 = Delta::Source(5);
    /// assert_eq!(d1.target(), None);
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.target(), Some(&5));
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(d3.target(), Some(&5));
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
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let d1 = Delta::Source(3);
    /// assert_eq!(d1.map(|x| x + 20), Delta::Source(23));
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.map(|x| x + 20), Delta::Target(25));
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(d3.map(|x| x + 20), Delta::Transition(23, 25));
    /// ```
    pub fn map<R, F: FnMut(T) -> R>(self, mut transform: F) -> Delta<R> {
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
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let d1 = Delta::Source(3);
    /// assert_eq!(d1.map_any(|x| Some(x + 20)), Some(Delta::Source(23)));
    /// assert_eq!(d1.map_any(|_| None::<i32>), None);
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.map_any(|x| Some(x + 20)), Some(Delta::Target(25)));
    /// assert_eq!(d2.map_any(|_| None::<i32>), None);
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(
    ///     d3.map_any(|x| if x >= 2 { Some(x + 20) } else { None }),
    ///     Some(Delta::Transition(23, 25))
    /// );
    /// assert_eq!(
    ///     d3.map_any(|x| if x <= 4 { Some(x + 20) } else { None }),
    ///     Some(Delta::Source(23))
    /// );
    /// assert_eq!(
    ///     d3.map_any(|x| if x >= 4 { Some(x + 20) } else { None }),
    ///     Some(Delta::Target(25))
    /// );
    /// assert_eq!(
    ///     d3.map_any(|x| if x >= 6 { Some(x + 20) } else { None }),
    ///     None
    /// );
    /// ```
    pub fn map_any<R, F: FnMut(T) -> Option<R>>(self, mut transform: F) -> Option<Delta<R>> {
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
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let d1 = Delta::Source(3);
    /// assert_eq!(d1.map_all(|x| Some(x + 20)), Some(Delta::Source(23)));
    /// assert_eq!(d1.map_all(|_| None::<i32>), None);
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.map_all(|x| Some(x + 20)), Some(Delta::Target(25)));
    /// assert_eq!(d2.map_all(|_| None::<i32>), None);
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(d3.map_all(|x| if x >= 2 { Some(x + 20) } else { None }), Some(Delta::Transition(23, 25)));
    /// assert_eq!(d3.map_all(|x| if x <= 4 { Some(x + 20) } else { None }), None);
    /// assert_eq!(d3.map_all(|x| if x >= 4 { Some(x + 20) } else { None }), None);
    /// assert_eq!(d3.map_all(|x| if x >= 6 { Some(x + 20) } else { None }), None);
    pub fn map_all<R, F: FnMut(T) -> Option<R>>(self, mut transform: F) -> Option<Delta<R>> {
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
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::{Delta, Side};
    /// let d1 = Delta::Source(3);
    /// assert_eq!(d1.resolve(Side::Source), 3);
    /// assert_eq!(d1.resolve(Side::Target), 3);
    ///
    /// let d2 = Delta::Target(5);
    /// assert_eq!(d2.resolve(Side::Source), 5);
    /// assert_eq!(d2.resolve(Side::Target), 5);
    ///
    /// let d3 = Delta::Transition(3, 5);
    /// assert_eq!(d3.resolve(Side::Source), 3);
    /// assert_eq!(d3.resolve(Side::Target), 5);
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
    /// ### Examples
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
    /// ### Examples
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

    /// Returns whether the delta is of the transition case and a predicate is true given the source and target elements.
    ///
    /// A source delta or target delta always returns `false` without invoking `predicate`.
    ///
    /// - Parameter predicate: The return value of this function is returned by `isIdentity(by:)`.
    ///
    /// ### Examples
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::identity(5);
    /// assert!(delta.is_identity(|s, t| s == t));
    /// ```
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Transition(-5, 5);
    /// assert!(delta.is_identity(|s, t| i32::abs(*s) == i32::abs(*t)));
    /// ```
    ///
    /// ```
    /// # use lt_delta::Delta;
    /// let delta = Delta::Source(5);
    /// assert!(!delta.is_identity(|s, t| s == t));
    /// ```
    pub fn is_identity<F: FnOnce(&T, &T) -> bool>(self, predicate: F) -> bool {
        match self {
            Delta::Source(_) => false,
            Delta::Target(_) => false,
            Delta::Transition(source, target) => predicate(&source, &target),
        }
    }
}

impl<T: Copy> Delta<T> {
    /// Returns a transition delta where both the source and target share the same element.
    pub fn identity(element: T) -> Self {
        Delta::Transition(element, element)
    }
}

pub enum Side {
    Source,
    Target,
}
