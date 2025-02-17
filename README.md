# `Delta<T>`

A type representing a source element, a target element, or both a source and a target element.

This type represents an inclusive OR relation:
Either a source element is available, or a target element is available, or both are available.
`Delta` behaves similar to `Option`, but instead of representing 0 or 1 elements, it represents 1 or 2 elements.

## Implementation

The source and target are described as the two sides of a delta.
Both sides are accessible via optional `source` and `target` methods.
Convenient methods like `resolve` and `merge` also provide access to the elements.

Transform a `Delta` value to a different `Delta` value using `map`, `map_any`, or `map_all`.
