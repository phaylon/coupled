use crate::{Vs, Iter};


/// An unordered pair of values
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p1 = Pair::new(23, 42);
/// let p2 = Pair::new(42, 23);
///
/// assert_eq!(p1, p2);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(transparent),
)]
pub struct Pair<T> {
    items: [T; 2],
}

impl<T> std::fmt::Debug for Pair<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(&self.items).finish()
    }
}

impl<T> Pair<T> {
    /// Construct a pair of values.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p1 = Pair::new(23, 42);
    /// let p2 = Pair::new(42, 23);
    ///
    /// assert_eq!(p1, p2);
    /// ```
    pub fn new(a: T, b: T) -> Self
    where
        T: Ord,
    {
        if a < b {
            Self { items: [a, b] }
        } else {
            Self { items: [b, a] }
        }
    }

    /// Construct a pair with two identical values.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    ///
    /// let p1 = Pair::with_cloned(23);
    /// let p2 = Pair::new(23, 23);
    ///
    /// assert_eq!(p1, p2);
    /// ```
    pub fn with_cloned(item: T) -> Self
    where
        T: Ord + Clone,
    {
        let b = item.clone();
        let a = item;
        Self::new(a, b)
    }

    /// Returns `true` if the given values are the ones in the pair.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    ///
    /// assert!(p.has_values(&23, &42));
    /// assert!(p.has_values(&42, &23));
    /// assert!(! p.has_values(&23, &5));
    /// ```
    pub fn has_values(&self, a: &T, b: &T) -> bool
    where
        T: Ord,
    {
        if a < b {
            self.items[0] == *a && self.items[1] == *b
        } else {
            self.items[0] == *b && self.items[1] == *a
        }
    }

    /// The first item of the pair.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// assert_eq!(p.first(), &23);
    /// ```
    pub fn first(&self) -> &T {
        &self.items[0]
    }

    /// The second item of the pair.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// assert_eq!(p.second(), &42);
    /// ```
    pub fn second(&self) -> &T {
        &self.items[1]
    }

    /// Returns `true` if the given value is contained in the pair.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    ///
    /// assert!(p.contains(&23));
    /// assert!(! p.contains(&5));
    /// ```
    pub fn contains(&self, item: &T) -> bool
    where
        T: Eq,
    {
        self.items.contains(item)
    }

    /// Return the other value if the given one is contained in the pair.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    ///
    /// assert_eq!(p.other(&23), Some(&42));
    /// assert_eq!(p.other(&5), None);
    /// ```
    pub fn other(&self, item: &T) -> Option<&T>
    where
        T: Eq,
    {
        if self.items[0] == *item {
            Some(&self.items[1])
        } else if self.items[1] == *item {
            Some(&self.items[0])
        } else {
            None
        }
    }

    /// Converts from `&Pair<T>` to `Pair<&T>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let strs = Pair::new(String::from("23"), String::from("543"));
    /// let lens = strs.as_ref().map(|s| s.len());
    ///
    /// assert_eq!(lens, Pair::new(2, 3));
    /// ```
    pub fn as_ref(&self) -> Pair<&T> {
        Pair {
            items: [&self.items[0], &self.items[1]],
        }
    }

    /// Converts from `&Pair<T>` to `&[T]`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let strs = Pair::new("23", "42");
    /// let joined = strs.as_slice().join("/");
    ///
    /// assert_eq!(joined, "23/42");
    /// ```
    pub fn as_slice(&self) -> &[T] {
        &self.items
    }

    /// Converts from `&Pair<T>` to `&[T; 2]`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// let [a, b] = p.as_array();
    ///
    /// assert_eq!(a, &23);
    /// assert_eq!(b, &42);
    /// ```
    pub fn as_array(&self) -> &[T; 2] {
        &self.items
    }

    /// Converts from `Pair<T>` to `[T; 2]`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// let [a, b] = p.into_array();
    ///
    /// assert_eq!(a, 23);
    /// assert_eq!(b, 42);
    /// ```
    pub fn into_array(self) -> [T; 2] {
        self.items
    }

    /// Converts from `Pair<T>` to `(T, T)`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// let (a, b) = p.into_tuple();
    ///
    /// assert_eq!(a, 23);
    /// assert_eq!(b, 42);
    /// ```
    pub fn into_tuple(self) -> (T, T) {
        let [a, b] = self.items;
        (a, b)
    }

    /// Map the pair into another pair of values.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// let p2 = p.map(|v| v * 2);
    ///
    /// assert_eq!(p2, Pair::new(46, 84));
    /// ```
    pub fn map<U, F>(self, mut map_item: F) -> Pair<U>
    where
        F: FnMut(T) -> U,
        U: Ord,
    {
        let [a, b] = self.items;
        Pair::new(map_item(a), map_item(b))
    }

    /// Map to another set of values, with consideration of the other present value.
    ///
    /// The closure will receive the opposing value as second argument.
    ///
    /// Since values must be referenced multiple times, this is a by-reference operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let strs = Pair::new(23, 42);
    /// let subtracted = strs.map_to_with_other(|a, b| a - b);
    ///
    /// assert_eq!(subtracted, Pair::new(-19, 19));
    /// ```
    pub fn map_to_with_other<'a, U, F>(&'a self, mut map_item: F) -> Pair<U>
    where
        F: FnMut(&'a T, &'a T) -> U,
        U: Ord,
    {
        let [a, b] = &self.items;
        Pair::new(map_item(&a, &b), map_item(&b, &a))
    }

    /// An iterator over references to the contained values.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// assert_eq!(p.iter().sum::<i32>(), 65);
    /// ```
    pub fn iter(&self) -> Iter<&T> {
        Iter::new(&self.items[0], &self.items[1])
    }

    /// An iterator over tuples with referencs to the contained values paired with their opposites.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(23, 42);
    /// let paired = p.iter_with_other().collect::<Vec<_>>();
    /// assert_eq!(paired, Vec::from([(&23, &42), (&42, &23)]));
    /// ```
    pub fn iter_with_other(&self) -> Iter<(&T, &T)> {
        let [a, b] = &self.items;
        Iter::new((a, b), (b, a))
    }
}

impl<T> Pair<&T>
where
    T: Ord,
{
    /// Map `Pair<&T>` to `Pair<T>` via cloning.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let v1 = vec![2, 3];
    /// let v2 = vec![4, 2];
    /// let p = Pair::new(&v1, &v2);
    /// let sums = p.cloned().map(|v| v.into_iter().sum::<i32>());
    ///
    /// assert_eq!(sums, Pair::new(5, 6));
    /// ```
    pub fn cloned(self) -> Pair<T>
    where
        T: Clone,
    {
        let [a, b] = self.items;
        Pair::new(a.clone(), b.clone())
    }

    /// Map `Pair<&T>` to `Pair<T>` via copying.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let p = Pair::new(&23, &42);
    /// let sum = p.copied().into_iter().sum::<i32>();
    ///
    /// assert_eq!(sum, 65);
    /// ```
    pub fn copied(self) -> Pair<T>
    where
        T: Copy,
    {
        let [a, b] = self.items;
        Pair::new(*a, *b)
    }
}

impl<T> Pair<&mut T>
where
    T: Ord,
{
    /// Map `Pair<&mut T>` to `Pair<T>` via cloning.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let mut v1 = vec![2, 3];
    /// let mut v2 = vec![4, 2];
    /// let p = Pair::new(&mut v1, &mut v2);
    /// let sums = p.cloned().map(|v| v.into_iter().sum::<i32>());
    ///
    /// assert_eq!(sums, Pair::new(5, 6));
    /// ```
    pub fn cloned(self) -> Pair<T>
    where
        T: Clone,
    {
        let [a, b] = self.items;
        Pair::new(a.clone(), b.clone())
    }

    /// Map `Pair<&mut T>` to `Pair<T>` via copying.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Pair;
    /// let mut a = 23;
    /// let mut b = 42;
    /// let p = Pair::new(&mut a, &mut b);
    /// let sum = p.copied().into_iter().sum::<i32>();
    ///
    /// assert_eq!(sum, 65);
    /// ```
    pub fn copied(self) -> Pair<T>
    where
        T: Copy,
    {
        let [a, b] = self.items;
        Pair::new(*a, *b)
    }
}

/// Tuple equality.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p = Pair::new(23, 42);
///
/// assert_eq!(p, (23, 42));
/// assert_eq!(p, (42, 23));
///
/// assert_ne!(p, (23, 23));
/// assert_ne!(p, (42, 42));
/// assert_ne!(p, (22, 44));
/// ```
impl<T> PartialEq<(T, T)> for Pair<T>
where
    T: Ord,
{
    fn eq(&self, other: &(T, T)) -> bool {
        self.has_values(&other.0, &other.1)
    }
}

/// Slice equality.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p = Pair::new(23, 42);
///
/// assert_eq!(&p, &[23, 42][..]);
/// assert_eq!(&p, &[42, 23][..]);
///
/// assert_ne!(&p, &[23, 65][..]);
/// ```
impl<T> PartialEq<[T]> for Pair<T>
where
    T: Ord,
{
    fn eq(&self, other: &[T]) -> bool {
        other.len() == 2 && self.has_values(&other[0], &other[1])
    }
}

/// Array equality.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p = Pair::new(23, 42);
///
/// assert_eq!(&p, &[23, 42]);
/// assert_eq!(&p, &[42, 23]);
///
/// assert_ne!(&p, &[23, 65]);
/// ```
impl<T> PartialEq<[T; 2]> for Pair<T>
where
    T: Ord,
{
    fn eq(&self, other: &[T; 2]) -> bool {
        self.has_values(&other[0], &other[1])
    }
}

/// An iterator over the contained values.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p = Pair::new(23, 42);
/// let sum = p.into_iter().sum::<i32>();
///
/// assert_eq!(sum, 65);
/// ```
impl<T> IntoIterator for Pair<T> {
    type Item = T;
    type IntoIter = Iter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let [a, b] = self.items;
        Iter::new(a, b)
    }
}

/// An iterator over references to the contained values.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let ref p = Pair::new(23, 42);
/// let sum = p.into_iter().copied().sum::<i32>();
///
/// assert_eq!(sum, 65);
/// ```
impl<'a, T> IntoIterator for &'a Pair<T> {
    type Item = &'a T;
    type IntoIter = Iter<&'a T>;

    fn into_iter(self) -> Self::IntoIter {
        let [a, b] = &self.items;
        Iter::new(a, b)
    }
}

/// Construct from a two-item tuple.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p1 = Pair::from((23, 42));
/// let p2 = Pair::new(23, 42);
///
/// assert_eq!(p1, p2);
/// ```
impl<T> From<(T, T)> for Pair<T>
where
    T: Ord,
{
    fn from((a, b): (T, T)) -> Self {
        Pair::new(a, b)
    }
}

/// Construct from a two-value array.
///
/// # Example
///
/// ```rust
/// # use coupled::Pair;
/// let p1 = Pair::from([23, 42]);
/// let p2 = Pair::new(23, 42);
///
/// assert_eq!(p1, p2);
/// ```
impl<T> From<[T; 2]> for Pair<T>
where
    T: Ord,
{
    fn from([a, b]: [T; 2]) -> Self {
        Pair::new(a, b)
    }
}

/// Construct from [`Vs`].
///
/// # Example
///
/// ```rust
/// # use coupled::{Vs, Pair};
/// let v = Vs::new(23, 42);
///
/// let p = Pair::from(v);
/// assert_eq!(p, (23, 42));
/// assert_eq!(p, (42, 23));
/// ```
impl<T> From<Vs<T>> for Pair<T>
where
    T: Ord,
{
    fn from(vs: Vs<T>) -> Self {
        Pair::new(vs.selected, vs.other)
    }
}