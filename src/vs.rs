use crate::{Pair, Iter};


/// Two values with one being primarily selected.
///
/// The fields are public, as there are no invariants to uphold.
///
/// # Example
///
/// ```rust
/// # use coupled::Vs;
/// let mut v = Vs::new(23, 42);
///
/// assert_eq!(v.selected, 23);
/// assert_eq!(v.other, 42);
///
/// v.flip();
///
/// assert_eq!(v.selected, 42);
/// assert_eq!(v.other, 23);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
    serde(deny_unknown_fields),
)]
pub struct Vs<T> {
    /// The primarily selected value.
    pub selected: T,
    /// The not selected value.
    pub other: T,
}

impl<T> Vs<T> {
    /// Construct with explicit selected and non-selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 42);
    /// ```
    pub fn new(selected: T, other: T) -> Self {
        Self { selected, other }
    }

    /// Construct with a cloned value for both fields.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::with_cloned(23);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 23);
    /// ```
    pub fn with_cloned(item: T) -> Self
    where
        T: Clone,
    {
        let other = item.clone();
        let selected = item;
        Self { selected, other }
    }

    /// Construct from selected value, default for other.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::with_selected(23);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 0);
    /// ```
    pub fn with_selected(selected: T) -> Self
    where
        T: Default,
    {
        let other = T::default();
        Self { selected, other }
    }

    /// Construct from other value, default for selected.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::with_other(23);
    ///
    /// assert_eq!(v.selected, 0);
    /// assert_eq!(v.other, 23);
    /// ```
    pub fn with_other(other: T) -> Self
    where
        T: Default,
    {
        let selected = T::default();
        Self { selected, other }
    }

    /// Accessor for the primarily selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.selected(), &23);
    /// ```
    pub fn selected(&self) -> &T {
        &self.selected
    }

    /// Mutable ccessor for the primarily selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut v = Vs::new(23, 42);
    /// assert_eq!(v.selected, 23);
    ///
    /// *v.selected_mut() *= 2;
    /// assert_eq!(v.selected, 46);
    /// ```
    pub fn selected_mut(&mut self) -> &mut T {
        &mut self.selected
    }

    /// Accessor for the currently not selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.other(), &42);
    /// ```
    pub fn other(&self) -> &T {
        &self.other
    }

    /// Mutable ccessor for the currently not selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut v = Vs::new(23, 42);
    /// assert_eq!(v.other, 42);
    ///
    /// *v.other_mut() /= 2;
    /// assert_eq!(v.other, 21);
    /// ```
    pub fn other_mut(&mut self) -> &mut T {
        &mut self.other
    }

    /// Returns `true` if any of the values are equal to the given value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert!(v.contains(&23));
    /// assert!(! v.contains(&36));
    /// ```
    pub fn contains(&self, item: &T) -> bool
    where
        T: Eq,
    {
        self.selected == *item || self.other == *item
    }

    /// Returns the [`VsPosition`] of the value, if it is contained.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::{Vs, VsPosition};
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.position(&23), Some(VsPosition::Selected));
    /// assert_eq!(v.position(&42), Some(VsPosition::Other));
    /// assert_eq!(v.position(&36), None);
    /// ```
    pub fn position(&self, item: &T) -> Option<VsPosition>
    where
        T: Eq,
    {
        if self.selected == *item {
            Some(VsPosition::Selected)
        } else if self.other == *item {
            Some(VsPosition::Other)
        } else {
            None
        }
    }

    /// Returns `true` if the given value is currently selected.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert!(v.is_selected(&23));
    /// assert!(! v.is_selected(&42));
    /// assert!(! v.is_selected(&36));
    /// ```
    pub fn is_selected(&self, item: &T) -> bool
    where
        T: Eq,
    {
        self.selected == *item
    }

    /// Returns `true` if the given value is the currently not selected value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert!(v.is_other(&42));
    /// assert!(! v.is_other(&23));
    /// assert!(! v.is_other(&36));
    /// ```
    pub fn is_other(&self, item: &T) -> bool
    where
        T: Eq,
    {
        self.other == *item
    }

    /// Convert from `&Vs<T>` to `Vs<&T>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(
    ///     String::from("AB"),
    ///     String::from("BCD"),
    /// );
    ///
    /// let lens = v.as_ref().map(|s, _| s.len());
    /// assert_eq!(lens.selected, 2);
    /// assert_eq!(lens.other, 3);
    /// ```
    pub fn as_ref(&self) -> Vs<&T> {
        Vs {
            selected: &self.selected,
            other: &self.other,
        }
    }

    /// Convert from `&mut Vs<T>` to `Vs<&mut T>`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut v = Vs::new(23, 42);
    ///
    /// let v_mut = v.as_mut();
    /// *v_mut.selected *= 2;
    /// *v_mut.other /= 2;
    ///
    /// assert_eq!(v.selected, 46);
    /// assert_eq!(v.other, 21);
    /// ```
    pub fn as_mut(&mut self) -> Vs<&mut T> {
        Vs {
            selected: &mut self.selected,
            other: &mut self.other,
        }
    }

    /// Flip the value positions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 42);
    /// v.flip();
    /// assert_eq!(v.selected, 42);
    /// assert_eq!(v.other, 23);
    /// ```
    pub fn flip(&mut self) {
        std::mem::swap(&mut self.selected, &mut self.other);
    }

    /// Return a cloned `Vs<T>` with flipped positions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 42);
    /// let v_flipped = v.to_flipped();
    /// assert_eq!(v_flipped.selected, 42);
    /// assert_eq!(v_flipped.other, 23);
    /// ```
    pub fn to_flipped(&self) -> Self
    where
        T: Clone,
    {
        Self {
            selected: self.other.clone(),
            other: self.selected.clone(),
        }
    }

    /// Convert `Vs<T>` into an instance with flipped positions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let v = Vs::new(23, 42);
    ///
    /// assert_eq!(v.selected, 23);
    /// assert_eq!(v.other, 42);
    /// let v_flipped = v.into_flipped();
    /// assert_eq!(v_flipped.selected, 42);
    /// assert_eq!(v_flipped.other, 23);
    /// ```
    pub fn into_flipped(self) -> Self {
        Self {
            selected: self.other,
            other: self.selected,
        }
    }

    /// Map into another set of values.
    ///
    /// The closure will receive the items' [`VsPosition`] as second argument.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::{Vs, VsPosition};
    /// let v = Vs::new(2, 3);
    /// let v2 = v.map(|value, pos| (value * 2, pos));
    ///
    /// assert_eq!(v2.selected, (4, VsPosition::Selected));
    /// assert_eq!(v2.other, (6, VsPosition::Other));
    /// ```
    pub fn map<U, F>(self, mut map_item: F) -> Vs<U>
    where
        F: FnMut(T, VsPosition) -> U,
    {
        Vs {
            selected: map_item(self.selected, VsPosition::Selected),
            other: map_item(self.other, VsPosition::Other),
        }
    }

    /// Map to another set of values, with consideration of the other present value.
    ///
    /// The closure will receive the items' [`VsPosition`] as second argument, and the
    /// opposing value as the third.
    ///
    /// Since values must be referenced multiple times, this is a by-reference operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::{Vs, VsPosition};
    /// let v = Vs::new(23, 42);
    /// let v2 = v.map_to_with_other(|value, pos, oppo| {
    ///     ((*value, *oppo), pos)
    /// });
    ///
    /// assert_eq!(v2.selected, ((23, 42), VsPosition::Selected));
    /// assert_eq!(v2.other, ((42, 23), VsPosition::Other));
    /// ```
    pub fn map_to_with_other<'a, U, F>(&'a self, mut map_item: F) -> Vs<U>
    where
        F: FnMut(&'a T, VsPosition, &'a T) -> U,
    {
        Vs {
            selected: map_item(&self.selected, VsPosition::Selected, &self.other),
            other: map_item(&self.other, VsPosition::Other, &self.selected),
        }
    }

    /// An iterator over tuples of references to the values and their positions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::{Vs, VsPosition};
    /// let v = Vs::new(23, 42);
    /// let mut vs = v.iter();
    ///
    /// assert_eq!(vs.next(), Some((&23, VsPosition::Selected)));
    /// assert_eq!(vs.next(), Some((&42, VsPosition::Other)));
    /// assert_eq!(vs.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<(&T, VsPosition)> {
        Iter::new(
            (&self.selected, VsPosition::Selected),
            (&self.other, VsPosition::Other),
        )
    }

    /// An iterator over tuples of mutable references to the values and their positions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut v = Vs::new(23, 42);
    /// for (value, pos) in v.iter_mut() {
    ///     if pos.is_selected() {
    ///         *value += 10;
    ///     } else {
    ///         *value += 20;
    ///     }
    /// }
    ///
    /// assert_eq!(v.selected, 33);
    /// assert_eq!(v.other, 62);
    /// ```
    pub fn iter_mut(&mut self) -> Iter<(&mut T, VsPosition)> {
        Iter::new(
            (&mut self.selected, VsPosition::Selected),
            (&mut self.other, VsPosition::Other),
        )
    }

    /// An iterator over tuples of references to the values, their positions, and a reference
    /// to the opposing value.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::{Vs, VsPosition};
    /// let v = Vs::new(23, 42);
    /// let mut vs = v.iter_with_other();
    ///
    /// assert_eq!(vs.next(), Some((&23, VsPosition::Selected, &42)));
    /// assert_eq!(vs.next(), Some((&42, VsPosition::Other, &23)));
    /// assert_eq!(vs.next(), None);
    /// ```
    pub fn iter_with_other(&self) -> Iter<(&T, VsPosition, &T)> {
        Iter::new(
            (&self.selected, VsPosition::Selected, &self.other),
            (&self.other, VsPosition::Other, &self.selected),
        )
    }
}

impl<T> Vs<&T> {
    /// Map `Vs<&T>` to `Vs<T>` via cloning.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let s1 = String::from("A");
    /// let s2 = String::from("B");
    /// let v = Vs::new(&s1, &s2);
    /// let vs: Vs<String> = v.cloned();
    ///
    /// assert_eq!(vs.selected, s1);
    /// assert_eq!(vs.other, s2);
    /// ```
    pub fn cloned(self) -> Vs<T>
    where
        T: Clone,
    {
        Vs {
            selected: self.selected.clone(),
            other: self.other.clone(),
        }
    }

    /// Map `Vs<&T>` to `Vs<T>` via copying.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let n1 = 23;
    /// let n2 = 42;
    /// let v = Vs::new(&n1, &n2);
    /// let vn: Vs<i32> = v.copied();
    ///
    /// assert_eq!(vn.selected, 23);
    /// assert_eq!(vn.other, 42);
    /// ```
    pub fn copied(self) -> Vs<T>
    where
        T: Copy,
    {
        Vs {
            selected: *self.selected,
            other: *self.other,
        }
    }
}

impl<T> Vs<&mut T> {
    /// Map `Vs<&mut T>` to `Vs<T>` via cloning.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut s1 = String::from("A");
    /// let mut s2 = String::from("B");
    /// let v = Vs::new(&mut s1, &mut s2);
    /// let vs: Vs<String> = v.cloned();
    ///
    /// assert_eq!(vs.selected, s1);
    /// assert_eq!(vs.other, s2);
    /// ```
    pub fn cloned(self) -> Vs<T>
    where
        T: Clone,
    {
        Vs {
            selected: self.selected.clone(),
            other: self.other.clone(),
        }
    }

    /// Map `Vs<&mut T>` to `Vs<T>` via copying.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use coupled::Vs;
    /// let mut n1 = 23;
    /// let mut n2 = 42;
    /// let v = Vs::new(&mut n1, &mut n2);
    /// let vn: Vs<i32> = v.copied();
    ///
    /// assert_eq!(vn.selected, 23);
    /// assert_eq!(vn.other, 42);
    /// ```
    pub fn copied(self) -> Vs<T>
    where
        T: Copy,
    {
        Vs {
            selected: *self.selected,
            other: *self.other,
        }
    }
}

/// An iterator over the values and their positions.
///
/// # Example
///
/// ```rust
/// # use coupled::{Vs, VsPosition};
/// let v = Vs::new(23, 42);
/// let mut vs = v.into_iter();
///
/// assert_eq!(vs.next(), Some((23, VsPosition::Selected)));
/// assert_eq!(vs.next(), Some((42, VsPosition::Other)));
/// assert_eq!(vs.next(), None);
/// ```
impl<T> IntoIterator for Vs<T> {
    type Item = (T, VsPosition);
    type IntoIter = Iter<(T, VsPosition)>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(
            (self.selected, VsPosition::Selected),
            (self.other, VsPosition::Other),
        )
    }
}

/// An iterator over references to the values and their positions.
///
/// # Example
///
/// ```rust
/// # use coupled::{Vs, VsPosition};
/// let v = &Vs::new(23, 42);
/// let mut vs = v.into_iter();
///
/// assert_eq!(vs.next(), Some((&23, VsPosition::Selected)));
/// assert_eq!(vs.next(), Some((&42, VsPosition::Other)));
/// assert_eq!(vs.next(), None);
/// ```
impl<'a, T> IntoIterator for &'a Vs<T> {
    type Item = (&'a T, VsPosition);
    type IntoIter = Iter<(&'a T, VsPosition)>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(
            (&self.selected, VsPosition::Selected),
            (&self.other, VsPosition::Other),
        )
    }
}

/// An iterator over mutable references to the values and their positions.
///
/// # Example
///
/// ```rust
/// # use coupled::{Vs, VsPosition};
/// let v = &mut Vs::new(23, 42);
/// let mut vs = v.into_iter();
///
/// assert_eq!(vs.next(), Some((&mut 23, VsPosition::Selected)));
/// assert_eq!(vs.next(), Some((&mut 42, VsPosition::Other)));
/// assert_eq!(vs.next(), None);
/// ```
impl<'a, T> IntoIterator for &'a mut Vs<T> {
    type Item = (&'a mut T, VsPosition);
    type IntoIter = Iter<(&'a mut T, VsPosition)>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(
            (&mut self.selected, VsPosition::Selected),
            (&mut self.other, VsPosition::Other),
        )
    }
}

/// Construct from a two-item tuple.
///
/// # Example
///
/// ```rust
/// # use coupled::Vs;
/// let v: Vs<_> = (23, 42).into();
/// assert_eq!(v, Vs::new(23, 42));
/// ```
impl<T> From<(T, T)> for Vs<T> {
    fn from((selected, other): (T, T)) -> Self {
        Self { selected, other }
    }
}

/// Construct from a two-value array.
///
/// # Example
///
/// ```rust
/// # use coupled::Vs;
/// let v: Vs<_> = [23, 42].into();
/// assert_eq!(v, Vs::new(23, 42));
/// ```
impl<T> From<[T; 2]> for Vs<T> {
    fn from([selected, other]: [T; 2]) -> Self {
        Self { selected, other }
    }
}

/// Construct from a [`Pair`].
///
/// # Example
///
/// ```rust
/// # use coupled::{Vs, Pair};
/// let p = Pair::new(23, 42);
/// let v: Vs<_> = p.into();
/// assert_eq!(v, Vs::new(23, 42));
/// ```
impl<T> From<Pair<T>> for Vs<T> {
    fn from(pair: Pair<T>) -> Self {
        let [selected, other] = pair.into_array();
        Self { selected, other }
    }
}

/// The position of a value in a [`Vs`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(
    feature = "serde",
    derive(serde::Serialize, serde::Deserialize),
)]
pub enum VsPosition {
    /// The value is the primarily selected value.
    Selected,
    /// The value is the not selected value.
    Other,
}

impl VsPosition {
    /// Returns true for [`VsPosition::Selected`].
    pub fn is_selected(self) -> bool {
        self == Self::Selected
    }

    /// Returns true for [`VsPosition::Other`].
    pub fn is_other(self) -> bool {
        self == Self::Other
    }
}
