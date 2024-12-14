use crate::CowStr;
use std::fmt;

pub(crate) fn valid(src: &str) -> usize {
    use State::*;

    let mut n = 0;
    let mut state = Start;
    for c in src.bytes() {
        n += 1;
        state = state.step(c);
        match state {
            Done | Invalid => break,
            _ => {}
        }
    }

    if matches!(state, Done) {
        n
    } else {
        0
    }
}

/// Stores an attribute value that supports backslash escapes of ASCII punctuation upon displaying,
/// without allocating.
///
/// Each value is paired together with an [`AttributeKind`] in order to form an element.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct AttributeValue<'s> {
    raw: CowStr<'s>,
}

impl<'s> AttributeValue<'s> {
    /// Create an empty attribute value.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Processes the attribute value escapes and returns an iterator of the parts of the value
    /// that should be displayed.
    pub fn parts(&'s self) -> AttributeValueParts<'s> {
        AttributeValueParts { ahead: &self.raw }
    }

    // lifetime is 's to avoid allocation if empty value is concatenated with single value
    fn extend(&mut self, s: &'s str) {
        if s.is_empty() {
            return;
        }
        if !self.raw.is_empty() {
            self.extend_raw(" ");
        }
        self.extend_raw(s);
    }

    fn extend_raw(&mut self, s: &'s str) {
        match &mut self.raw {
            CowStr::Borrowed(prev) => {
                if prev.is_empty() {
                    *prev = s;
                } else {
                    self.raw = format!("{}{}", prev, s).into();
                }
            }
            CowStr::Owned(ref mut prev) => {
                if prev.is_empty() {
                    self.raw = s.into();
                } else {
                    prev.push_str(s);
                }
            }
        }
    }
}

impl<'s> From<&'s str> for AttributeValue<'s> {
    fn from(value: &'s str) -> Self {
        Self { raw: value.into() }
    }
}

impl<'s> From<CowStr<'s>> for AttributeValue<'s> {
    fn from(value: CowStr<'s>) -> Self {
        Self { raw: value }
    }
}

impl From<String> for AttributeValue<'_> {
    fn from(value: String) -> Self {
        Self { raw: value.into() }
    }
}

impl fmt::Display for AttributeValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.parts().try_for_each(|part| f.write_str(part))
    }
}

/// An iterator over the parts of an [`AttributeValue`] that should be displayed.
pub struct AttributeValueParts<'s> {
    ahead: &'s str,
}

impl<'s> Iterator for AttributeValueParts<'s> {
    type Item = &'s str;

    fn next(&mut self) -> Option<Self::Item> {
        for (i, _) in self.ahead.match_indices('\\') {
            match self.ahead.as_bytes().get(i + 1) {
                Some(b'\\') => {
                    let next = &self.ahead[..i + 1];
                    self.ahead = &self.ahead[i + 2..];
                    return Some(next);
                }
                Some(c) if c.is_ascii_punctuation() => {
                    let next = &self.ahead[..i];
                    self.ahead = &self.ahead[i + 1..];
                    return Some(next);
                }
                _ => {}
            }
        }

        (!self.ahead.is_empty()).then(|| std::mem::take(&mut self.ahead))
    }
}

/// The kind of an element within an attribute set.
///
/// Each kind is paired together with an [`AttributeValue`] to form an element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttributeKind<'s> {
    /// A class element, e.g. `.a`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{.a}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some((AttributeKind::Class, "a".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    Class,
    /// An id element, e.g. `#a`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{#a}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some((AttributeKind::Id, "a".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    Id,
    /// A key-value pair element, e.g. `key=value`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from(r#"{key=value id="a"}"#)
    ///     .unwrap()
    ///     .into_iter();
    /// assert_eq!(
    ///     a.next(),
    ///     Some((AttributeKind::Pair { key: "key" }, "value".into())),
    /// );
    /// assert_eq!(
    ///     a.next(),
    ///     Some((AttributeKind::Pair { key: "id" }, "a".into())),
    /// );
    /// assert_eq!(a.next(), None);
    /// ```
    Pair { key: &'s str },
    /// A comment element, e.g. `%cmt%`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{%cmt0% %cmt1}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some((AttributeKind::Comment, "cmt0".into())));
    /// assert_eq!(a.next(), Some((AttributeKind::Comment, "cmt1".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    Comment,
}

impl<'s> AttributeKind<'s> {
    /// Returns the element's key, if applicable.
    #[must_use]
    pub fn key(&self) -> Option<&'s str> {
        match self {
            AttributeKind::Class => Some("class"),
            AttributeKind::Id => Some("id"),
            AttributeKind::Pair { key } => Some(key),
            AttributeKind::Comment => None,
        }
    }
}

/// A set of attributes, with order, duplicates and comments preserved.
///
/// `Attributes` is a wrapper object around a [`Vec`] containing the elements of the set, each a
/// pair of an [`AttributeKind`] and an [`AttributeValue`]. It implements [`std::ops::Deref`] and
/// [`std::ops::DerefMut`] so methods of the inner [`Vec`] and [`slice`] can be used directly on
/// the `Attributes` to access or modify the elements. The wrapper also implements [`From`] and
/// [`Into`] for [`Vec`] so one can easily add or remove the wrapper.
///
/// `Attributes` are typically created by a [`crate::Parser`] and placed in the [`crate::Event`]s
/// that it emits. `Attributes` can also be created from a djot string representation, see
/// [`Attributes::try_from`].
///
/// The attribute elements can be accessed using e.g. [`slice::iter`] or [`slice::iter_mut`], but
/// if e.g. duplicate keys or comments are not desired, refer to [`Attributes::get_value`] and
/// [`Attributes::unique_pairs`].
///
/// # Examples
///
/// Access the inner [`Vec`]:
///
/// ```
/// # use jotdown::*;
/// let a: Attributes = r#"{#a .b id=c class=d key="val" %comment%}"#
///     .try_into()
///     .unwrap();
/// assert_eq!(
///     Vec::from(a),
///     vec![
///         (AttributeKind::Id, "a".into()),
///         (AttributeKind::Class, "b".into()),
///         (AttributeKind::Pair { key: "id" }, "c".into()),
///         (AttributeKind::Pair { key: "class" }, "d".into()),
///         (AttributeKind::Pair { key: "key" }, "val".into()),
///         (AttributeKind::Comment, "comment".into()),
///     ],
/// );
/// ```
///
/// Replace a value:
///
/// ```
/// # use jotdown::*;
/// let mut attrs = Attributes::try_from("{key1=val1 key2=val2}").unwrap();
///
/// for (attr, value) in &mut attrs {
///     if attr.key() == Some("key2") {
///         *value = "new_val".into();
///     }
/// }
///
/// assert_eq!(
///     attrs.as_slice(),
///     &[
///         (AttributeKind::Pair { key: "key1" }, "val1".into()),
///         (AttributeKind::Pair { key: "key2" }, "new_val".into()),
///     ]
/// );
/// ```
///
/// Filter out keys with a specific prefix:
///
/// ```
/// # use jotdown::*;
/// let a: Attributes = Attributes::try_from("{ign:x=a ign:y=b z=c}")
///     .unwrap()
///     .into_iter()
///     .filter(|(k, _)| !matches!(k.key(), Some(key) if key.starts_with("ign:")))
///     .collect();
/// let b = Attributes::try_from("{z=c}").unwrap();
/// assert_eq!(a, b);
/// ```
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Attributes<'s>(Vec<AttributeElem<'s>>);

type AttributeElem<'s> = (AttributeKind<'s>, AttributeValue<'s>);

impl<'s> Attributes<'s> {
    /// Create an empty collection.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn take(&mut self) -> Self {
        std::mem::take(self)
    }

    /// Parse and append attributes.
    pub(crate) fn parse(&mut self, input: &'s str) -> Result<(), usize> {
        let mut parser = Parser::new(self.take());
        parser.parse(input)?;
        *self = parser.finish();
        Ok(())
    }

    /// Returns whether the specified key exists in the set.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let a = Attributes::try_from("{x=y .a}").unwrap();
    /// assert!(a.contains_key("x"));
    /// assert!(!a.contains_key("y"));
    /// assert!(a.contains_key("class"));
    /// ```
    #[must_use]
    pub fn contains_key(&self, key: &str) -> bool {
        self.0
            .iter()
            .any(|(k, _)| matches!(k.key(), Some(k) if k == key))
    }

    /// Returns the value corresponding to the provided attribute key.
    ///
    /// Note: A copy of the value is returned rather than a reference, due to class values
    /// differing from its internal representation.
    ///
    /// # Examples
    ///
    /// For the "class" key, concatenate all class values:
    ///
    /// ```
    /// # use jotdown::*;
    /// assert_eq!(
    ///     Attributes::try_from("{.a class=b}").unwrap().get_value("class"),
    ///     Some("a b".into()),
    /// );
    /// ```
    ///
    /// For other keys, return the last set value:
    ///
    /// ```
    /// # use jotdown::*;
    /// assert_eq!(
    ///     Attributes::try_from("{x=a x=b}").unwrap().get_value("x"),
    ///     Some("b".into()),
    /// );
    /// ```
    #[must_use]
    pub fn get_value(&self, key: &str) -> Option<AttributeValue> {
        if key == "class"
            && self
                .0
                .iter()
                .filter(|(k, _)| k.key() == Some("class"))
                .count()
                > 1
        {
            let mut value = AttributeValue::new();
            for (k, v) in &self.0 {
                if k.key() == Some("class") {
                    value.extend(&v.raw);
                }
            }
            Some(value)
        } else {
            self.0
                .iter()
                .rfind(|(k, _)| k.key() == Some(key))
                .map(|(_, v)| v.clone())
        }
    }

    /// Returns an iterator that only emits a single key-value pair per unique key, i.e. like they
    /// appear in the rendered output.
    ///
    /// # Examples
    ///
    /// For "class" elements, values are concatenated:
    ///
    /// ```
    /// # use jotdown::*;
    /// let a: Attributes = "{class=a .b}".try_into().unwrap();
    /// let mut pairs = a.unique_pairs();
    /// assert_eq!(pairs.next(), Some(("class", "a b".into())));
    /// assert_eq!(pairs.next(), None);
    /// ```
    ///
    /// For other keys, the last set value is used:
    ///
    /// ```
    /// # use jotdown::*;
    /// let a: Attributes = "{id=a key=b #c key=d}".try_into().unwrap();
    /// let mut pairs = a.unique_pairs();
    /// assert_eq!(pairs.next(), Some(("id", "c".into())));
    /// assert_eq!(pairs.next(), Some(("key", "d".into())));
    /// assert_eq!(pairs.next(), None);
    /// ```
    ///
    /// Comments are ignored:
    ///
    /// ```
    /// # use jotdown::*;
    /// let a: Attributes = "{%cmt% #a}".try_into().unwrap();
    /// let mut pairs = a.unique_pairs();
    /// assert_eq!(pairs.next(), Some(("id", "a".into())));
    /// ```
    #[must_use]
    pub fn unique_pairs<'a>(&'a self) -> AttributePairsIter<'a, 's> {
        AttributePairsIter {
            attrs: &self.0,
            pos: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseAttributesError {
    /// Location in input string where attributes became invalid.
    pub pos: usize,
}

impl<'s> TryFrom<&'s str> for Attributes<'s> {
    type Error = ParseAttributesError;

    /// Parse attributes represented in the djot syntax.
    ///
    /// Note: The [`Attributes`] borrows from the provided [`&str`], it is therefore not compatible
    /// with the existing [`std::str::FromStr`] trait.
    ///
    /// # Examples
    ///
    /// A single set of attributes can be parsed:
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{.a}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some((AttributeKind::Class, "a".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    ///
    /// Multiple sets can be parsed if they immediately follow the each other:
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{.a}{.b}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some((AttributeKind::Class, "a".into())));
    /// assert_eq!(a.next(), Some((AttributeKind::Class, "b".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    ///
    /// When the attributes are invalid, the position where the parsing failed is returned:
    ///
    /// ```
    /// # use jotdown::*;
    /// assert_eq!(Attributes::try_from("{.a $}"), Err(ParseAttributesError { pos: 4 }));
    /// ```
    fn try_from(s: &'s str) -> Result<Self, Self::Error> {
        let mut a = Attributes::new();
        match a.parse(s) {
            Ok(()) => Ok(a),
            Err(pos) => Err(ParseAttributesError { pos }),
        }
    }
}

impl<'s> From<Vec<AttributeElem<'s>>> for Attributes<'s> {
    fn from(v: Vec<AttributeElem<'s>>) -> Self {
        Self(v)
    }
}

impl<'s> From<Attributes<'s>> for Vec<AttributeElem<'s>> {
    fn from(a: Attributes<'s>) -> Self {
        a.0
    }
}

impl<'s> std::ops::Deref for Attributes<'s> {
    type Target = Vec<AttributeElem<'s>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for Attributes<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[cfg(test)]
impl<'s> FromIterator<(AttributeKind<'s>, &'s str)> for Attributes<'s> {
    fn from_iter<I: IntoIterator<Item = (AttributeKind<'s>, &'s str)>>(iter: I) -> Self {
        let attrs = iter
            .into_iter()
            .map(|(a, v)| (a, v.into()))
            .collect::<Vec<_>>();
        Attributes(attrs)
    }
}

impl<'s> FromIterator<AttributeElem<'s>> for Attributes<'s> {
    /// Create `Attributes` from an iterator of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let e0 = (AttributeKind::Class, AttributeValue::from("a"));
    /// let e1 = (AttributeKind::Id, AttributeValue::from("b"));
    /// let a: Attributes = [e0.clone(), e1.clone()].into_iter().collect();
    /// assert_eq!(format!("{:?}", a), "{.a #b}");
    /// let mut elems = a.into_iter();
    /// assert_eq!(elems.next(), Some(e0));
    /// assert_eq!(elems.next(), Some(e1));
    /// ```
    fn from_iter<I: IntoIterator<Item = AttributeElem<'s>>>(iter: I) -> Self {
        Attributes(iter.into_iter().collect())
    }
}

impl std::fmt::Debug for Attributes<'_> {
    /// Formats the attributes using the given formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let a = r#"{#a .b id=c class=d key="val" %comment%}"#;
    /// let b = r#"{#a .b id="c" class="d" key="val" %comment%}"#;
    /// assert_eq!(format!("{:?}", Attributes::try_from(a).unwrap()), b);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in self {
            if !first {
                write!(f, " ")?;
            }
            first = false;
            match k {
                AttributeKind::Class => write!(f, ".{}", v.raw)?,
                AttributeKind::Id => write!(f, "#{}", v.raw)?,
                AttributeKind::Pair { key } => write!(f, "{}=\"{}\"", key, v.raw)?,
                AttributeKind::Comment => write!(f, "%{}%", v.raw)?,
            }
        }
        write!(f, "}}")
    }
}

impl<'s> IntoIterator for Attributes<'s> {
    type Item = AttributeElem<'s>;

    type IntoIter = std::vec::IntoIter<AttributeElem<'s>>;

    /// Turn into an iterator of attribute elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let a = Attributes::try_from("{key1=val1 key2=val2}").unwrap();
    /// let mut elems = a.into_iter();
    /// assert_eq!(
    ///     elems.next(),
    ///     Some((
    ///         AttributeKind::Pair { key: "key1" },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some((
    ///         AttributeKind::Pair { key: "key2" },
    ///         AttributeValue::from("val2"),
    ///     )),
    /// );
    /// assert_eq!(elems.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'i, 's> IntoIterator for &'i Attributes<'s> {
    type Item = &'i AttributeElem<'s>;

    type IntoIter = std::slice::Iter<'i, AttributeElem<'s>>;

    /// Create an iterator of borrowed attribute elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let a = Attributes::try_from("{key1=val1 key2=val2}").unwrap();
    /// let mut elems = a.iter();
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&(
    ///         AttributeKind::Pair { key: "key1" },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&(
    ///         AttributeKind::Pair { key: "key2" },
    ///         AttributeValue::from("val2"),
    ///     )),
    /// );
    /// assert_eq!(elems.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'i, 's> IntoIterator for &'i mut Attributes<'s> {
    type Item = &'i mut AttributeElem<'s>;

    type IntoIter = std::slice::IterMut<'i, AttributeElem<'s>>;

    /// Create an iterator of mutably borrowed attribute elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let mut a = Attributes::try_from("{key1=val1 key2=val2}").unwrap();
    /// let mut elems = a.iter_mut();
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&mut (
    ///         AttributeKind::Pair { key: "key1" },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&mut (
    ///         AttributeKind::Pair { key: "key2" },
    ///         AttributeValue::from("val2"),
    ///     )),
    /// );
    /// assert_eq!(elems.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

/// Iterator of unique attribute pairs.
///
/// See [`Attributes::unique_pairs`] for more information.
pub struct AttributePairsIter<'a, 's> {
    attrs: &'a [AttributeElem<'s>],
    pos: usize,
}

impl<'a: 's, 's> Iterator for AttributePairsIter<'a, 's> {
    type Item = (&'s str, AttributeValue<'s>);
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((key, value)) = self.attrs[self.pos..].first() {
            self.pos += 1;
            let key = if let Some(k) = key.key() {
                k
            } else {
                continue; // ignore comments
            };

            if self.attrs[..self.pos - 1]
                .iter()
                .any(|(k, _)| k.key() == Some(key))
            {
                continue; // already emitted when this key first encountered
            }

            if key == "class" {
                let mut value = value.clone();
                for (k, v) in &self.attrs[self.pos..] {
                    if k.key() == Some("class") {
                        value.extend(&v.raw);
                    }
                }
                return Some((key, value));
            }

            if let Some((_, v)) = self.attrs[self.pos..]
                .iter()
                .rfind(|(k, _)| k.key() == Some(key))
            {
                return Some((key, v.clone())); // emit last value when key first encountered
            }

            return Some((key, value.clone()));
        }
        None
    }
}

#[derive(Clone)]
pub struct Validator {
    state: State,
}

impl Validator {
    pub fn new() -> Self {
        Self {
            state: State::Start,
        }
    }

    pub fn restart(&mut self) {
        self.state = State::Start;
    }

    /// Returns number of valid bytes parsed (0 means invalid) if finished, otherwise more input is
    /// needed.
    pub fn parse(&mut self, input: &str) -> Option<usize> {
        let mut bytes = input.bytes();
        for c in &mut bytes {
            self.state = self.state.step(c);
            match self.state {
                State::Done => return Some(input.len() - bytes.len()),
                State::Invalid => return Some(0),
                _ => {}
            }
        }
        None
    }
}

/// Attributes parser, take input of one or more consecutive attributes and create an `Attributes`
/// object.
pub struct Parser<'s> {
    attrs: Attributes<'s>,
    state: State,
}

impl<'s> Parser<'s> {
    pub fn new(attrs: Attributes<'s>) -> Self {
        Self {
            attrs,
            state: State::Start,
        }
    }

    /// Return value indicates the number of bytes parsed if finished. If None, more input is
    /// required to finish the attributes.
    pub fn parse(&mut self, input: &'s str) -> Result<(), usize> {
        use State::*;

        let mut pos_prev = 0;
        for (pos, c) in input.bytes().enumerate() {
            let state_next = self.state.step(c);

            if matches!(state_next, Invalid) {
                return Err(pos);
            }

            let st = std::mem::replace(&mut self.state, state_next);

            if st != self.state && !matches!((st, self.state), (ValueEscape, _) | (_, ValueEscape))
            {
                let content = &input[pos_prev..pos];
                pos_prev = pos;
                match st {
                    Class => self.attrs.push((AttributeKind::Class, content.into())),
                    Identifier => self.attrs.push((AttributeKind::Id, content.into())),
                    Key => self
                        .attrs
                        .push((AttributeKind::Pair { key: content }, "".into())),
                    Value | ValueQuoted | ValueContinued => {
                        let last = self.attrs.len() - 1;
                        self.attrs.0[last]
                            .1
                            .extend(&content[usize::from(matches!(st, ValueQuoted))..]);
                    }
                    Comment | CommentNewline => {
                        let last = self.attrs.len() - 1;
                        self.attrs.0[last].1.extend_raw(if matches!(st, Comment) {
                            content
                        } else {
                            "\n"
                        });
                    }
                    CommentFirst => self.attrs.push((AttributeKind::Comment, "".into())),
                    _ => {}
                }
            };

            debug_assert!(!matches!(self.state, Invalid));

            if matches!(self.state, Done) {
                if input[pos + 1..].starts_with('{') {
                    self.state = Start;
                } else {
                    return Ok(());
                }
            }
        }

        Ok(())
    }

    pub fn finish(self) -> Attributes<'s> {
        self.attrs
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Start,
    Whitespace,
    CommentFirst,
    Comment,
    CommentNewline,
    ClassFirst,
    Class,
    IdentifierFirst,
    Identifier,
    Key,
    ValueFirst,
    Value,
    ValueQuoted,
    ValueEscape,
    ValueNewline,
    ValueContinued,
    Done,
    Invalid,
}

impl State {
    fn step(self, c: u8) -> State {
        use State::*;

        match self {
            Start if c == b'{' => Whitespace,
            Start => Invalid,
            Whitespace => match c {
                b'}' => Done,
                b'.' => ClassFirst,
                b'#' => IdentifierFirst,
                b'%' => CommentFirst,
                c if is_name(c) => Key,
                c if c.is_ascii_whitespace() => Whitespace,
                _ => Invalid,
            },
            CommentFirst | Comment | CommentNewline if c == b'%' => Whitespace,
            CommentFirst | Comment | CommentNewline if c == b'}' => Done,
            CommentFirst | Comment | CommentNewline if c == b'\n' => CommentNewline,
            CommentFirst | Comment | CommentNewline => Comment,
            ClassFirst if is_name(c) => Class,
            ClassFirst => Invalid,
            IdentifierFirst if is_name(c) => Identifier,
            IdentifierFirst => Invalid,
            s @ (Class | Identifier | Value) if is_name(c) => s,
            Class | Identifier | Value if c.is_ascii_whitespace() => Whitespace,
            Class | Identifier | Value if c == b'}' => Done,
            Class | Identifier | Value => Invalid,
            Key if is_name(c) => Key,
            Key if c == b'=' => ValueFirst,
            Key => Invalid,
            ValueFirst if is_name(c) => Value,
            ValueFirst if c == b'"' => ValueQuoted,
            ValueFirst => Invalid,
            ValueQuoted | ValueNewline | ValueContinued if c == b'"' => Whitespace,
            ValueQuoted | ValueNewline | ValueContinued | ValueEscape if c == b'\n' => ValueNewline,
            ValueQuoted if c == b'\\' => ValueEscape,
            ValueQuoted | ValueEscape => ValueQuoted,
            ValueNewline | ValueContinued => ValueContinued,
            Invalid | Done => panic!("{:?}", self),
        }
    }
}

pub fn is_name(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b':' | b'_' | b'-')
}

#[cfg(test)]
mod test {
    use super::AttributeKind::*;
    use super::*;

    macro_rules! test_attr {
        ($src:expr, [$($exp:expr),* $(,)?], [$($exp_uniq:expr),* $(,)?] $(,)?) => {
            #[allow(unused)]
            let mut attr = Attributes::try_from($src).unwrap();

            let actual = attr.iter().map(|(k, v)| (k.clone(), v.to_string())).collect::<Vec<_>>();
            let expected = &[$($exp),*].map(|(k, v): (_, &str)| (k, v.to_string()));
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);

            let actual = attr.unique_pairs().map(|(k, v)| (k, v.to_string())).collect::<Vec<_>>();
            let expected = &[$($exp_uniq),*].map(|(k, v): (_, &str)| (k, v.to_string()));
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn empty() {
        test_attr!("{}", [], []);
    }

    #[test]
    fn class_id() {
        test_attr!(
            "{.some_class #some_id}",
            [(Class, "some_class"), (Id, "some_id")],
            [("class", "some_class"), ("id", "some_id")],
        );
        test_attr!("{.a .b}", [(Class, "a"), (Class, "b")], [("class", "a b")]);
        test_attr!("{#a #b}", [(Id, "a"), (Id, "b")], [("id", "b")]);
    }

    #[test]
    fn value_unquoted() {
        test_attr!(
            "{attr0=val0 attr1=val1}",
            [
                (Pair { key: "attr0" }, "val0"),
                (Pair { key: "attr1" }, "val1"),
            ],
            [("attr0", "val0"), ("attr1", "val1")],
        );
    }

    #[test]
    fn value_quoted() {
        test_attr!(
            r#"{attr0="val0" attr1="val1"}"#,
            [
                (Pair { key: "attr0" }, "val0"),
                (Pair { key: "attr1" }, "val1"),
            ],
            [("attr0", "val0"), ("attr1", "val1")],
        );
        test_attr!(
            r#"{#id .class style="color:red"}"#,
            [
                (Id, "id"),
                (Class, "class"),
                (Pair { key: "style" }, "color:red"),
            ],
            [("id", "id"), ("class", "class"), ("style", "color:red")]
        );
    }

    #[test]
    fn value_newline() {
        test_attr!(
            "{attr0=\"abc\ndef\"}",
            [(Pair { key: "attr0" }, "abc def")],
            [("attr0", "abc def")]
        );
    }

    #[test]
    fn comment() {
        test_attr!("{%}", [(Comment, "")], []);
        test_attr!("{%%}", [(Comment, "")], []);
        test_attr!("{ % abc % }", [(Comment, " abc ")], []);
        test_attr!(
            "{ .some_class % #some_id }",
            [(Class, "some_class"), (Comment, " #some_id ")],
            [("class", "some_class")]
        );
        test_attr!(
            "{ .some_class % abc % #some_id}",
            [(Class, "some_class"), (Comment, " abc "), (Id, "some_id")],
            [("class", "some_class"), ("id", "some_id")],
        );
    }

    #[test]
    fn comment_newline() {
        test_attr!("{%a\nb%}", [(Comment, "a\nb")], []);
        test_attr!("{%\nb%}", [(Comment, "\nb")], []);
        test_attr!("{%a\n%}", [(Comment, "a\n")], []);
        test_attr!("{%a\n}", [(Comment, "a\n")], []);
        test_attr!("{%\nb\n%}", [(Comment, "\nb\n")], []);
    }

    #[test]
    fn escape() {
        test_attr!(
            r#"{attr="with escaped \~ char"}"#,
            [(Pair { key: "attr" }, "with escaped ~ char")],
            [("attr", "with escaped ~ char")]
        );
        test_attr!(
            r#"{key="quotes \" should be escaped"}"#,
            [(Pair { key: "key" }, r#"quotes " should be escaped"#)],
            [("key", r#"quotes " should be escaped"#)]
        );
    }

    #[test]
    fn escape_backslash() {
        test_attr!(
            r#"{attr="with\\backslash"}"#,
            [(Pair { key: "attr" }, r"with\backslash")],
            [("attr", r"with\backslash")]
        );
        test_attr!(
            r#"{attr="with many backslashes\\\\"}"#,
            [(Pair { key: "attr" }, r"with many backslashes\\")],
            [("attr", r"with many backslashes\\")]
        );
        test_attr!(
            r#"{attr="\\escaped backslash at start"}"#,
            [(Pair { key: "attr" }, r"\escaped backslash at start")],
            [("attr", r"\escaped backslash at start")]
        );
    }

    #[test]
    fn only_escape_punctuation() {
        test_attr!(
            r#"{attr="do not \escape"}"#,
            [(Pair { key: "attr" }, r"do not \escape")],
            [("attr", r"do not \escape")]
        );
        test_attr!(
            r#"{attr="\backslash at the beginning"}"#,
            [(Pair { key: "attr" }, r"\backslash at the beginning")],
            [("attr", r"\backslash at the beginning")]
        );
    }

    #[test]
    fn valid_full() {
        let src = "{.class %comment%}";
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_unicode() {
        let src = r#"{a="б"}"#;
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_empty() {
        let src = "{}";
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_whitespace() {
        let src = "{ \n }";
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_comment() {
        let src = "{%comment%}";
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_trailing() {
        let src = "{.class}{.ignore}";
        let src_valid = "{.class}";
        assert_eq!(super::valid(src), src_valid.len());
    }

    #[test]
    fn valid_invalid() {
        assert_eq!(super::valid(" {.valid}"), 0);
        assert_eq!(super::valid("{.class invalid}"), 0);
        assert_eq!(super::valid("abc"), 0);
        assert_eq!(super::valid("{.abc.}"), 0);
    }

    #[test]
    fn get_value_named() {
        assert_eq!(
            Attributes::try_from("{x=a}").unwrap().get_value("x"),
            Some("a".into()),
        );
        assert_eq!(
            Attributes::try_from("{x=a x=b}").unwrap().get_value("x"),
            Some("b".into()),
        );
    }

    #[test]
    fn get_value_id() {
        assert_eq!(
            Attributes::try_from("{#a}").unwrap().get_value("id"),
            Some("a".into()),
        );
        assert_eq!(
            Attributes::try_from("{#a #b}").unwrap().get_value("id"),
            Some("b".into()),
        );
        assert_eq!(
            Attributes::try_from("{#a id=b}").unwrap().get_value("id"),
            Some("b".into()),
        );
        assert_eq!(
            Attributes::try_from("{id=a #b}").unwrap().get_value("id"),
            Some("b".into()),
        );
    }

    #[test]
    fn get_value_class() {
        assert_eq!(
            Attributes::try_from("{.a #a .b #b .c}")
                .unwrap()
                .get_value("class"),
            Some("a b c".into()),
        );
        assert_eq!(
            Attributes::try_from("{#a}").unwrap().get_value("class"),
            None,
        );
        assert_eq!(
            Attributes::try_from("{.a}").unwrap().get_value("class"),
            Some("a".into()),
        );
        assert_eq!(
            Attributes::try_from("{.a #a class=b #b .c}")
                .unwrap()
                .get_value("class"),
            Some("a b c".into()),
        );
    }

    #[test]
    fn from_to_vec() {
        let v0: Vec<(AttributeKind, AttributeValue)> = vec![(Class, "a".into()), (Id, "b".into())];
        let a: Attributes = v0.clone().into();
        assert_eq!(format!("{:?}", a), "{.a #b}");
        let v1: Vec<(AttributeKind, AttributeValue)> = a.into();
        assert_eq!(v0, v1);
    }
}
