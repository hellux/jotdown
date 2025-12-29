use crate::CowStr;

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

impl std::fmt::Display for AttributeValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    ///     Some((AttributeKind::Pair { key: "key".into() }, "value".into())),
    /// );
    /// assert_eq!(
    ///     a.next(),
    ///     Some((AttributeKind::Pair { key: "id".into() }, "a".into())),
    /// );
    /// assert_eq!(a.next(), None);
    /// ```
    Pair { key: CowStr<'s> },
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

impl AttributeKind<'_> {
    /// Returns the element's key, if applicable.
    #[must_use]
    pub fn key(&self) -> Option<&str> {
        match self {
            AttributeKind::Class => Some("class"),
            AttributeKind::Id => Some("id"),
            AttributeKind::Pair { key } => Some(key.as_ref()),
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
///         (AttributeKind::Pair { key: "id".into() }, "c".into()),
///         (AttributeKind::Pair { key: "class".into() }, "d".into()),
///         (AttributeKind::Pair { key: "key".into() }, "val".into()),
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
///         (AttributeKind::Pair { key: "key1".into() }, "val1".into()),
///         (AttributeKind::Pair { key: "key2".into() }, "new_val".into()),
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
        let input = input.trim_end_matches(|c: char| c.is_ascii_whitespace());
        let n = parser.parse(input)?;
        if n == input.len() && matches!(parser.state, State::Done) {
            *self = parser.finish();
            Ok(())
        } else {
            Err(n)
        }
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
    pub fn get_value(&self, key: &str) -> Option<AttributeValue<'_>> {
        if key == "class" {
            let mut value = AttributeValue::new();
            for (k, v) in &self.0 {
                if k.key() == Some("class") {
                    value.extend(&v.raw);
                }
            }
            if value.raw.is_empty() {
                None
            } else {
                Some(value)
            }
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
    ///         AttributeKind::Pair { key: "key1".into() },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some((
    ///         AttributeKind::Pair { key: "key2".into() },
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
    ///         AttributeKind::Pair { key: "key1".into() },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&(
    ///         AttributeKind::Pair { key: "key2".into() },
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
    ///         AttributeKind::Pair { key: "key1".into() },
    ///         AttributeValue::from("val1"),
    ///     )),
    /// );
    /// assert_eq!(
    ///     elems.next(),
    ///     Some(&mut (
    ///         AttributeKind::Pair { key: "key2".into() },
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
pub(crate) struct Validator {
    state: State,
}

impl Validator {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
        }
    }

    pub(crate) fn restart(&mut self) {
        self.state = State::Start;
    }

    /// Returns number of valid bytes parsed (0 means invalid) if finished, otherwise more input is
    /// needed.
    pub(crate) fn parse(&mut self, input: &str) -> Option<usize> {
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
pub(crate) struct Parser<'s> {
    attrs: Attributes<'s>,
    state: State,
}

impl<'s> Parser<'s> {
    pub(crate) fn new(attrs: Attributes<'s>) -> Self {
        Self {
            attrs,
            state: State::Start,
        }
    }

    pub(crate) fn parse(&mut self, input: &'s str) -> Result<usize, usize> {
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
                    Key => self.attrs.push((
                        AttributeKind::Pair {
                            key: content.into(),
                        },
                        "".into(),
                    )),
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
                    return Ok(pos + 1);
                }
            }
        }

        Ok(input.len())
    }

    pub(crate) fn finish(self) -> Attributes<'s> {
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

pub(crate) fn is_name(c: u8) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, b':' | b'_' | b'-')
}

#[cfg(test)]
mod test {
    #[test]
    fn valid_unicode() {
        let src = r#"{a="б"}"#;
        assert_eq!(super::valid(src), src.len());
    }

    #[test]
    fn valid_whitespace() {
        let src = "{ \n }";
        assert_eq!(super::valid(src), src.len());
    }
}
