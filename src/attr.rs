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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AttributeValue<'s> {
    raw: CowStr<'s>,
}

impl<'s> AttributeValue<'s> {
    /// Processes the attribute value escapes and returns an iterator of the parts of the value
    /// that should be displayed.
    pub fn parts(&'s self) -> AttributeValueParts<'s> {
        AttributeValueParts { ahead: &self.raw }
    }

    // lifetime is 's to avoid allocation if empty value is concatenated with single value
    fn extend(&mut self, s: &'s str) {
        match &mut self.raw {
            CowStr::Borrowed(prev) => {
                if prev.is_empty() {
                    *prev = s;
                } else {
                    self.raw = format!("{} {}", prev, s).into();
                }
            }
            CowStr::Owned(ref mut prev) => {
                prev.push(' ');
                prev.push_str(s);
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

impl<'s> From<String> for AttributeValue<'s> {
    fn from(value: String) -> Self {
        Self { raw: value.into() }
    }
}

impl<'s> fmt::Display for AttributeValue<'s> {
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

/// A collection of attributes, i.e. a key-value map.
// Attributes are relatively rare, we choose to pay 8 bytes always and sometimes an extra
// indirection instead of always 24 bytes.
#[allow(clippy::box_collection)]
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, AttributeValue<'s>)>>>);

impl<'s> Attributes<'s> {
    /// Create an empty collection.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub(crate) fn take(&mut self) -> Self {
        Self(self.0.take())
    }

    /// Parse and append attributes.
    pub(crate) fn parse(&mut self, input: &'s str) -> Result<(), usize> {
        let mut parser = Parser::new(self.take());
        parser.parse(input)?;
        *self = parser.finish();
        Ok(())
    }

    /// Combine all attributes from both objects, prioritizing self on conflicts.
    pub(crate) fn union(&mut self, other: Self) {
        if let Some(attrs0) = &mut self.0 {
            if let Some(mut attrs1) = other.0 {
                for (key, val) in attrs1.drain(..) {
                    if key == "class" || !attrs0.iter().any(|(k, _)| *k == key) {
                        attrs0.push((key, val));
                    }
                }
            }
        } else {
            self.0 = other.0;
        }
    }

    /// Insert an attribute. If the attribute already exists, the previous value will be
    /// overwritten, unless it is a "class" attribute. In that case the provided value will be
    /// appended to the existing value.
    pub fn insert(&mut self, key: &'s str, val: AttributeValue<'s>) {
        self.insert_pos(key, val);
    }

    // duplicate of insert but returns position of inserted value
    fn insert_pos(&mut self, key: &'s str, val: AttributeValue<'s>) -> usize {
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };

        let attrs = self.0.as_mut().unwrap();
        if let Some(i) = attrs.iter().position(|(k, _)| *k == key) {
            let prev = &mut attrs[i].1;
            if key == "class" {
                match val.raw {
                    CowStr::Borrowed(s) => prev.extend(s),
                    CowStr::Owned(s) => {
                        *prev = format!("{} {}", prev, s).into();
                    }
                }
            } else {
                *prev = val;
            }
            i
        } else {
            let i = attrs.len();
            attrs.push((key, val));
            i
        }
    }

    /// Returns true if the collection contains no attributes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.as_ref().map_or(true, |v| v.is_empty())
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |v| v.len())
    }

    /// Returns a reference to the value corresponding to the attribute key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&AttributeValue> {
        self.iter().find(|(k, _)| *k == key).map(|(_, v)| v)
    }

    /// Returns a mutable reference to the value corresponding to the attribute key.
    pub fn get_mut(&'s mut self, key: &str) -> Option<&mut AttributeValue> {
        self.iter_mut().find(|(k, _)| *k == key).map(|(_, v)| v)
    }

    /// Returns an iterator over references to the attribute keys and values in undefined order.
    pub fn iter(&self) -> AttributesIter {
        self.into_iter()
    }

    /// Returns an iterator over mutable references to the attribute keys and values in undefined order.
    pub fn iter_mut<'i>(&'i mut self) -> AttributesIterMut<'i, 's> {
        self.into_iter()
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
    /// # use jotdown::Attributes;
    /// let mut a = Attributes::try_from("{.a}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some(("class", "a".into())));
    /// assert_eq!(a.next(), None);
    /// ```
    ///
    /// Multiple sets can be parsed if they immediately follow the each other:
    ///
    /// ```
    /// # use jotdown::Attributes;
    /// let mut a = Attributes::try_from("{.a}{.b}").unwrap().into_iter();
    /// assert_eq!(a.next(), Some(("class", "a b".into())));
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

#[cfg(test)]
impl<'s> FromIterator<(&'s str, &'s str)> for Attributes<'s> {
    fn from_iter<I: IntoIterator<Item = (&'s str, &'s str)>>(iter: I) -> Self {
        let attrs = iter
            .into_iter()
            .map(|(a, v)| (a, v.into()))
            .collect::<Vec<_>>();
        if attrs.is_empty() {
            Attributes::new()
        } else {
            Attributes(Some(attrs.into()))
        }
    }
}

impl<'s> std::fmt::Debug for Attributes<'s> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in self {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}=\"{}\"", k, v.raw)?;
        }
        write!(f, "}}")
    }
}

/// Iterator over [Attributes] key-value pairs, in arbitrary order.
pub struct AttributesIntoIter<'s>(std::vec::IntoIter<(&'s str, AttributeValue<'s>)>);

impl<'s> Iterator for AttributesIntoIter<'s> {
    type Item = (&'s str, AttributeValue<'s>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'s> IntoIterator for Attributes<'s> {
    type Item = (&'s str, AttributeValue<'s>);

    type IntoIter = AttributesIntoIter<'s>;

    fn into_iter(self) -> Self::IntoIter {
        AttributesIntoIter(self.0.map_or(vec![].into_iter(), |b| (*b).into_iter()))
    }
}

/// Iterator over references to [Attributes] key-value pairs, in arbitrary order.
pub struct AttributesIter<'i, 's>(std::slice::Iter<'i, (&'s str, AttributeValue<'s>)>);

impl<'i, 's> Iterator for AttributesIter<'i, 's> {
    type Item = (&'s str, &'i AttributeValue<'s>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(move |(k, v)| (*k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'i, 's> IntoIterator for &'i Attributes<'s> {
    type Item = (&'s str, &'i AttributeValue<'s>);

    type IntoIter = AttributesIter<'i, 's>;

    fn into_iter(self) -> Self::IntoIter {
        let sl = self.0.as_ref().map_or(&[][..], |a| a.as_slice());
        AttributesIter(sl.iter())
    }
}

/// Iterator over mutable references to [Attributes] key-value pairs, in arbitrary order.
pub struct AttributesIterMut<'i, 's>(std::slice::IterMut<'i, (&'s str, AttributeValue<'s>)>);

impl<'i, 's> Iterator for AttributesIterMut<'i, 's> {
    type Item = (&'s str, &'i mut AttributeValue<'s>);

    fn next(&mut self) -> Option<Self::Item> {
        // this map splits &(&k, v) into (&&k, &v)
        self.0.next().map(|(k, v)| (*k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'i, 's> IntoIterator for &'i mut Attributes<'s> {
    type Item = (&'s str, &'i mut AttributeValue<'s>);

    type IntoIter = AttributesIterMut<'i, 's>;

    fn into_iter(self) -> Self::IntoIter {
        let sl = self.0.as_mut().map_or(&mut [][..], |a| a.as_mut());
        AttributesIterMut(sl.iter_mut())
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
    i_prev: usize,
    state: State,
}

impl<'s> Parser<'s> {
    pub fn new(attrs: Attributes<'s>) -> Self {
        Self {
            attrs,
            i_prev: usize::MAX,
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
                    Class => self.attrs.insert("class", content.into()),
                    Identifier => self.attrs.insert("id", content.into()),
                    Key => self.i_prev = self.attrs.insert_pos(content, "".into()),
                    Value | ValueQuoted | ValueContinued => {
                        self.attrs.0.as_mut().unwrap()[self.i_prev]
                            .1
                            .extend(&content[usize::from(matches!(st, ValueQuoted))..]);
                    }
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
    Comment,
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
                b'%' => Comment,
                c if is_name(c) => Key,
                c if c.is_ascii_whitespace() => Whitespace,
                _ => Invalid,
            },
            Comment if c == b'%' => Whitespace,
            Comment if c == b'}' => Done,
            Comment => Comment,
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
    use super::*;

    macro_rules! test_attr {
        ($src:expr $(,$($av:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut attr = Attributes::try_from($src).unwrap();
            let actual = attr.iter().collect::<Vec<_>>();
            let expected = &[$($($av),*,)?];
            for i in 0..actual.len() {
                let actual_val = format!("{}", actual[i].1);
                assert_eq!((actual[i].0, actual_val.as_str()), expected[i], "\n\n{}\n\n", $src);
            }
        };
    }

    #[test]
    fn empty() {
        test_attr!("{}");
    }

    #[test]
    fn class_id() {
        test_attr!(
            "{.some_class #some_id}",
            ("class", "some_class"),
            ("id", "some_id"),
        );
        test_attr!("{.a .b}", ("class", "a b"));
        test_attr!("{#a #b}", ("id", "b"));
    }

    #[test]
    fn value_unquoted() {
        test_attr!(
            "{attr0=val0 attr1=val1}",
            ("attr0", "val0"),
            ("attr1", "val1"),
        );
    }

    #[test]
    fn value_quoted() {
        test_attr!(
            r#"{attr0="val0" attr1="val1"}"#,
            ("attr0", "val0"),
            ("attr1", "val1"),
        );
        test_attr!(
            r#"{#id .class style="color:red"}"#,
            ("id", "id"),
            ("class", "class"),
            ("style", "color:red")
        );
    }

    #[test]
    fn value_newline() {
        test_attr!("{attr0=\"abc\ndef\"}", ("attr0", "abc def"));
    }

    #[test]
    fn comment() {
        test_attr!("{%}");
        test_attr!("{%%}");
        test_attr!("{ % abc % }");
        test_attr!("{ .some_class % #some_id }", ("class", "some_class"));
        test_attr!(
            "{ .some_class % abc % #some_id}",
            ("class", "some_class"),
            ("id", "some_id"),
        );
    }

    #[test]
    fn escape() {
        test_attr!(
            r#"{attr="with escaped \~ char"}"#,
            ("attr", "with escaped ~ char")
        );
        test_attr!(
            r#"{key="quotes \" should be escaped"}"#,
            ("key", r#"quotes " should be escaped"#)
        );
    }

    #[test]
    fn escape_backslash() {
        test_attr!(r#"{attr="with\\backslash"}"#, ("attr", r"with\backslash"));
        test_attr!(
            r#"{attr="with many backslashes\\\\"}"#,
            ("attr", r"with many backslashes\\")
        );
        test_attr!(
            r#"{attr="\\escaped backslash at start"}"#,
            ("attr", r"\escaped backslash at start")
        );
    }

    #[test]
    fn only_escape_punctuation() {
        test_attr!(r#"{attr="do not \escape"}"#, ("attr", r"do not \escape"));
        test_attr!(
            r#"{attr="\backslash at the beginning"}"#,
            ("attr", r"\backslash at the beginning")
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

    fn make_attrs<'a>(v: Vec<(&'a str, &'a str)>) -> Attributes<'a> {
        v.into_iter().collect()
    }

    #[test]
    fn can_iter() {
        let attrs = make_attrs(vec![("key1", "val1"), ("key2", "val2")]);
        let as_vec = attrs.iter().collect::<Vec<_>>();
        assert_eq!(
            as_vec,
            vec![
                ("key1", &AttributeValue::from("val1")),
                ("key2", &AttributeValue::from("val2")),
            ]
        );
    }

    #[test]
    fn can_iter_mut() {
        let mut attrs = make_attrs(vec![("key1", "val1"), ("key2", "val2")]);
        let as_vec = attrs.iter_mut().collect::<Vec<_>>();
        assert_eq!(
            as_vec,
            vec![
                ("key1", &mut AttributeValue::from("val1")),
                ("key2", &mut AttributeValue::from("val2")),
            ]
        );
    }

    #[test]
    fn iter_after_iter_mut() {
        let mut attrs: Attributes = make_attrs(vec![("key1", "val1"), ("key2", "val2")]);

        for (attr, value) in &mut attrs {
            if attr == "key2" {
                *value = "new_val".into();
            }
        }

        assert_eq!(
            attrs.iter().collect::<Vec<_>>(),
            vec![
                ("key1", &AttributeValue::from("val1")),
                ("key2", &AttributeValue::from("new_val")),
            ]
        );
    }
}
