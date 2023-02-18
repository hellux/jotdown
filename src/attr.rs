use crate::CowStr;
use std::fmt;

pub(crate) fn parse(src: &str) -> Attributes {
    let mut a = Attributes::new();
    a.parse(src);
    a
}

pub fn valid<I: Iterator<Item = char>>(chars: I) -> (usize, bool) {
    use State::*;

    let mut has_attr = false;
    let mut n = 0;
    let mut state = Start;
    for c in chars {
        n += 1;
        state = state.step(c);
        match state {
            Class | Identifier | Value | ValueQuoted => has_attr = true,
            Done | Invalid => break,
            _ => {}
        }
    }

    if matches!(state, Done) {
        (n, has_attr)
    } else {
        (0, false)
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
#[allow(clippy::box_vec)]
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

    pub(crate) fn parse(&mut self, input: &'s str) -> bool {
        let mut parser = Parser::new(self, input);
        loop {
            match parser.step() {
                StepResult::Done => return true,
                StepResult::Invalid | StepResult::More => return false,
                StepResult::Valid => {}
            }
        }
    }

    /// Combine all attributes from both objects, prioritizing self on conflicts.
    pub(crate) fn union(&mut self, other: Self) {
        if let Some(attrs0) = &mut self.0 {
            if let Some(mut attrs1) = other.0 {
                for (key, val) in attrs1.drain(..) {
                    if !attrs0.iter().any(|(k, _)| *k == key) {
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
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };

        let attrs = self.0.as_mut().unwrap();
        if let Some(i) = attrs.iter().position(|(k, _)| *k == key) {
            let prev = &mut attrs[i].1;
            if key == "class" {
                *prev = format!("{} {}", prev, val).into();
            } else {
                *prev = val;
            }
        } else {
            attrs.push((key, val));
        }
    }

    fn insert_str(&mut self, key: &'s str, val: &'s str) -> usize {
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };

        let attrs = self.0.as_mut().unwrap();
        if let Some(i) = attrs.iter().position(|(k, _)| *k == key) {
            let prev = &mut attrs[i].1;
            if key == "class" {
                prev.extend(val);
            } else {
                *prev = val.into();
            }
            i
        } else {
            let i = attrs.len();
            attrs.push((key, val.into()));
            i
        }
    }

    fn append_str(&mut self, i: usize, val: &'s str) {
        self.0.as_mut().unwrap()[i].1.extend(val)
    }

    /// Returns true if the collection contains no attributes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.as_ref().map_or(true, |v| v.is_empty())
    }

    /// Returns a reference to the value corresponding to the attribute key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&AttributeValue<'s>> {
        self.iter().find(|(k, _)| *k == key).map(|(_, v)| v)
    }

    /// Returns an iterator over the attributes in undefined order.
    pub fn iter(&self) -> impl Iterator<Item = (&'s str, &AttributeValue<'s>)> + '_ {
        self.0.iter().flat_map(|v| v.iter().map(|(a, b)| (*a, b)))
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
        for (k, v) in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}=\"{}\"", k, v.raw)?;
        }
        write!(f, "}}")
    }
}

pub enum StepResult {
    /// Attributes are valid and completed.
    Done,
    /// Attributes are invalid.
    Invalid,
    /// Attributes are valid so far.
    Valid,
    /// Attributes are valid so far, more input is needed.
    More,
}

pub struct Parser<'a, 's> {
    input: &'s str,
    chars: std::str::Chars<'s>,
    attrs: &'a mut Attributes<'s>,
    i_last: usize,

    pos: usize,
    pos_prev: usize,
    state: State,
}

impl<'a, 's> Parser<'a, 's> {
    pub fn new(attrs: &'a mut Attributes<'s>, input: &'s str) -> Self {
        Self {
            input,
            chars: input.chars(),
            attrs,
            i_last: usize::MAX,
            pos: 0,
            pos_prev: 0,
            state: State::Start,
        }
    }

    pub fn restart(&mut self) {
        self.state = State::Start;
    }

    pub fn set_input(&mut self, input: &'s str) {
        debug_assert_eq!(self.chars.next(), None);
        self.input = input;
        self.chars = input.chars();
        self.pos = 0;
        self.pos_prev = 0;
    }

    pub fn step(&mut self) -> StepResult {
        self.chars.next().map_or(StepResult::More, |c| {
            use State::*;

            let state_next = self.state.step(c);
            let st = std::mem::replace(&mut self.state, state_next);

            if st != self.state && !matches!((st, self.state), (ValueEscape, _) | (_, ValueEscape))
            {
                let content = &self.input[self.pos_prev..self.pos];
                self.pos_prev = self.pos;
                match st {
                    Class => {
                        self.attrs.insert_str("class", content);
                    }
                    Identifier => {
                        self.attrs.insert_str("id", content);
                    }
                    Key => self.i_last = self.attrs.insert_str(content, ""),
                    Value | ValueQuoted | ValueContinued => self.attrs.append_str(
                        self.i_last,
                        &content[usize::from(matches!(st, ValueQuoted))..],
                    ),
                    _ => {}
                }
            };

            self.pos += c.len_utf8();

            match self.state {
                State::Done => StepResult::Done,
                State::Invalid => StepResult::Invalid,
                _ => StepResult::Valid,
            }
        })
    }

    pub fn len(&self) -> usize {
        self.input.len() - self.chars.as_str().len()
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
    fn step(self, c: char) -> State {
        use State::*;

        match self {
            Start if c == '{' => Whitespace,
            Start => Invalid,
            Whitespace => match c {
                '}' => Done,
                '.' => ClassFirst,
                '#' => IdentifierFirst,
                '%' => Comment,
                c if is_name(c) => Key,
                c if c.is_whitespace() => Whitespace,
                _ => Invalid,
            },
            Comment if c == '%' => Whitespace,
            Comment => Comment,
            ClassFirst if is_name(c) => Class,
            ClassFirst => Invalid,
            IdentifierFirst if is_name(c) => Identifier,
            IdentifierFirst => Invalid,
            s @ (Class | Identifier | Value) if is_name(c) => s,
            Class | Identifier | Value if c.is_whitespace() => Whitespace,
            Class | Identifier | Value if c == '}' => Done,
            Class | Identifier | Value => Invalid,
            Key if is_name(c) => Key,
            Key if c == '=' => ValueFirst,
            Key => Invalid,
            ValueFirst if is_name(c) => Value,
            ValueFirst if c == '"' => ValueQuoted,
            ValueFirst => Invalid,
            ValueQuoted | ValueNewline | ValueContinued if c == '"' => Whitespace,
            ValueQuoted | ValueNewline | ValueContinued | ValueEscape if c == '\n' => ValueNewline,
            ValueQuoted if c == '\\' => ValueEscape,
            ValueQuoted | ValueEscape => ValueQuoted,
            ValueNewline | ValueContinued => ValueContinued,
            Invalid | Done => panic!("{:?}", self),
        }
    }
}

pub fn is_name(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, ':' | '_' | '-')
}

#[cfg(test)]
mod test {
    macro_rules! test_attr {
        ($src:expr $(,$($av:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut attr = super::Attributes::new();
            attr.parse($src);
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
    fn unicode_whitespace() {
        test_attr!("{.a .b}", ("class", "a b"));
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
        test_attr!("{%%}");
        test_attr!("{ % abc % }");
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
        assert_eq!(super::valid(src.chars()), (src.len(), true));
    }

    #[test]
    fn valid_empty() {
        let src = "{}";
        assert_eq!(super::valid(src.chars()), (src.len(), false));
    }

    #[test]
    fn valid_whitespace() {
        let src = "{ \n }";
        assert_eq!(super::valid(src.chars()), (src.len(), false));
    }

    #[test]
    fn valid_comment() {
        let src = "{%comment%}";
        assert_eq!(super::valid(src.chars()), (src.len(), false));
    }

    #[test]
    fn valid_trailing() {
        let src = "{.class}";
        assert_eq!(
            super::valid(src.chars().chain("{.ignore}".chars())),
            (src.len(), true),
        );
    }

    #[test]
    fn valid_invalid() {
        assert_eq!(super::valid(" {.valid}".chars()), (0, false));
        assert_eq!(super::valid("{.class invalid}".chars()), (0, false));
        assert_eq!(super::valid("abc".chars()), (0, false));
        assert_eq!(super::valid("{.abc.}".chars()), (0, false));
    }
}
