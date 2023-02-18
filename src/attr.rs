use crate::CowStr;
use crate::DiscontinuousString;
use crate::Span;

pub(crate) fn parse<'s, S: DiscontinuousString<'s>>(chars: S) -> Attributes<'s> {
    let mut a = Attributes::new();
    a.parse(chars);
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

/// A collection of attributes, i.e. a key-value map.
// Attributes are relatively rare, we choose to pay 8 bytes always and sometimes an extra
// indirection instead of always 24 bytes.
#[allow(clippy::box_vec)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, CowStr<'s>)>>>);

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

    pub(crate) fn parse<S: DiscontinuousString<'s>>(&mut self, input: S) -> bool {
        let mut p = Parser::new();
        let mut span_key = None;
        for c in input.chars() {
            if let Some((ty, sp)) = p.step(c) {
                match ty {
                    Event::Class => self.insert("class", input.src(sp)),
                    Event::Identifier => self.insert("id", input.src(sp)),
                    Event::Key => span_key = Some(sp),
                    Event::Value { continuation } => {
                        if continuation {
                            self.0.as_mut().unwrap().last_mut().unwrap().1 = format!(
                                "{} {}",
                                self.0.as_ref().unwrap().last().unwrap().1,
                                input.src(sp),
                            )
                            .into();
                        } else {
                            self.insert(
                                match input.src(span_key.take().unwrap()) {
                                    CowStr::Owned(_) => panic!(),
                                    CowStr::Borrowed(s) => s,
                                },
                                input.src(sp),
                            )
                        }
                    }
                }
            }
            if matches!(p.state, State::Done | State::Invalid) {
                break;
            }
        }
        matches!(p.state, State::Done)
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
    pub fn insert(&mut self, key: &'s str, val: CowStr<'s>) {
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

    /// Returns true if the collection contains no attributes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.as_ref().map_or(true, |v| v.is_empty())
    }

    /// Returns a reference to the value corresponding to the attribute key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.iter().find(|(k, _)| *k == key).map(|(_, v)| v)
    }

    /// Returns an iterator over the attributes in undefined order.
    pub fn iter(&self) -> impl Iterator<Item = (&'s str, &str)> + '_ {
        self.0
            .iter()
            .flat_map(|v| v.iter().map(|(a, b)| (*a, b.as_ref())))
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
                c if c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '-') => Key,
                c if c.is_whitespace() => Whitespace,
                _ => Invalid,
            },
            Comment if c == '%' => Whitespace,
            Comment => Comment,
            ClassFirst if is_name_start(c) => Class,
            ClassFirst => Invalid,
            IdentifierFirst if is_name_start(c) => Identifier,
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
            ValueQuoted | ValueNewline | ValueContinued if c == '\n' => ValueNewline,
            ValueQuoted => ValueQuoted,
            ValueNewline => ValueContinued,
            ValueContinued => ValueContinued,
            Invalid | Done => panic!("{:?}", self),
        }
    }
}

struct Parser {
    pos: usize,
    pos_prev: usize,
    state: State,
}

impl Parser {
    fn new() -> Self {
        Parser {
            pos: 0,
            pos_prev: 0,
            state: State::Start,
        }
    }

    fn step(&mut self, c: char) -> Option<(Event, Span)> {
        use State::*;

        let state_next = self.state.step(c);

        let elem = if self.state != state_next {
            let st = std::mem::replace(&mut self.state, state_next);
            let span = Span::new(self.pos_prev, self.pos);
            self.pos_prev = self.pos;
            match st {
                ClassFirst | IdentifierFirst | ValueFirst | ValueNewline | Comment | Start
                | Whitespace | Done | Invalid => None,
                Key => Some((Event::Key, span)),
                Class => Some((Event::Class, span)),
                Identifier => Some((Event::Identifier, span)),
                Value | ValueQuoted | ValueContinued => Some((
                    Event::Value {
                        continuation: matches!(st, ValueContinued),
                    },
                    span.skip(usize::from(matches!(st, ValueQuoted))),
                )),
            }
        } else {
            None
        };

        self.pos += c.len_utf8();

        elem
    }
}

pub fn is_name_start(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | ':')
}

pub fn is_name(c: char) -> bool {
    is_name_start(c) || c.is_ascii_digit() || matches!(c, '-')
}

enum Event {
    Class,
    Identifier,
    Key,
    Value { continuation: bool },
}

#[cfg(test)]
mod test {
    macro_rules! test_attr {
        ($src:expr $(,$($av:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut attr =super::Attributes::new();
            attr.parse($src);
            let actual = attr.iter().collect::<Vec<_>>();
            let expected = &[$($($av),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
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
