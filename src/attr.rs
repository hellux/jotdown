use crate::CowStr;
use crate::DiscontinuousString;
use crate::Span;

use State::*;

pub(crate) fn parse<'s, S: DiscontinuousString<'s>>(chars: S) -> Attributes<'s> {
    let mut a = Attributes::new();
    a.parse(chars);
    a
}

pub fn valid<I: Iterator<Item = char>>(chars: I) -> (usize, bool) {
    let mut has_attr = false;
    let mut p = Parser::new(chars);
    for e in &mut p {
        match e {
            Element::Class(..) | Element::Identifier(..) | Element::Attribute(..) => {
                has_attr = true;
            }
            Element::Invalid => return (0, false),
        }
    }
    (p.pos, has_attr)
}

// Attributes are relatively rare, we choose to pay 8 bytes always and sometimes an extra
// indirection instead of always 24 bytes.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, CowStr<'s>)>>>);

impl<'s> Attributes<'s> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn take(&mut self) -> Self {
        Self(self.0.take())
    }

    pub(crate) fn parse<S: DiscontinuousString<'s>>(&mut self, input: S) -> bool {
        for elem in Parser::new(input.chars()) {
            match elem {
                Element::Class(c) => self.add("class", input.src(c)),
                Element::Identifier(i) => self.add("id", input.src(i)),
                Element::Attribute(a, v) => self.add(
                    match input.src(a) {
                        CowStr::Owned(_) => panic!(),
                        CowStr::Borrowed(s) => s,
                    },
                    input.src(v),
                ),
                Element::Invalid => return false,
            }
        }
        true
    }

    /// Combine all attributes from both objects, prioritizing self on conflicts.
    pub fn union(&mut self, other: Self) {
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

    fn add(&mut self, attr: &'s str, val: CowStr<'s>) {
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };

        let attrs = self.0.as_mut().unwrap();
        if let Some(i) = attrs.iter().position(|(a, _)| *a == attr) {
            let prev = &mut attrs[i].1;
            if attr == "class" {
                *prev = format!("{} {}", prev, val).into();
            } else {
                *prev = val;
            }
        } else {
            attrs.push((attr, val));
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        if let Some(v) = &self.0 {
            v.is_empty()
        } else {
            true
        }
    }

    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.iter().find(|(k, _)| *k == key).map(|(_, v)| v)
    }

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
    Attribute,
    ValueFirst,
    Value,
    ValueQuoted,
    Done,
    Invalid,
}

struct Parser<I> {
    chars: I,
    pos: usize,
    state: State,
}

impl<I: Iterator<Item = char>> Parser<I> {
    fn new(chars: I) -> Self {
        Parser {
            chars,
            pos: 0,
            state: Start,
        }
    }

    fn step_char(&mut self) -> Option<State> {
        self.chars.next().map(|c| {
            self.pos += c.len_utf8();
            match self.state {
                Start => match c {
                    '{' => Whitespace,
                    _ => Invalid,
                },
                Whitespace => match c {
                    '}' => Done,
                    '.' => ClassFirst,
                    '#' => IdentifierFirst,
                    '%' => Comment,
                    c if c.is_ascii_alphanumeric() || matches!(c, '_' | ':' | '-') => Attribute,
                    c if c.is_whitespace() => Whitespace,
                    _ => Invalid,
                },
                Comment => {
                    if c == '%' {
                        Whitespace
                    } else {
                        Comment
                    }
                }
                s @ (ClassFirst | IdentifierFirst) => {
                    if is_name_start(c) {
                        match s {
                            ClassFirst => Class,
                            IdentifierFirst => Identifier,
                            _ => panic!(),
                        }
                    } else {
                        Invalid
                    }
                }
                s @ (Class | Identifier | Value) => {
                    if is_name(c) {
                        s
                    } else if c.is_whitespace() {
                        Whitespace
                    } else if c == '}' {
                        Done
                    } else {
                        Invalid
                    }
                }
                Attribute => {
                    if is_name(c) {
                        Attribute
                    } else if c == '=' {
                        ValueFirst
                    } else {
                        Invalid
                    }
                }
                ValueFirst => {
                    if is_name(c) {
                        Value
                    } else if c == '"' {
                        ValueQuoted
                    } else {
                        Invalid
                    }
                }
                ValueQuoted => {
                    if c == '"' {
                        Whitespace
                    } else {
                        ValueQuoted
                    }
                }
                Invalid | Done => panic!("{:?}", self.state),
            }
        })
    }

    fn step(&mut self) -> (State, Span) {
        let start = self.pos.saturating_sub(1);

        if self.state == Done {
            return (Done, Span::empty_at(start));
        }

        if self.state == Invalid {
            return (Invalid, Span::empty_at(start));
        }

        while let Some(state_next) = self.step_char() {
            if self.state != state_next {
                return (
                    std::mem::replace(&mut self.state, state_next),
                    Span::new(start, self.pos - 1),
                );
            }
        }

        (
            if self.state == Done { Done } else { Invalid },
            Span::new(start, self.pos.saturating_sub(1)),
        )
    }
}

fn is_name_start(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | ':')
}

fn is_name(c: char) -> bool {
    is_name_start(c) || c.is_ascii_digit() || matches!(c, '-')
}

enum Element {
    Class(Span),
    Identifier(Span),
    Attribute(Span, Span),
    Invalid,
}

impl<I: Iterator<Item = char>> Iterator for Parser<I> {
    type Item = Element;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (st, span0) = self.step();
            return match st {
                ClassFirst | IdentifierFirst => {
                    let (st, span1) = self.step();
                    Some(match st {
                        Class => Element::Class(span1),
                        Identifier => Element::Identifier(span1),
                        _ => return Some(Element::Invalid),
                    })
                }
                Attribute => {
                    let (st, _span1) = self.step();
                    match st {
                        ValueFirst => {
                            let (st, span2) = self.step();
                            match st {
                                Value => Some(Element::Attribute(span0, span2)),
                                ValueQuoted => Some(Element::Attribute(span0, span2.skip(1))),
                                Invalid => Some(Element::Invalid),
                                _ => panic!("{:?}", st),
                            }
                        }
                        Invalid => Some(Element::Invalid),
                        _ => panic!("{:?}", st),
                    }
                }
                Comment | Start | Whitespace => continue,
                Done => None,
                Invalid => Some(Element::Invalid),
                _ => panic!("{:?}", st),
            };
        }
    }
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
