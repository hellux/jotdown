use crate::Span;

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

// class: slice starts on first key=class, emits all values followed by a key=class,
// other: slice starts on the last key=key, only emits the immediately following values
#[derive(Debug)]
pub struct ValueRef<'a, 's>(&'a [(Element, &'s str)]);

impl<'a, 's> std::fmt::Display for ValueRef<'a, 's> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = self.parts();
        write!(f, "{}", parts.next().unwrap())?;
        parts.try_for_each(|p| write!(f, " {}", p))
    }
}

impl<'a, 's> ValueRef<'a, 's> {
    /// Return all separated parts of a value. A value may be separated due to a line break or in
    /// case of "class" values due to concatenation.
    pub fn parts(&self) -> impl Iterator<Item = &'s str> + 'a {
        let mut elems = self.0.iter();

        let key0 = elems.next().unwrap().1;
        let concatenate = matches!(key0, "class");

        let mut done = false;
        std::iter::from_fn(move || {
            if !done {
                while let Some((e, s)) = elems.next() {
                    match e {
                        Element::Key => {
                            if *s != "class" {
                                elems.find(|e| matches!(e, (Element::Key, "class")));
                            }
                        }
                        Element::Value { closed } => {
                            if *closed && !concatenate {
                                done = true;
                            }
                            return Some(*s);
                        }
                    }
                }
                done = true;
            }
            None
        })
    }
}

/// A collection of attributes, i.e. a key-value map.
// Attributes are relatively rare, we choose to pay 8 bytes always and sometimes an extra
// indirection instead of always 24 bytes.
#[allow(clippy::box_vec)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Attributes<'s>(Option<Box<Vec<(Element, &'s str)>>>);

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
        let mut p = Parser::new();
        for c in input.chars() {
            if let Some((ev, sp)) = p.step(c) {
                self.push_event(ev, sp.of(input));
            }
            if matches!(p.state, State::Done | State::Invalid) {
                break;
            }
        }
        matches!(p.state, State::Done)
    }

    fn push_event(&mut self, ev: Event, s: &'s str) {
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };
        let elems = &mut self.0.as_mut().unwrap();
        match ev {
            Event::Class => {
                elems.push((Element::Key, "class"));
                elems.push((Element::Value { closed: true }, s));
            }
            Event::Identifier => {
                elems.push((Element::Key, "id"));
                elems.push((Element::Value { closed: true }, s));
            }
            Event::Key => elems.push((Element::Key, s)),
            Event::Value { closed } => elems.push((Element::Value { closed }, s)),
        }
    }

    /// Append all attributes from another collection of attributes.
    pub(crate) fn append(&mut self, mut other: Self) {
        if let Some(attrs0) = &mut self.0 {
            if let Some(attrs1) = &mut other.0 {
                for (elem, val) in attrs1.drain(..) {
                    attrs0.push((elem, val));
                }
            }
        }
    }

    /// Prepend all attributes from another collection of attributes.
    pub(crate) fn prepend(&mut self, mut other: Self) {
        other.append(self.take());
        self.0 = other.0;
    }

    /// Push an attribute.
    pub fn push(&mut self, key: &'s str, val: &'s str) {
        if self.0.is_none() {
            self.0 = Some(Vec::new().into());
        };
        let elems = &mut self.0.as_mut().unwrap();
        elems.push((Element::Key, key));
        elems.push((Element::Value { closed: true }, val));
    }

    /// Returns true if the collection contains no attributes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.as_ref().map_or(true, |v| v.is_empty())
    }

    /// Returns a reference to the value corresponding to the attribute key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<ValueRef> {
        if key == "class" {
            self.0.as_ref().and_then(|elems| {
                elems
                    .as_ref()
                    .iter()
                    .position(|(e, v)| matches!(e, Element::Key) && *v == "class")
                    .map(|i| ValueRef(&elems[i..]))
            })
        } else {
            self.0.as_ref().and_then(|elems| {
                elems
                    .as_ref()
                    .iter()
                    .rposition(|(e, v)| matches!(e, Element::Key) && *v == key)
                    .map(|i| ValueRef(&elems[i..]))
            })
        }
    }

    /// Return an iterator over each unique key in the collection of attributes.
    pub fn keys(&self) -> impl Iterator<Item = &str> + '_ {
        let mut i = 0;
        std::iter::from_fn(move || {
            self.0.as_ref().and_then(|elems| {
                while let Some((e, v)) = elems.get(i) {
                    let unique_key = matches!(e, Element::Key)
                        && !elems
                            .iter()
                            .take(i)
                            .any(|e| matches!(e, (Element::Key, key) if key == v));
                    i += 1;
                    if unique_key {
                        return Some(*v);
                    }
                }
                None
            })
        })
    }

    /// Returns an iterator over the attributes in undefined order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, ValueRef)> {
        self.keys().map(|k| (k, self.get(k).unwrap()))
    }
}

#[cfg(test)]
impl<'s> FromIterator<(&'s str, &'s str)> for Attributes<'s> {
    fn from_iter<I: IntoIterator<Item = (&'s str, &'s str)>>(iter: I) -> Self {
        let mut attrs = Attributes::new();
        for (k, v) in iter {
            attrs.push(k, v.into());
        }
        attrs
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

pub struct Builder<'s> {
    input: &'s str,
    chars: std::str::Chars<'s>,
    attrs: Attributes<'s>,
    parser: Parser,
    checkpoint_events: usize,
}

impl<'s> Builder<'s> {
    pub fn new(input: &'s str) -> Self {
        Self {
            input,
            chars: input.chars(),
            attrs: Attributes::new(),
            parser: Parser {
                pos: 0,
                pos_prev: 0,
                state: State::Start,
            },
            checkpoint_events: 0,
        }
    }

    pub fn restart(&mut self) {
        self.parser.state = State::Start;
    }

    pub fn set_input(&mut self, input: &'s str) {
        debug_assert_eq!(self.chars.next(), None);
        self.input = input;
        self.chars = input.chars();
        self.parser.pos = 0;
        self.parser.pos_prev = 0;
    }

    pub fn step(&mut self) -> StepResult {
        if let Some(c) = self.chars.next() {
            if let Some((ev, sp)) = self.parser.step(c) {
                self.attrs.push_event(ev, sp.of(self.input));
            }
            match self.parser.state {
                State::Done => {
                    if let Some(elems) = self.attrs.0.as_ref() {
                        self.checkpoint_events = elems.len();
                    }
                    StepResult::Done
                }
                State::Invalid => StepResult::Invalid,
                _ => StepResult::Valid,
            }
        } else {
            StepResult::More
        }
    }

    pub fn len(&self) -> usize {
        self.input.len() - self.chars.as_str().len()
    }

    pub fn finish(mut self) -> Attributes<'s> {
        if let Some(elems) = self.attrs.0.as_mut() {
            debug_assert_ne!(elems.len(), 0);
            elems.drain(self.checkpoint_events..);
        }
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
                        closed: !matches!(self.state, ValueNewline),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Element {
    Key,
    Value { closed: bool },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event {
    Class,
    Identifier,
    Key,
    Value { closed: bool },
}

#[cfg(test)]
mod test {
    macro_rules! test_attr {
        ($src:expr $(,$(($key:expr, $val:expr)),* $(,)?)?) => {
            #[allow(unused)]
            let mut attr =super::Attributes::new();
            attr.parse($src);
            let actual = attr.iter().map(|(k, v)| (k, v.to_string())).collect::<Vec<_>>();
            let expected = &[$($(($key, $val.into())),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn parse_empty() {
        test_attr!("{}");
    }

    #[test]
    fn parse_class_id() {
        test_attr!(
            "{.some_class #some_id}",
            ("class", "some_class"),
            ("id", "some_id"),
        );
        test_attr!("{.a .b}", ("class", "a b"));
        test_attr!("{#a #b}", ("id", "b"));
    }

    #[test]
    fn parse_unicode_whitespace() {
        test_attr!("{.a .b}", ("class", "a b"));
    }

    #[test]
    fn parse_value_unquoted() {
        test_attr!(
            "{attr0=val0 attr1=val1}",
            ("attr0", "val0"),
            ("attr1", "val1"),
        );
    }

    #[test]
    fn parse_value_quoted() {
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
    fn parse_value_newline() {
        test_attr!("{attr0=\"abc\ndef\"}", ("attr0", "abc def"));
    }

    #[test]
    fn parse_comment() {
        test_attr!("{%%}");
        test_attr!("{ % abc % }");
        test_attr!(
            "{ .some_class % abc % #some_id}",
            ("class", "some_class"),
            ("id", "some_id"),
        );
    }

    macro_rules! test_value {
        ($src:expr, $key:expr, $expected:expr) => {
            #[allow(unused)]
            let mut attr = super::Attributes::new();
            attr.parse($src);
            let actual = attr.get($key).unwrap().to_string();
            assert_eq!(actual, $expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn value_id() {
        test_value!("{#a #b #c .cls}", "id", "c");
    }

    #[test]
    fn value_class() {
        test_value!("{.a .b .c}", "class", "a b c");
        test_value!("{.a .b #id .c}", "class", "a b c");
        test_value!("{.a class=def .b .c}", "class", "a def b c");
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
