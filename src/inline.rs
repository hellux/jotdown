use crate::lex;
use crate::Span;

use lex::Delimiter;
use lex::Symbol;

use Atom::*;
use Container::*;
use Node::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,
    OpenMarker, // ??
    Ellipsis,
    ImageMarker, // ??
    EmDash,
    EnDash,
    Lt,
    Gt,
    Ampersand,
    Quote,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Str,
    // link
    Url,
    ImageSource,
    LinkReference,
    FootnoteReference,
    // verbatim
    Verbatim,
    RawFormat,
    InlineMath,
    DisplayMath,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Container {
    Span,
    Attributes,
    // typesetting
    Subscript,
    Superscript,
    Insert,
    Delete,
    Emphasis,
    Strong,
    Mark,
    // smart quoting
    SingleQuoted,
    DoubleQuoted,
}

#[derive(Debug, PartialEq, Eq)]
pub enum EventKind {
    Enter(Container),
    Exit(Container),
    Atom(Atom),
    Node(Node),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub enum Dir {
    Open,
    Close,
    Both,
}

pub struct Parser<'s> {
    openers: Vec<(Container, usize)>,
    events: std::collections::VecDeque<Event>,
    span: Span,

    lexer: std::iter::Peekable<lex::Lexer<'s>>,
}

impl<'s> Parser<'s> {
    pub fn new() -> Self {
        Self {
            openers: Vec::new(),
            events: std::collections::VecDeque::new(),
            span: Span::new(0, 0),

            lexer: lex::Lexer::new("").peekable(),
        }
    }

    pub fn parse(&mut self, src: &'s str) {
        self.lexer = lex::Lexer::new(src).peekable();
    }

    fn eat(&mut self) -> Option<lex::Token> {
        let tok = self.lexer.next();
        if let Some(t) = &tok {
            self.span = self.span.extend(t.len);
        }
        tok
    }

    fn peek(&mut self) -> Option<&lex::Token> {
        self.lexer.peek()
    }

    fn reset_span(&mut self) {
        self.span = Span::empty_at(self.span.end());
    }

    fn node(&self, kind: Node) -> Event {
        Event {
            kind: EventKind::Node(kind),
            span: self.span,
        }
    }

    fn parse_event(&mut self) -> Option<Event> {
        self.reset_span();
        self.eat().map(|first| {
            self.parse_verbatim(&first)
                .or_else(|| self.parse_container(&first))
                .or_else(|| self.parse_atom(&first))
                .unwrap_or_else(|| self.node(Str))
        })
    }

    fn parse_atom(&mut self, first: &lex::Token) -> Option<Event> {
        let atom = match first.kind {
            lex::Kind::Escape => Escape,
            lex::Kind::Nbsp => Nbsp,
            lex::Kind::Sym(lex::Symbol::Lt) => Lt,
            lex::Kind::Sym(lex::Symbol::Gt) => Gt,
            lex::Kind::Sym(lex::Symbol::Quote2) => Quote,
            _ => return None,
        };

        Some(Event {
            kind: EventKind::Atom(atom),
            span: self.span,
        })
    }

    fn parse_verbatim(&mut self, first: &lex::Token) -> Option<Event> {
        match first.kind {
            lex::Kind::Seq(lex::Sequence::Dollar) => {
                let math_opt = (first.len <= 2)
                    .then(|| {
                        if let Some(lex::Token {
                            kind: lex::Kind::Seq(lex::Sequence::Backtick),
                            len,
                        }) = self.peek()
                        {
                            Some((
                                if first.len == 2 {
                                    DisplayMath
                                } else {
                                    InlineMath
                                },
                                *len,
                            ))
                        } else {
                            None
                        }
                    })
                    .flatten();
                if math_opt.is_some() {
                    self.eat(); // backticks
                }
                math_opt
            }
            lex::Kind::Seq(lex::Sequence::Backtick) => Some((Verbatim, first.len)),
            _ => None,
        }
        .map(|(kind, opener_len)| {
            let mut span = Span::empty_at(self.span.end());
            while let Some(tok) = self.eat() {
                if matches!(tok.kind, lex::Kind::Seq(lex::Sequence::Backtick))
                    && tok.len == opener_len
                {
                    break;
                }
                span = span.extend(tok.len);
            }
            Event {
                kind: EventKind::Node(kind),
                span,
            }
        })
    }

    fn parse_container(&mut self, first: &lex::Token) -> Option<Event> {
        match first.kind {
            lex::Kind::Sym(Symbol::Asterisk) => Some((Strong, Dir::Both)),
            lex::Kind::Sym(Symbol::Underscore) => Some((Emphasis, Dir::Both)),
            lex::Kind::Sym(Symbol::Caret) => Some((Superscript, Dir::Both)),
            lex::Kind::Sym(Symbol::Tilde) => Some((Subscript, Dir::Both)),
            lex::Kind::Sym(Symbol::Quote1) => Some((SingleQuoted, Dir::Both)),
            lex::Kind::Sym(Symbol::Quote2) => Some((DoubleQuoted, Dir::Both)),
            lex::Kind::Open(Delimiter::Bracket) => Some((Span, Dir::Open)),
            lex::Kind::Close(Delimiter::Bracket) => Some((Span, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceAsterisk) => Some((Strong, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceAsterisk) => Some((Strong, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceCaret) => Some((Superscript, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceCaret) => Some((Superscript, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceEqual) => Some((Mark, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceEqual) => Some((Mark, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceHyphen) => Some((Delete, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceHyphen) => Some((Delete, Dir::Close)),
            lex::Kind::Open(Delimiter::BracePlus) => Some((Insert, Dir::Open)),
            lex::Kind::Close(Delimiter::BracePlus) => Some((Insert, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceTilde) => Some((Subscript, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceTilde) => Some((Subscript, Dir::Close)),
            lex::Kind::Open(Delimiter::BraceUnderscore) => Some((Emphasis, Dir::Open)),
            lex::Kind::Close(Delimiter::BraceUnderscore) => Some((Emphasis, Dir::Close)),
            _ => None,
        }
        .map(|(cont, dir)| {
            self.openers
                .iter()
                .rposition(|(c, _)| *c == cont)
                .and_then(|o| {
                    matches!(dir, Dir::Close | Dir::Both).then(|| {
                        let (_, e) = &mut self.openers[o];
                        self.events[*e].kind = EventKind::Enter(cont);
                        self.openers.drain(o..);
                        EventKind::Exit(cont)
                    })
                })
                .unwrap_or_else(|| {
                    self.openers.push((cont, self.events.len()));
                    // use str for now, replace if closed later
                    EventKind::Node(Str)
                })
        })
        .map(|kind| Event {
            kind,
            span: self.span,
        })
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while self.events.is_empty()
            || !self.openers.is_empty()
            || self
                .events
                .back()
                .map_or(false, |ev| matches!(ev.kind, EventKind::Node(Str)))
        {
            if let Some(ev) = self.parse_event() {
                self.events.push_back(ev);
            } else {
                break;
            }
        }

        self.events.pop_front().map(|e| {
            if matches!(e.kind, EventKind::Node(Str)) {
                // merge str events
                let mut span = e.span;
                while self
                    .events
                    .front()
                    .map_or(false, |ev| matches!(ev.kind, EventKind::Node(Str)))
                {
                    span = span.union(self.events.pop_front().unwrap().span);
                }
                Event {
                    kind: EventKind::Node(Str),
                    span,
                }
            } else {
                e
            }
        })
    }
}

#[cfg(test)]
mod test {
    use crate::Span;

    use super::Atom::*;
    use super::Container::*;
    use super::EventKind::*;
    use super::Node::*;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut p = super::Parser::new();
            p.parse($src);
            let actual = p.map(|ev| (ev.kind, ev.span.of($src))).collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    impl super::EventKind {
        pub fn span(self, start: usize, end: usize) -> super::Event {
            super::Event {
                span: Span::new(start, end),
                kind: self,
            }
        }
    }

    #[test]
    fn str() {
        test_parse!("abc", (Node(Str), "abc"));
        test_parse!("abc def", (Node(Str), "abc def"));
    }

    #[test]
    fn verbatim() {
        test_parse!("`abc`", (Node(Verbatim), "abc"));
        test_parse!("`abc", (Node(Verbatim), "abc"));
        test_parse!("``abc``", (Node(Verbatim), "abc"));
        test_parse!("abc `def`", (Node(Str), "abc "), (Node(Verbatim), "def"));
    }

    #[test]
    fn math() {
        test_parse!("$`abc`", (Node(InlineMath), "abc"));
        test_parse!("$`abc` str", (Node(InlineMath), "abc"), (Node(Str), " str"));
        test_parse!("$$`abc`", (Node(DisplayMath), "abc"));
        test_parse!("$`abc", (Node(InlineMath), "abc"));
        test_parse!("$```abc```", (Node(InlineMath), "abc"),);
    }

    #[test]
    fn container_basic() {
        test_parse!(
            "_abc_",
            (Enter(Emphasis), "_"),
            (Node(Str), "abc"),
            (Exit(Emphasis), "_"),
        );
        test_parse!(
            "{_abc_}",
            (Enter(Emphasis), "{_"),
            (Node(Str), "abc"),
            (Exit(Emphasis), "_}"),
        );
    }

    #[test]
    fn container_nest() {
        test_parse!(
            "{_{_abc_}_}",
            (Enter(Emphasis), "{_"),
            (Enter(Emphasis), "{_"),
            (Node(Str), "abc"),
            (Exit(Emphasis), "_}"),
            (Exit(Emphasis), "_}"),
        );
        test_parse!(
            "*_abc_*",
            (Enter(Strong), "*"),
            (Enter(Emphasis), "_"),
            (Node(Str), "abc"),
            (Exit(Emphasis), "_"),
            (Exit(Strong), "*"),
        );
    }

    #[test]
    fn container_unopened() {
        test_parse!("*}abc", (Node(Str), "*}abc"));
    }

    #[test]
    fn container_close_parent() {
        test_parse!(
            "{*{_abc*}",
            (Enter(Strong), "{*"),
            (Node(Str), "{_abc"),
            (Exit(Strong), "*}"),
        );
    }

    #[test]
    fn container_close_block() {
        test_parse!("{_abc", (Node(Str), "{_abc"));
        test_parse!("{_{*{_abc", (Node(Str), "{_{*{_abc"));
    }
}
