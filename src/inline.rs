use crate::lex;
use crate::Span;

use lex::Delimiter;
use lex::Symbol;

use Atom::*;
use Container::*;
use NodeKind::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,
    OpenMarker, // ??
    Ellipses,
    ImageMarker, // ??
    EmDash,
    EnDash,
    Lt,
    Gt,
    Ampersand,
    Quote,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub kind: NodeKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeKind {
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
    //Mark,
    // smart quoting
    SingleQuoted,
    DoubleQuoted,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Enter(Container),
    Exit(Container),
    Atom(Atom),
    Node(Node),
}

#[derive(Debug, Clone, Copy)]
pub enum Dir {
    Open,
    Close,
    Both,
}

pub struct Parser<'s> {
    openers: Vec<Container>,
    close_containers: Option<usize>,
    next: Option<Event>,
    span: Span,

    lexer: std::iter::Peekable<lex::Lexer<'s>>,
}

impl<'s> Parser<'s> {
    pub fn new() -> Self {
        Self {
            openers: Vec::new(),
            close_containers: None,
            next: None,
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

    fn node(&self, kind: NodeKind) -> Event {
        Event::Node(Node {
            span: self.span,
            kind,
        })
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
        match first.kind {
            lex::Kind::Escape => Some(Event::Atom(Escape)),
            lex::Kind::Nbsp => Some(Event::Atom(Nbsp)),
            lex::Kind::Sym(lex::Symbol::Lt) => Some(Event::Atom(Lt)),
            lex::Kind::Sym(lex::Symbol::Gt) => Some(Event::Atom(Gt)),
            lex::Kind::Sym(lex::Symbol::Quote2) => Some(Event::Atom(Quote)),
            _ => None,
        }
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
            Event::Node(Node { kind, span })
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
            //lex::Kind::Open(Delimiter::BraceEqual) => Some((Mark, Dir::Open)),
            //lex::Kind::Close(Delimiter::BraceEqual) => Some((Mark, Dir::Close)),
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
        .and_then(|(cont, dir)| {
            if matches!(dir, Dir::Close | Dir::Both) && self.openers.contains(&cont) {
                self.close_containers = self.openers.iter().rposition(|o| *o == cont);
                Some(Event::Exit(self.openers.pop().unwrap()))
            } else if matches!(dir, Dir::Open | Dir::Both) {
                self.openers.push(cont);
                Some(Event::Enter(cont))
            } else {
                None
            }
        })
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().or_else(|| {
            self.close_containers
                .and_then(|i| {
                    if i < self.openers.len() {
                        Some(Event::Exit(self.openers.pop().unwrap()))
                    } else {
                        self.close_containers = None;
                        None
                    }
                })
                .or_else(|| {
                    let mut current = self.parse_event();

                    if let Some(Event::Node(Node { kind: Str, span })) = &mut current {
                        self.next = self.parse_event();
                        while let Some(Event::Node(Node { kind: Str, span: s })) = self.next {
                            *span = span.union(s);
                            self.next = self.parse_event();
                        }
                    }

                    current
                })
                .or_else(|| self.openers.pop().map(Event::Exit))
        })
    }
}

#[cfg(test)]
mod test {
    use crate::Span;

    use super::Atom::*;
    use super::Container::*;
    use super::Event::*;
    use super::NodeKind::*;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut p = super::Parser::new();
            p.parse($src);
            let actual = p.collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    impl super::NodeKind {
        pub fn span(self, start: usize, end: usize) -> super::Node {
            super::Node {
                span: Span::new(start, end),
                kind: self,
            }
        }
    }

    #[test]
    fn str() {
        test_parse!("abc", Node(Str.span(0, 3)));
        test_parse!("abc def", Node(Str.span(0, 7)));
    }

    #[test]
    fn verbatim() {
        test_parse!("`abc`", Node(Verbatim.span(1, 4)));
        test_parse!("`abc", Node(Verbatim.span(1, 4)));
        test_parse!("``abc``", Node(Verbatim.span(2, 5)));
        test_parse!("abc `def`", Node(Str.span(0, 4)), Node(Verbatim.span(5, 8)));
    }

    #[test]
    fn math() {
        test_parse!("$`abc`", Node(InlineMath.span(2, 5)));
        test_parse!("$$```abc", Node(DisplayMath.span(5, 8)));
    }

    #[test]
    fn container_basic() {
        test_parse!(
            "_abc_",
            Enter(Emphasis),
            Node(Str.span(1, 4)),
            Exit(Emphasis)
        );
        test_parse!(
            "{_abc_}",
            Enter(Emphasis),
            Node(Str.span(2, 5)),
            Exit(Emphasis)
        );
    }

    #[test]
    fn container_nest() {
        test_parse!(
            "{_{_abc_}_}",
            Enter(Emphasis),
            Enter(Emphasis),
            Node(Str.span(4, 7)),
            Exit(Emphasis),
            Exit(Emphasis)
        );
        test_parse!(
            "*_abc_*",
            Enter(Strong),
            Enter(Emphasis),
            Node(Str.span(2, 5)),
            Exit(Emphasis),
            Exit(Strong)
        );
    }

    #[test]
    fn container_unopened() {
        test_parse!("*}abc", Node(Str.span(0, 5)),);
    }

    #[test]
    fn container_close_parent() {
        test_parse!(
            "{*{_abc*}",
            Enter(Strong),
            Enter(Emphasis),
            Node(Str.span(4, 7)),
            Exit(Emphasis),
            Exit(Strong)
        );
    }

    #[test]
    fn container_close_block() {
        test_parse!(
            "{_abc",
            Enter(Emphasis),
            Node(Str.span(2, 5)),
            Exit(Emphasis)
        );
        test_parse!(
            "{_{*{_abc",
            Enter(Emphasis),
            Enter(Strong),
            Enter(Emphasis),
            Node(Str.span(6, 9)),
            Exit(Emphasis),
            Exit(Strong),
            Exit(Emphasis),
        );
    }
}
