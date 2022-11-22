use crate::lex;
use crate::Span;

use lex::Delimiter;
use lex::Symbol;

use Atom::*;
use Container::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Str,
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,
    OpenMarker, // ??
    Ellipses,
    ImageMarker, // ??
    EmDash,
    EnDash,
    FootnoteReference,
    Link,
    ReferenceLink,
    Emoji,
    RawFormat,
    // math
    DisplayMath,
    InlineMath,
    Verbatim,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Container {
    // attributes
    Attributes,
    Span,
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
    // URLs
    AutoUrl,
    Url,
    ImageText,
    LinkText,
    Reference,
    Destination,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Enter(Container),
    Exit(Container),
    Atom(Atom),
}

#[derive(Debug, Clone, Copy)]
pub enum Dir {
    Open,
    Close,
    Both,
}

pub struct Parser<'s> {
    openers: Vec<Container>,
    events: Vec<Event>,
    lexer: Option<std::iter::Peekable<lex::Lexer<'s>>>,
}

impl<'s> Parser<'s> {
    pub fn new() -> Self {
        Self {
            openers: Vec::new(),
            events: Vec::new(),
            lexer: None,
        }
    }

    pub fn parse(&mut self, src: &'s str) {
        self.lexer = Some(lex::Lexer::new(src).peekable());
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        if self.events.is_empty() {
            if let Some(lexer) = &mut self.lexer {
                Parse::new(lexer, &mut self.openers, &mut self.events).parse();
            }
        }

        self.events.pop()
    }
}

struct Parse<'l, 's, 'e> {
    tokens: &'l mut std::iter::Peekable<lex::Lexer<'s>>,
    openers: &'e mut Vec<Container>,
    events: &'e mut Vec<Event>,
}

impl<'l, 's, 'e> Parse<'l, 's, 'e> {
    fn new(
        tokens: &'l mut std::iter::Peekable<lex::Lexer<'s>>,
        openers: &'e mut Vec<Container>,
        events: &'e mut Vec<Event>,
    ) -> Self {
        Self {
            tokens,
            openers,
            events,
        }
    }

    fn peek(&mut self) -> Option<&lex::Kind> {
        self.tokens.peek().map(|t| &t.kind)
    }

    fn parse(&mut self) {
        let mut t = if let Some(t) = self.tokens.next() {
            t
        } else {
            return;
        };

        {
            let verbatim_opt = match t.kind {
                lex::Kind::Seq(lex::Sequence::Dollar) => {
                    let math_opt = (t.len <= 2)
                        .then(|| {
                            if let Some(lex::Kind::Seq(lex::Sequence::Backtick)) = self.peek() {
                                Some((DisplayMath, t.len))
                            } else {
                                None
                            }
                        })
                        .flatten();
                    if math_opt.is_some() {
                        self.tokens.next(); // backticks
                    }
                    math_opt
                }
                lex::Kind::Seq(lex::Sequence::Backtick) => Some((Verbatim, t.len)),
                _ => None,
            };

            if let Some((atom, opener_len)) = verbatim_opt {
                for tok in &mut self.tokens {
                    if matches!(tok.kind, lex::Kind::Seq(lex::Sequence::Backtick))
                        && tok.len == opener_len
                    {
                        self.events.push(Event::Atom(atom));
                        return;
                    }
                }
            }
        }

        {
            let container_opt = match t.kind {
                lex::Kind::Sym(Symbol::Asterisk) => Some((Strong, Dir::Both)),
                lex::Kind::Sym(Symbol::Underscore) => Some((Emphasis, Dir::Both)),
                lex::Kind::Sym(Symbol::Caret) => Some((Superscript, Dir::Both)),
                lex::Kind::Sym(Symbol::Tilde) => Some((Subscript, Dir::Both)),
                lex::Kind::Sym(Symbol::Quote1) => Some((SingleQuoted, Dir::Both)),
                lex::Kind::Sym(Symbol::Quote2) => Some((DoubleQuoted, Dir::Both)),
                lex::Kind::Open(Delimiter::Bracket) => Some((LinkText, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceAsterisk) => Some((Strong, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceCaret) => Some((Superscript, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceEqual) => Some((Mark, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceHyphen) => Some((Delete, Dir::Open)),
                lex::Kind::Open(Delimiter::BracePlus) => Some((Insert, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceTilde) => Some((Subscript, Dir::Open)),
                lex::Kind::Open(Delimiter::BraceUnderscore) => Some((Emphasis, Dir::Open)),
                lex::Kind::Close(Delimiter::Bracket) => Some((LinkText, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceAsterisk) => Some((Strong, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceCaret) => Some((Superscript, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceEqual) => Some((Mark, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceHyphen) => Some((Delete, Dir::Close)),
                lex::Kind::Close(Delimiter::BracePlus) => Some((Insert, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceTilde) => Some((Subscript, Dir::Close)),
                lex::Kind::Close(Delimiter::BraceUnderscore) => Some((Emphasis, Dir::Close)),
                _ => None,
            };

            if let Some((cont, dir)) = container_opt {
                if matches!(dir, Dir::Close | Dir::Both) && self.openers.contains(&cont) {
                    loop {
                        let c = self.openers.pop().unwrap();
                        self.events.push(Event::Exit(c));
                        if c == cont {
                            break;
                        }
                    }
                    return;
                } else if matches!(dir, Dir::Open | Dir::Both) {
                    self.openers.push(cont);
                    self.events.push(Event::Enter(cont));
                    return;
                }
            }
        }

        {
            if let lex::Kind::Open(Delimiter::Brace) = t.kind {
                todo!(); // check for attr
            }
        }

        if let Some(Event::Atom(Str)) = self.events.last() {
        } else {
            self.events.push(Event::Atom(Str));
        }
    }
}

#[cfg(test)]
mod test {
    use super::Atom::*;
    use super::Container::*;
    use super::Event::*;

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

    #[test]
    fn str() {
        test_parse!("abc", Atom(Str));
        test_parse!("abc def", Atom(Str));
    }

    #[test]
    fn container_brace() {
        test_parse!("{_abc_}", Enter(Emphasis), Atom(Str), Exit(Emphasis));
    }
}
