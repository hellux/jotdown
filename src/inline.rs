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
    Start(Container),
    End(Container),
    Atom(Atom),
}

/*
#[derive(Debug)]
pub enum OpenerState {
    Unclosed,
    Closed,
    Discarded,
}
*/

#[derive(Debug)]
pub enum Dir {
    Open,
    Close,
    Both,
}

pub struct Parser {
    openers: Vec<Container>,
    events: Vec<Event>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            openers: Vec::new(),
            events: Vec::new(),
        }
    }

    pub fn parse<'a>(&'a mut self, src: &'a str) -> impl Iterator<Item = Event> + 'a {
        let mut lexer = lex::Lexer::new(src).peekable();
        std::iter::from_fn(move || {
            dbg!(&src);
            if self.events.is_empty() {
                Parse::new(&mut lexer, &mut self.openers, &mut self.events).parse();
            }

            self.events.pop()
        })
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

    /*
    fn step(&mut self) -> lex::Token {
        let token = self.lexer.next_token();
        dbg!(&token, self.pos);
        self.pos += token.len;
        std::mem::replace(&mut self.next_token, token)
    }

    fn eat(&mut self) -> lex::Kind {
        let end = self.pos;
        let token = self.step();
        self.span = Span::new(end - token.len, end);
        token.kind
    }

    fn peek(&mut self) -> &lex::Kind {
        &self.next_token.kind
    }
    */

    fn peek(&mut self) -> Option<&lex::Kind> {
        self.tokens.peek().map(|t| &t.kind)
    }

    fn parse(&mut self) {
        let mut t = if let Some(t) = self.tokens.next() {
            t
        } else {
            return;
        };

        //dbg!(&kind);

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

            if let Some((cont, ty)) = container_opt {
                if matches!(ty, Dir::Close | Dir::Both) && self.openers.contains(&cont) {
                    loop {
                        let c = self.openers.pop().unwrap();
                        self.events.push(Event::End(c));
                        if c == cont {
                            break;
                        }
                    }
                    return;
                } else if matches!(ty, Dir::Open | Dir::Both) {
                    self.openers.push(cont);
                    self.events.push(Event::Start(cont));
                }
                return;
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
    use super::Event::*;

    #[test]
    fn container_brace() {
        let mut p = super::Parser::new();
        assert_eq!(
            &[Atom(Str)],
            p.parse("{_hej_}").collect::<Vec<_>>().as_slice(),
        );
    }
}
