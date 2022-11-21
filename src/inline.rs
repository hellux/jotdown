use crate::lex;

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

#[derive(Debug)]
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
    //tree: tree::Builder<Container, Atom>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            openers: Vec::new(),
            events: Vec::new(),
        }
    }

    /*
    pub fn parse(mut self, src: &str) -> impl Iterator<Event> {
        todo!()
    }
    */
}

struct Parse<'s> {
    src: &'s str,
    lexer: lex::Lexer<'s>,
    events: &'s mut Vec<Event>,
}

impl<'s> Parse<'s> {
    fn new(src: &'s str, events: &'s mut Vec<Event>) -> Self {
        todo!()
    }

    /*
    fn parse(mut self, src: &str, evs: &mut Vec<Event>) {
        let mut chars = src.chars();
        while let Some(t) = chars.next() {
            {
                let verbatim_opt = match t.kind {
                    lex::Kind::Seq(lex::Sequence::Dollar) => {
                        let math_opt = (t.len <= 2)
                            .then(|| {
                                if let Some(lex::Token {
                                    kind: lex::Kind::Seq(lex::Sequence::Backtick),
                                    len,
                                }) = self.chars.clone().next()
                                {
                                    Some((DisplayMath, *len))
                                } else {
                                    None
                                }
                            })
                            .flatten();
                        if math_opt.is_some() {
                            chars.next(); // backticks
                        }
                        math_opt
                    }
                    lex::Kind::Seq(lex::Sequence::Backtick) => Some((Verbatim, t.len)),
                    _ => None,
                };

                if let Some((atom, opener_len)) = verbatim_opt {
                    for tok in chars {
                        if let lex::Kind::Seq(lex::Sequence::Backtick) = tok.kind {
                            if tok.len >= opener_len {
                                break;
                            }
                        }
                    }
                    evs.push(Event::Atom(atom));
                    return;
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
                            evs.push(Event::End(c));
                            if c == cont {
                                break;
                            }
                        }
                        return;
                    } else if matches!(ty, Dir::Open | Dir::Both) {
                        self.openers.push(cont);
                        evs.push(Event::Start(cont));
                    }
                    return;
                }
            }

            {
                if let lex::Kind::Open(Delimiter::Brace) = t.kind {
                    todo!(); // check for attr
                }
            }

            if let Some(Event::Atom(Str)) = evs.last() {
            } else {
                evs.push(Event::Atom(Str));
            }
        }
    }
*/
}

/*
impl<'s> Iterator for Parser<'s> {
    type Item = (Event<'s>, Span);

    fn next(&mut self) -> Option<Self::Item> {
        self.chars.next().map(|c| {
            match c {
                '*' => todo!(),
                '_' => todo!(),
                '^' => todo!(),
                '~' => todo!(),
                '\'' => todo!(),
                '"' => todo!(),
                '$' => todo!(),
                '<' => todo!(),
                '{' => todo!(),
                '[' => todo!(),
                _ =>
            }
        })
    }
}
*/

mod test {}
