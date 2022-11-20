use crate::Span;

use crate::tree;
use crate::CowStr;

use Atom::*;
use Container::*;

pub type Tree<'s> = tree::Tree<Container, Atom<'s>>;

/*
pub fn parse<'s, I: Iterator<Item = Span>>(src: &'s str, inlines: I) -> Vec<Event<'s>> {
    Parser::new(src).parse(inlines)
}
*/

pub enum Inline<'s> {
    Atom(Atom<'s>),
    Container(Container),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom<'s> {
    Str,
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,        // ??
    OpenMarker,  // ??
    Ellipses,    // ??
    ImageMarker, // ??
    EmDash,      // ??
    FootnoteReference { label: CowStr<'s> },
    ExplicitLink { label: CowStr<'s> },
    ReferenceLink { label: CowStr<'s> },
    Emoji { name: CowStr<'s> },
    RawFormat { format: CowStr<'s> },
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
    Emph,
    Strong,
    Mark,
    Verbatim,
    // smart quoting
    SingleQuoted,
    DoubleQuoted,
    // math
    DisplayMath,
    InlineMath,
    // URLs
    Email,
    Url,
    ImageText,
    LinkText,
    Reference,
    Destination,
}

#[derive(Debug)]
pub enum Event<'s> {
    Start(Container, OpenerState),
    End(Container),
    Atom(Atom<'s>),
}

#[derive(Debug)]
pub enum OpenerState {
    Unclosed,
    Closed,
    Discarded,
}

#[derive(Debug)]
pub enum ContainerType {
    Opener,
    Closer,
    Both,
}

pub struct Parser<'s, I: Iterator<Item = char>> {
    chars: std::iter::Peekable<I>,
    openers: Vec<(Container, usize)>,
    events: Vec<Event<'s>>,
    //tree: tree::Builder<Container, Atom>,
}

impl<'s, I: Iterator<Item = char>> Parser<'s, I> {
    pub fn new(chars: I) -> Self {
        Self {
            chars: chars.peekable(),
            openers: Vec::new(),
            events: Vec::new(),
        }
    }

    /*
    fn step(&mut self) -> lex::Token {
        let token = lex::Lexer::new(&self.src[self.pos..]).next_token();
        self.pos += token.len;
        std::mem::replace(&mut self.next_token, token)
    }

    fn eat(&mut self) -> lex::TokenKind {
        loop {
            let end = self.pos;
            let token = self.step();
            if !matches!(token.kind, lex::TokenKind::Whitespace) {
                self.span = Span::new(end - token.len, end);
                return token.kind;
            }
        }
    }

    fn peek(&mut self) -> &lex::TokenKind {
        if matches!(self.next_token.kind, lex::TokenKind::Whitespace) {
            let _whitespace = self.step();
        }
        &self.next_token.kind
    }
    */

    pub fn parse(mut self) -> Vec<(Event<'s>, u32)> {
        let mut len = 0;

        while let Some(c) = self.chars.peek() {
            //let start = self.pos();

            let cont = match c {
                '*' => Some((Strong, ContainerType::Both)),
                '_' => Some((Emph, ContainerType::Both)),
                '^' => Some((Superscript, ContainerType::Both)),
                '~' => Some((Subscript, ContainerType::Both)),
                '\'' => Some((SingleQuoted, ContainerType::Both)),
                '"' => Some((DoubleQuoted, ContainerType::Both)),
                '`' => todo!(),
                '{' => todo!(),
                '$' => todo!(),
                '<' => todo!(),
                '[' => todo!(),
                _ => None,
            };

            let ev = cont
                .and_then(|(cont, ty)| {
                    self.openers
                        .iter()
                        .rposition(|(c, _)| *c == cont)
                        .map(|i| {
                            if let Event::Start(c, state) = &mut self.events[i] {
                                assert_eq!(*c, cont);
                                if matches!(ty, ContainerType::Closer | ContainerType::Both) {
                                    *state = OpenerState::Closed;
                                    Some(Event::End(cont))
                                } else if matches!(ty, ContainerType::Opener | ContainerType::Both)
                                {
                                    *state = OpenerState::Discarded;
                                    Some(Event::Start(cont, OpenerState::Unclosed))
                                } else {
                                    None
                                }
                            } else {
                                unreachable!()
                            }
                        })
                        .unwrap_or_else(|| {
                            matches!(ty, ContainerType::Opener | ContainerType::Both).then(|| {
                                self.openers.push((cont, self.events.len()));
                                Event::Start(cont, OpenerState::Unclosed)
                            })
                        })
                })
                .unwrap_or(Event::Atom(Str));

            self.events.push(ev);
        }
        //self.events
        todo!()
    }
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
