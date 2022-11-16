use crate::Span;

use crate::tree;

use Atom::*;
use Container::*;

pub type Tree = tree::Tree<Container, Atom>;

pub fn parse<I: Iterator<Item = Span>>(src: &str, inlines: I) -> Tree {
    Parser::new(src).parse(inlines)
}

pub enum Inline {
    Atom(Atom),
    Container(Container),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Str,
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,
    FootnoteReference,
    ExplicitLink,
    ReferenceLink,
    Emoji,
    OpenMarker,
    Ellipses,
    ImageMarker,
    EmDash,
    RawFormat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

pub struct Event;

pub struct Parser<'s> {
    src: &'s str,
    openers: Vec<(Container, usize)>,
    events: Vec<(Event, Span)>,
    //tree: tree::Builder<Container, Atom>,
}

impl<'s> Parser<'s> {
    fn new(src: &'s str) -> Self {
        Self {
            src,
            openers: Vec::new(),
            events: Vec::new(),
        }
    }

    fn parse<I: Iterator<Item = Span>>(mut self, inlines: I) -> Tree {
        todo!()
    }
}
