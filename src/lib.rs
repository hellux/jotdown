mod block;
mod inline;
mod lex;
mod span;
mod tree;

use inline::Atom;
use inline::Container as InlineTag;

pub struct Block;

const EOF: char = '\0';

type CowStr<'s> = std::borrow::Cow<'s, str>;

/*
pub enum Tag<'s> {
    Paragraph,
    Heading { level: u8 },
    BlockQuote,
    CodeBlock { info_string: CowStr<'s> },
    List { start_index: Option<u64> },
    ListItem,
    FootnoteDefinition { label: CowStr<'s> },
    Table,
    Image {},
    Link {},
    Block(Block),
    Inline(InlineTag),
}

pub struct Attributes; // TODO

pub enum Event<'s> {
    Start(Tag<'s>, Attributes),
    End(Tag<'s>),
    Atom(Atom<'s>),
}
*/

use span::Span;

pub struct Parser<'s> {
    src: &'s str,
    tree: block::Tree,
}

impl<'s> Parser<'s> {
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: block::parse(src),
        }
    }

    pub fn parse(&mut self) {}

    pub fn iter(&self) -> Iter {
        Iter {
            src: self.src,
            tree: self.tree.iter().peekable(),
            events: Vec::new(),
        }
    }
}

pub struct Iter<'s> {
    src: &'s str,
    tree: std::iter::Peekable<block::TreeIter<'s>>,
    events: Vec<inline::Event>,
}

impl<'s> Iterator for Iter<'s> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.tree.next().map(|ev| match ev {
            tree::Event::Enter(block::Block::Container(cont), _sp) => {
                format!("cont {:?}", cont)
            }
            tree::Event::Enter(block::Block::Leaf(leaf), _sp) => {
                // concatenate all inlines
                let chars = (&mut self.tree)
                    .take_while(|ev| matches!(ev, tree::Event::Element(..)))
                    .flat_map(|ev| ev.span().of(self.src).chars());
                //inline::Parser::new(chars).parse(&mut self.events);
                /*
                let chars = std::iter::from_fn(|| {
                    let mut eat = false;
                    let ret = if let Some(tree::Event::Element(_a, sp)) = self.tree.peek() {
                        eat = true;
                        let chars = sp.of(self.src).chars();
                        Some(chars)
                    } else {
                        None
                    };
                    if eat {
                        self.tree.next();
                    }
                    ret
                })
                .flatten();
                */
                format!("leaf {:?} {:?}", leaf, self.events)
            }
            tree::Event::Element(atom, _sp) => {
                format!("atom {:?}", atom)
            }
            tree::Event::Exit => "exit".to_string(),
        })
    }
}
