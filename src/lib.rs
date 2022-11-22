mod block;
mod inline;
mod lex;
mod span;
mod tree;

pub struct Block;

const EOF: char = '\0';

use span::Span;

pub struct Parser<'s> {
    src: &'s str,
    tree: block::Tree,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: block::parse(src),
        }
    }

    #[must_use]
    pub fn iter(&self) -> Iter {
        Iter {
            src: self.src,
            tree: self.tree.iter(),
            parser: None,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Start(block::Block),
    End,
    Inline(inline::Event),
    Blankline,
}

pub struct Iter<'s> {
    src: &'s str,
    tree: block::TreeIter<'s>,
    parser: Option<inline::Parser<'s>>,
}

impl<'s> Iterator for Iter<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(parser) = &mut self.parser {
            // inside leaf block, with inline content
            if let Some(inline) = parser.next() {
                return Some(Event::Inline(inline));
            } else if let Some(ev) = self.tree.next() {
                match ev {
                    tree::Event::Element(atom, sp) => {
                        assert_eq!(*atom, block::Atom::Inline);
                        parser.parse(sp.of(self.src));
                    }
                    tree::Event::Exit => {
                        self.parser = None;
                        return Some(Event::End);
                    }
                    tree::Event::Enter(..) => unreachable!(),
                }
            }
        }

        self.tree.next().map(|ev| match ev {
            tree::Event::Element(atom, _sp) => {
                assert_eq!(*atom, block::Atom::Blankline);
                Event::Blankline
            }
            tree::Event::Enter(block @ block::Block::Container(..), ..) => {
                Event::Start(block.clone())
            }
            tree::Event::Enter(block @ block::Block::Leaf(..), ..) => {
                self.parser = Some(inline::Parser::new());
                Event::Start(block.clone())
            }
            tree::Event::Exit => Event::End,
        })
    }
}

#[cfg(test)]
mod test {
    use super::Event::*;
    use crate::block::Block::*;
    use crate::block::Container::*;
    use crate::block::Leaf::*;
    use crate::inline::Atom::*;
    use crate::inline::Event::*;

    #[test]
    fn basic() {
        assert_eq!(
            super::Parser::new("abc").iter().collect::<Vec<_>>(),
            &[Start(Leaf(Paragraph)), Inline(Atom(Str)), End]
        );
    }
}
