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
            inline_start: 0,
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
    inline_start: usize,
}

impl<'s> Iterator for Iter<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(parser) = &mut self.parser {
            // inside leaf block, with inline content
            if let Some(mut inline) = parser.next() {
                if let inline::Event::Node(inline::Node { span, .. }) = &mut inline {
                    *span = span.translate(self.inline_start);
                }
                return Some(Event::Inline(inline));
            } else if let Some(ev) = self.tree.next() {
                match ev {
                    tree::Event::Element(atom, sp) => {
                        assert_eq!(*atom, block::Atom::Inline);
                        parser.parse(sp.of(self.src));
                        self.inline_start = sp.start();
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
            tree::Event::Enter(block, ..) => {
                if matches!(block, block::Block::Leaf(..)) {
                    self.parser = Some(inline::Parser::new());
                }
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
    use crate::inline::NodeKind::*;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let actual = super::Parser::new($src).iter().collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn para() {
        test_parse!(
            "para",
            Start(Leaf(Paragraph)),
            Inline(Node(Str.span(0, 4))),
            End
        );
        test_parse!(
            "pa     ra",
            Start(Leaf(Paragraph)),
            Inline(Node(Str.span(0, 9))),
            End
        );
        test_parse!(
            "para0\n\npara1",
            Start(Leaf(Paragraph)),
            Inline(Node(Str.span(0, 6))),
            End,
            Blankline,
            Start(Leaf(Paragraph)),
            Inline(Node(Str.span(7, 12))),
            End,
        );
    }
}
