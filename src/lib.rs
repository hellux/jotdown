mod block;
mod html;
mod inline;
mod lex;
mod span;
mod tree;

use span::Span;

pub struct Block;

const EOF: char = '\0';

#[derive(Debug, PartialEq, Eq)]
pub enum ListType {
    Unordered,
    Ordered,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TagKind<'s> {
    Paragraph,
    Heading { level: u8 },
    Table,
    TableRow,
    TableCell,
    RawBlock { format: &'s str },
    CodeBlock { language: &'s str },
    Blockquote,
    Div,
    UnorderedList,
    OrderedList { start: usize },
    ListItem,
    DescriptionList,
    DescriptionItem,
    Footnote { tag: &'s str },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event2<'s> {
    Start(TagKind<'s>),
    End(TagKind<'s>),
    Blankline,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Start(block::Block),
    End,
    Inline(inline::Event),
    Blankline,
}

pub struct Parser<'s> {
    src: &'s str,
    tree: block::Tree,
    parser: Option<inline::Parser<'s>>,
    inline_start: usize,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: block::parse(src),
            parser: None,
            inline_start: 0,
        }
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(parser) = &mut self.parser {
            // inside leaf block, with inline content
            if let Some(mut inline) = parser.next() {
                inline.span = inline.span.translate(self.inline_start);
                return Some(Event::Inline(inline));
            } else if let Some(ev) = self.tree.next() {
                match ev.kind {
                    tree::EventKind::Element(atom) => {
                        assert_eq!(atom, block::Atom::Inline);
                        parser.parse(ev.span.of(self.src));
                        self.inline_start = ev.span.start();
                    }
                    tree::EventKind::Exit => {
                        self.parser = None;
                        return Some(Event::End);
                    }
                    tree::EventKind::Enter(..) => unreachable!(),
                }
            }
        }

        self.tree.next().map(|ev| match ev.kind {
            tree::EventKind::Element(atom) => {
                assert_eq!(atom, block::Atom::Blankline);
                Event::Blankline
            }
            tree::EventKind::Enter(block) => {
                if matches!(block, block::Block::Leaf(..)) {
                    self.parser = Some(inline::Parser::new());
                }
                Event::Start(block)
            }
            tree::EventKind::Exit => Event::End,
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
    use crate::inline::EventKind::*;
    use crate::inline::Node::*;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let actual = super::Parser::new($src).collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn para() {
        test_parse!(
            "para",
            Start(Leaf(Paragraph)),
            Inline(Node(Str).span(0, 4)),
            End
        );
        test_parse!(
            "pa     ra",
            Start(Leaf(Paragraph)),
            Inline(Node(Str).span(0, 9)),
            End
        );
        test_parse!(
            "para0\n\npara1",
            Start(Leaf(Paragraph)),
            Inline(Node(Str).span(0, 6)),
            End,
            Blankline,
            Start(Leaf(Paragraph)),
            Inline(Node(Str).span(7, 12)),
            End,
        );
    }
}
