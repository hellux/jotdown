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
pub enum Event2<'s> {
    /// Start of a tag.
    Start(TagKind<'s>, Attributes<'s>),
    /// End of a tag.
    End(TagKind<'s>),
    /// A string object, text only.
    Str(&'s str),
    /// A verbatim string.
    Verbatim(&'s str),
    /// An inline or display math element.
    Math { content: &'s str, display: bool },
    /// An ellipsis, i.e. a set of three periods.
    Ellipsis,
    /// An en dash.
    EnDash,
    /// An em dash.
    EmDash,
    /// A thematic break, typically a horizontal rule.
    ThematicBreak,
    /// A blank line.
    Blankline,
    /// A space that may not break a line.
    NonBreakingSpace,
    /// A newline that may or may not break a line in the output format.
    Softbreak,
    /// A newline that must break a line.
    HardBreak,
}

// Attributes are rare, better to pay 8 bytes always and sometimes an extra allocation instead of
// always 24 bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, &'s str)>>>);

#[derive(Debug, PartialEq, Eq)]
pub enum TagKind<'s> {
    /// A paragraph.
    Paragraph,
    /// A heading.
    Heading { level: u8 },
    /// A link with a destination URL.
    Link(&'s str, LinkType),
    /// An image.
    Image(&'s str),
    /// A divider element.
    Div,
    /// An inline divider element.
    Span,
    /// A table element.
    Table,
    /// A row element of a table.
    TableRow,
    /// A cell element of row within a table.
    TableCell,
    /// A block with raw markup for a specific output format.
    RawBlock { format: &'s str },
    /// A block with code in a specific language.
    CodeBlock { language: Option<&'s str> },
    /// A blockquote element.
    Blockquote,
    /// A list.
    List(List),
    /// An item of a list
    ListItem,
    /// A description list element.
    DescriptionList,
    /// A item of a description list.
    DescriptionItem,
    /// A footnote definition.
    Footnote { tag: &'s str },
}

#[derive(Debug, PartialEq, Eq)]
pub enum LinkType {
    Inline,
    Reference,
    Autolink,
    Email,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum List {
    Unordered,
    Ordered {
        kind: OrderedListKind,
        start: u32,
        format: OrderedListFormat,
    },
    Description,
    Task(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedListKind {
    /// Decimal numbering, e.g. `1)`.
    Decimal,
    /// Lowercase alphabetic numbering, e.g. `a)`.
    AlphaLower,
    /// Uppercase alphabetic numbering, e.g. `A)`.
    AlphaUpper,
    /// Lowercase roman numbering, e.g. `iv)`.
    RomanLower,
    /// Uppercase roman numbering, e.g. `IV)`.
    RomanUpper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedListFormat {
    /// Number is followed by a period, e.g. `1.`.
    Period,
    /// Number is followed by a closing parenthesis, e.g. `1)`.
    Paren,
    /// Number is enclosed by parentheses, e.g. `(1)`.
    ParenParen,
}

/*
impl<'s> Event<'s> {
    fn from_inline(src: &'s str, inline: inline::Event) -> Self {
        match inline {
            Enter
        }
    }
}
*/

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
