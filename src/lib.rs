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
pub enum Event<'s> {
    /// Start of a tag.
    Start(Tag<'s>, Attributes<'s>),
    /// End of a tag.
    End(Tag<'s>),
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
    Hardbreak,
    /// An escape character, not visible in output.
    Escape,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Tag<'s> {
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
    /// A subscripted element.
    Subscript,
    /// A superscripted element.
    Superscript,
    /// An inserted element.
    Insert,
    /// A deleted element.
    Delete,
    /// An element emphasized with a bold typeface.
    Strong,
    /// An emphasized element.
    Emphasis,
    /// A highlighted inline element.
    Mark,
    /// An quoted element, using single quotes.
    SingleQuoted,
    /// A quoted inline element, using double quotes.
    DoubleQuoted,
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

impl<'s> Event<'s> {
    fn from_inline(src: &'s str, inline: inline::Event) -> Self {
        let content = inline.span.of(src);
        match inline.kind {
            inline::EventKind::Enter(c) | inline::EventKind::Exit(c) => {
                let t = match c {
                    inline::Container::Span => Tag::Span,
                    inline::Container::Subscript => Tag::Subscript,
                    inline::Container::Superscript => Tag::Superscript,
                    inline::Container::Insert => Tag::Insert,
                    inline::Container::Delete => Tag::Delete,
                    inline::Container::Emphasis => Tag::Emphasis,
                    inline::Container::Strong => Tag::Strong,
                    inline::Container::Mark => Tag::Mark,
                    inline::Container::SingleQuoted => Tag::SingleQuoted,
                    inline::Container::DoubleQuoted => Tag::DoubleQuoted,
                    _ => todo!(),
                };
                if matches!(inline.kind, inline::EventKind::Enter(_)) {
                    Self::Start(t, Attributes::none())
                } else {
                    Self::End(t)
                }
            }
            inline::EventKind::Atom(a) => match a {
                inline::Atom::Ellipsis => Self::Ellipsis,
                inline::Atom::EnDash => Self::EnDash,
                inline::Atom::EmDash => Self::EmDash,
                inline::Atom::Nbsp => Self::NonBreakingSpace,
                inline::Atom::Softbreak => Self::Softbreak,
                inline::Atom::Hardbreak => Self::Hardbreak,
                inline::Atom::Escape => Self::Escape,
                _ => todo!(),
            },
            inline::EventKind::Node(n) => match n {
                inline::Node::Str => Self::Str(content),
                inline::Node::Verbatim => Self::Verbatim(content),
                inline::Node::InlineMath => Self::Math {
                    content,
                    display: false,
                },
                inline::Node::DisplayMath => Self::Math {
                    content,
                    display: true,
                },
                _ => todo!(),
            },
        }
    }
}

impl<'s> Tag<'s> {
    fn from_block(src: &'s str, block: block::Block) -> Self {
        match block {
            block::Block::Leaf(l) => match l {
                block::Leaf::Paragraph => Self::Paragraph,
                block::Leaf::Heading { level } => Self::Heading { level },
                block::Leaf::CodeBlock { .. } => Self::CodeBlock { language: None },
                _ => todo!(),
            },
            block::Block::Container(c) => match c {
                block::Container::Blockquote => Self::Blockquote,
                block::Container::Div { .. } => Self::Div,
                block::Container::Footnote { .. } => Self::Footnote { tag: todo!() },
                _ => todo!(),
            },
        }
    }
}

// Attributes are rare, better to pay 8 bytes always and sometimes an extra allocation instead of
// always 24 bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, &'s str)>>>);

impl<'s> Attributes<'s> {
    #[must_use]
    pub fn none() -> Self {
        Self(None)
    }

    #[must_use]
    pub fn valid(src: &str) -> bool {
        todo!()
    }

    #[must_use]
    pub fn parse(src: &'s str) -> Self {
        todo!()
    }
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
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(parser) = &mut self.parser {
            // inside leaf block, with inline content
            if let Some(mut inline) = parser.next() {
                inline.span = inline.span.translate(self.inline_start);
                return Some(Event::from_inline(self.src, inline));
            } else if let Some(ev) = self.tree.next() {
                match ev.kind {
                    tree::EventKind::Element(atom) => {
                        assert_eq!(atom, block::Atom::Inline);
                        parser.parse(ev.span.of(self.src));
                        self.inline_start = ev.span.start();
                    }
                    tree::EventKind::Exit(block) => {
                        self.parser = None;
                        return Some(Event::End(Tag::from_block(self.src, block)));
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
                Event::Start(Tag::from_block(self.src, block), Attributes::none())
            }
            tree::EventKind::Exit(block) => Event::End(Tag::from_block(self.src, block)),
        })
    }
}

#[cfg(test)]
mod test {
    use super::Attributes;
    use super::Event::*;
    use super::Tag::*;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let actual = super::Parser::new($src).collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(
                actual,
                expected,
                concat!(
                    "\n",
                    "\x1b[0;1m====================== INPUT =========================\x1b[0m\n",
                    "\x1b[2m{}",
                    "\x1b[0;1m================ ACTUAL vs EXPECTED ==================\x1b[0m\n",
                    "{}",
                    "\x1b[0;1m======================================================\x1b[0m\n",
                ),
                $src,
                {
                    let a = actual.iter().map(|n| format!("{:?}", n)).collect::<Vec<_>>();
                    let b = expected.iter().map(|n| format!("{:?}", n)).collect::<Vec<_>>();
                    let max = a.len().max(b.len());
                    let a_width = a.iter().map(|a| a.len()).max().unwrap_or(0);
                    a.iter()
                        .map(AsRef::as_ref)
                        .chain(std::iter::repeat(""))
                        .zip(b.iter().map(AsRef::as_ref).chain(std::iter::repeat("")))
                        .take(max)
                        .map(|(a, b)|
                            format!(
                                "\x1b[{}m{:a_width$}\x1b[0m    {}=    \x1b[{}m{}\x1b[0m\n",
                                if a == b { "2" } else { "31" },
                                a,
                                if a == b { '=' } else { '!' },
                                if a == b { "2" } else { "32" },
                                b,
                                a_width = a_width,
                            )
                        )
                        .collect::<String>()
                },
            );
        };
    }

    #[test]
    fn para() {
        test_parse!(
            "para",
            Start(Paragraph, Attributes::none()),
            Str("para"),
            End(Paragraph),
        );
        test_parse!(
            "pa     ra",
            Start(Paragraph, Attributes::none()),
            Str("pa     ra"),
            End(Paragraph),
        );
        test_parse!(
            "para0\n\npara1",
            Start(Paragraph, Attributes::none()),
            Str("para0\n"),
            End(Paragraph),
            Blankline,
            Start(Paragraph, Attributes::none()),
            Str("para1"),
            End(Paragraph),
        );
    }
}
