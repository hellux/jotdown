pub mod html;

mod block;
mod inline;
mod lex;
mod span;
mod tree;

use span::Span;

pub struct Block;

const EOF: char = '\0';

#[derive(Debug, PartialEq, Eq)]
pub enum Event<'s> {
    /// Start of a container.
    Start(Container<'s>, Attributes<'s>),
    /// End of a container.
    End(Container<'s>),
    /// A string object, text only.
    Str(&'s str),
    /// An atomic element.
    Atom(Atom),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Container<'s> {
    /// A blockquote element.
    Blockquote,
    /// A list.
    List(List),
    /// An item of a list
    ListItem,
    /// A description list element.
    DescriptionList,
    /// Details describing a term within a description list.
    DescriptionDetails,
    /// A footnote definition.
    Footnote { tag: &'s str },
    /// A table element.
    Table,
    /// A row element of a table.
    TableRow,
    /// A block-level divider element.
    Div { class: Option<&'s str> },
    /// A paragraph.
    Paragraph,
    /// A heading.
    Heading { level: usize },
    /// A cell element of row within a table.
    TableCell,
    /// A term within a description list.
    DescriptionTerm,
    /// A block with raw markup for a specific output format.
    RawBlock { format: &'s str },
    /// A block with code in a specific language.
    CodeBlock { lang: Option<&'s str> },
    /// An inline divider element.
    Span,
    /// An inline link with a destination URL.
    Link(&'s str, LinkType),
    /// An inline image.
    Image(&'s str),
    /// An inline verbatim string.
    Verbatim,
    /// An inline or display math element.
    Math { display: bool },
    /// Inline raw markup for a specific output format.
    RawInline { format: &'s str },
    /// A subscripted element.
    Subscript,
    /// A superscripted element.
    Superscript,
    /// An inserted inline element.
    Insert,
    /// A deleted inline element.
    Delete,
    /// An inline element emphasized with a bold typeface.
    Strong,
    /// An emphasized inline element.
    Emphasis,
    /// A highlighted inline element.
    Mark,
    /// An quoted inline element, using single quotes.
    SingleQuoted,
    /// A quoted inline element, using double quotes.
    DoubleQuoted,
}

impl<'s> Container<'s> {
    /// Is a block element.
    fn is_block(&self) -> bool {
        match self {
            Self::Blockquote
            | Self::List(..)
            | Self::ListItem
            | Self::DescriptionList
            | Self::DescriptionDetails
            | Self::Footnote { .. }
            | Self::Table
            | Self::TableRow
            | Self::Div { .. }
            | Self::Paragraph
            | Self::Heading { .. }
            | Self::DescriptionTerm
            | Self::TableCell
            | Self::RawBlock { .. }
            | Self::CodeBlock { .. } => true,
            Self::Span
            | Self::Link(..)
            | Self::Image(..)
            | Self::Verbatim
            | Self::Math { .. }
            | Self::RawInline { .. }
            | Self::Subscript
            | Self::Superscript
            | Self::Insert
            | Self::Delete
            | Self::Strong
            | Self::Emphasis
            | Self::Mark
            | Self::SingleQuoted
            | Self::DoubleQuoted => false,
        }
    }

    /// Is a block element that may contain children blocks.
    fn is_block_container(&self) -> bool {
        match self {
            Self::Blockquote
            | Self::List(..)
            | Self::ListItem
            | Self::DescriptionList
            | Self::DescriptionDetails
            | Self::Footnote { .. }
            | Self::Table
            | Self::TableRow
            | Self::Div { .. } => true,
            Self::Paragraph
            | Self::Heading { .. }
            | Self::TableCell
            | Self::DescriptionTerm
            | Self::RawBlock { .. }
            | Self::CodeBlock { .. }
            | Self::Span
            | Self::Link(..)
            | Self::Image(..)
            | Self::Verbatim
            | Self::Math { .. }
            | Self::RawInline { .. }
            | Self::Subscript
            | Self::Superscript
            | Self::Insert
            | Self::Delete
            | Self::Strong
            | Self::Emphasis
            | Self::Mark
            | Self::SingleQuoted
            | Self::DoubleQuoted => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LinkType {
    Inline,
    Reference,
    AutoLink,
    Email,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum List {
    Unordered,
    Ordered { kind: OrderedListKind, start: u32 },
    Description,
    Task,
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
pub enum OrderedListStyle {
    /// Number is followed by a period, e.g. `1.`.
    Period,
    /// Number is followed by a closing parenthesis, e.g. `1)`.
    Paren,
    /// Number is enclosed by parentheses, e.g. `(1)`.
    ParenParen,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Atom {
    /// A horizontal ellipsis, i.e. a set of three periods.
    Ellipsis,
    /// An en dash.
    EnDash,
    /// An em dash.
    EmDash,
    /// A thematic break, typically a horizontal rule.
    ThematicBreak,
    /// A space that may not break a line.
    NonBreakingSpace,
    /// A newline that may or may not break a line in the output format.
    Softbreak,
    /// A newline that must break a line.
    Hardbreak,
    /// An escape character, not visible in output.
    Escape,
    /// A blank line, not visible in output.
    Blankline,
}

impl<'s> Event<'s> {
    fn from_inline(src: &'s str, inline: inline::Event) -> Self {
        let content = inline.span.of(src);
        match inline.kind {
            inline::EventKind::Enter(c) | inline::EventKind::Exit(c) => {
                let t = match c {
                    inline::Container::Span => Container::Span,
                    inline::Container::Verbatim => Container::Verbatim,
                    inline::Container::InlineMath => Container::Math { display: false },
                    inline::Container::DisplayMath => Container::Math { display: true },
                    inline::Container::RawFormat => Container::RawInline { format: content },
                    inline::Container::Subscript => Container::Subscript,
                    inline::Container::Superscript => Container::Superscript,
                    inline::Container::Insert => Container::Insert,
                    inline::Container::Delete => Container::Delete,
                    inline::Container::Emphasis => Container::Emphasis,
                    inline::Container::Strong => Container::Strong,
                    inline::Container::Mark => Container::Mark,
                    inline::Container::SingleQuoted => Container::SingleQuoted,
                    inline::Container::DoubleQuoted => Container::DoubleQuoted,
                    _ => todo!(),
                };
                if matches!(inline.kind, inline::EventKind::Enter(_)) {
                    Self::Start(t, Attributes::none())
                } else {
                    Self::End(t)
                }
            }
            inline::EventKind::Atom(a) => Event::Atom(match a {
                inline::Atom::Ellipsis => Atom::Ellipsis,
                inline::Atom::EnDash => Atom::EnDash,
                inline::Atom::EmDash => Atom::EmDash,
                inline::Atom::Nbsp => Atom::NonBreakingSpace,
                inline::Atom::Softbreak => Atom::Softbreak,
                inline::Atom::Hardbreak => Atom::Hardbreak,
                inline::Atom::Escape => Atom::Escape,
            }),
            inline::EventKind::Str => Self::Str(content),
            inline::EventKind::Attributes => todo!(),
        }
    }
}

impl<'s> Container<'s> {
    fn from_leaf_block(content: &str, l: block::Leaf) -> Self {
        match l {
            block::Leaf::Paragraph => Self::Paragraph,
            block::Leaf::Heading => Self::Heading {
                level: content.len(),
            },
            block::Leaf::CodeBlock => Self::CodeBlock { lang: None },
            _ => todo!(),
        }
    }

    fn from_container_block(content: &'s str, c: block::Container) -> Self {
        match c {
            block::Container::Blockquote => Self::Blockquote,
            block::Container::Div => Self::Div { class: None },
            block::Container::Footnote => Self::Footnote { tag: content },
            block::Container::ListItem => todo!(),
        }
    }
}

// Attributes are rare, better to pay 8 bytes always and sometimes an extra indirection instead of
// always 24 bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attributes<'s>(Option<Box<Vec<(&'s str, &'s str)>>>);

impl<'s> Attributes<'s> {
    #[must_use]
    pub fn none() -> Self {
        Self(None)
    }

    pub fn take(&mut self) -> Self {
        Self(self.0.take())
    }

    pub fn parse(&mut self, src: &'s str) {
        todo!()
    }
}

#[derive(Clone)]
struct InlineChars<'t, 's> {
    src: &'s str,
    inlines: tree::Inlines<'t, block::Block, block::Atom>,
}

impl<'t, 's> Iterator for InlineChars<'t, 's> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        (&mut self.inlines)
            .flat_map(|sp| sp.of(self.src).chars())
            .next()
    }
}

pub struct Parser<'s> {
    src: &'s str,
    tree: block::Tree,
    inline_parser: Option<inline::Parser<InlineChars<'s, 's>>>,
    inline_start: usize,
    block_attributes: Attributes<'s>,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: block::parse(src),
            inline_parser: None,
            inline_start: 0,
            block_attributes: Attributes::none(),
        }
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(parser) = &mut self.inline_parser {
            if let Some(mut inline) = parser.next() {
                inline.span = inline.span.translate(self.inline_start);
                return Some(Event::from_inline(self.src, inline));
            }
            self.inline_parser = None;
        }

        for ev in &mut self.tree {
            let content = ev.span.of(self.src);
            let event = match ev.kind {
                tree::EventKind::Atom(a) => match a {
                    block::Atom::Blankline => Event::Atom(Atom::Blankline),
                    block::Atom::ThematicBreak => Event::Atom(Atom::ThematicBreak),
                    block::Atom::Attributes => {
                        self.block_attributes.parse(content);
                        continue;
                    }
                },
                tree::EventKind::Enter(b) => {
                    if matches!(b, block::Block::Leaf(_)) {
                        let chars = InlineChars {
                            src: self.src,
                            inlines: self.tree.inlines(),
                        };
                        // TODO solve self-referential reference here without unsafe
                        self.inline_parser =
                            unsafe { Some(std::mem::transmute(inline::Parser::new(chars))) };
                        self.inline_start = ev.span.end();
                    }
                    let container = match b {
                        block::Block::Leaf(block::Leaf::CodeBlock { .. }) => {
                            self.inline_start += 1; // skip newline
                            Container::CodeBlock {
                                lang: (!ev.span.is_empty()).then(|| content),
                            }
                        }
                        block::Block::Container(block::Container::Div { .. }) => Container::Div {
                            class: (!ev.span.is_empty()).then(|| ev.span.of(self.src)),
                        },
                        block::Block::Leaf(l) => Container::from_leaf_block(content, l),
                        block::Block::Container(c) => Container::from_container_block(content, c),
                        block::Block::Atom(..) => panic!(),
                    };
                    Event::Start(container, self.block_attributes.take())
                }
                tree::EventKind::Exit(b) => Event::End(match b {
                    block::Block::Leaf(l) => Container::from_leaf_block(content, l),
                    block::Block::Container(c) => Container::from_container_block(content, c),
                    block::Block::Atom(..) => panic!(),
                }),
                tree::EventKind::Inline => panic!(),
            };
            return Some(event);
        }

        None
    }
}

#[cfg(test)]
mod test {
    use super::Atom::*;
    use super::Attributes;
    use super::Container::*;
    use super::Event::*;

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
            Str("para0"),
            End(Paragraph),
            Atom(Blankline),
            Start(Paragraph, Attributes::none()),
            Str("para1"),
            End(Paragraph),
        );
    }

    #[test]
    fn verbatim() {
        test_parse!(
            "`abc\ndef",
            Start(Paragraph, Attributes::none()),
            Start(Verbatim, Attributes::none()),
            Str("abc\ndef"),
            End(Verbatim),
            End(Paragraph),
        );
    }

    #[test]
    fn raw_inline() {
        test_parse!(
            "``raw\nraw``{=format}",
            Start(Paragraph, Attributes::none()),
            Start(RawInline { format: "format" }, Attributes::none()),
            Str("raw\nraw"),
            End(RawInline { format: "format" }),
            End(Paragraph),
        );
    }
}
