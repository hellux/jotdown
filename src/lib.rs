pub mod html;

mod attr;
mod block;
mod inline;
mod lex;
mod span;
mod tree;

use span::DiscontinuousString;
use span::Span;

pub use attr::Attributes;

type CowStr<'s> = std::borrow::Cow<'s, str>;

const EOF: char = '\0';

#[derive(Debug, PartialEq, Eq)]
pub enum Event<'s> {
    /// Start of a container.
    Start(Container<'s>, Attributes<'s>),
    /// End of a container.
    End(Container<'s>),
    /// A string object, text only.
    Str(CowStr<'s>),
    /// An atomic element.
    Atom(Atom<'s>),
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
    Footnote { tag: &'s str, number: usize },
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
    Link(CowStr<'s>, LinkType),
    /// An inline image with a source URL. Inner Str objects compose the alternative text.
    Image(CowStr<'s>, SpanLinkType),
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
pub enum SpanLinkType {
    Inline,
    Reference,
}

#[derive(Debug, PartialEq, Eq)]
pub enum LinkType {
    Span(SpanLinkType),
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
pub enum Atom<'s> {
    /// A footnote reference.
    FootnoteReference(&'s str, usize),
    /// A horizontal ellipsis, i.e. a set of three periods.
    Ellipsis,
    /// An en dash.
    EnDash,
    /// An em dash.
    EmDash,
    /// A thematic break, typically a horizontal rule.
    ThematicBreak,
    /// A space that must not break a line.
    NonBreakingSpace,
    /// A newline that may or may not break a line in the output.
    Softbreak,
    /// A newline that must break a line in the output.
    Hardbreak,
    /// An escape character, not visible in output.
    Escape,
    /// A blank line, not visible in output.
    Blankline,
}

impl<'s> Container<'s> {
    fn from_leaf_block(content: &'s str, l: block::Leaf) -> Self {
        match l {
            block::Leaf::Paragraph => Self::Paragraph,
            block::Leaf::Heading => Self::Heading {
                level: content.len(),
            },
            block::Leaf::CodeBlock => {
                if let Some(format) = content.strip_prefix('=') {
                    Self::RawBlock { format }
                } else {
                    Self::CodeBlock {
                        lang: (!content.is_empty()).then(|| content),
                    }
                }
            }
            _ => todo!(),
        }
    }
}

pub struct Parser<'s> {
    src: &'s str,

    _tree_data: block::Tree,
    link_definitions: std::collections::HashMap<&'s str, CowStr<'s>>,

    tree: block::Branch,
    inlines: span::InlineSpans<'s>,
    inline_parser: Option<inline::Parser<span::InlineCharsIter<'s>>>,
    /// Footnote references in the order they were encountered, without duplicates.
    footnote_references: Vec<&'s str>,
    /// Cache of footnotes to emit at the end.
    footnotes: std::collections::HashMap<&'s str, block::Branch>,
    /// Next or current footnote being parsed and emitted.
    footnote_index: usize,
    /// Currently within a footnote.
    footnote_active: bool,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        let tree = block::parse(src);

        let link_definitions = {
            let mut branch = tree.root();
            let mut defs = std::collections::HashMap::new();
            while let Some(e) = branch.next() {
                if let tree::EventKind::Enter(block::Node::Leaf(block::Leaf::LinkDefinition)) =
                    e.kind
                {
                    let tag = e.span.of(src);
                    let url = match branch.count_children() {
                        0 => "".into(),
                        1 => branch.take_inlines().next().unwrap().of(src).trim().into(),
                        _ => branch.take_inlines().map(|sp| sp.of(src).trim()).collect(),
                    };
                    defs.insert(tag, url);
                }
            }
            defs
        };

        let branch = tree.root();

        Self {
            src,
            _tree_data: tree,
            link_definitions,
            tree: branch,
            footnote_references: Vec::new(),
            footnotes: std::collections::HashMap::new(),
            footnote_index: 0,
            footnote_active: false,
            inlines: span::InlineSpans::new(src),
            inline_parser: None,
        }
    }
}

impl<'s> Parser<'s> {
    fn inline(&mut self) -> Option<Event<'s>> {
        self.inline_parser.as_mut().and_then(|parser| {
            let mut inline = parser.next();

            let mut first_is_attr = false;
            let attributes = inline.as_ref().map_or_else(Attributes::new, |inl| {
                if let inline::EventKind::Attributes = inl.kind {
                    first_is_attr = true;
                    attr::parse(self.inlines.slice(inl.span))
                } else {
                    Attributes::new()
                }
            });

            if first_is_attr {
                inline = parser.next();
            }

            inline.map(|inline| match inline.kind {
                inline::EventKind::Enter(c) | inline::EventKind::Exit(c) => {
                    let t = match c {
                        inline::Container::Span => Container::Span,
                        inline::Container::Verbatim => Container::Verbatim,
                        inline::Container::InlineMath => Container::Math { display: false },
                        inline::Container::DisplayMath => Container::Math { display: true },
                        inline::Container::RawFormat => Container::RawInline {
                            format: match self.inlines.src(inline.span) {
                                CowStr::Owned(_) => panic!(),
                                CowStr::Borrowed(s) => s,
                            },
                        },
                        inline::Container::Subscript => Container::Subscript,
                        inline::Container::Superscript => Container::Superscript,
                        inline::Container::Insert => Container::Insert,
                        inline::Container::Delete => Container::Delete,
                        inline::Container::Emphasis => Container::Emphasis,
                        inline::Container::Strong => Container::Strong,
                        inline::Container::Mark => Container::Mark,
                        inline::Container::SingleQuoted => Container::SingleQuoted,
                        inline::Container::DoubleQuoted => Container::DoubleQuoted,
                        inline::Container::InlineLink => Container::Link(
                            match self.inlines.src(inline.span) {
                                CowStr::Owned(s) => s.replace('\n', "").into(),
                                s @ CowStr::Borrowed(_) => s,
                            },
                            LinkType::Span(SpanLinkType::Inline),
                        ),
                        inline::Container::InlineImage => Container::Image(
                            match self.inlines.src(inline.span) {
                                CowStr::Owned(s) => s.replace('\n', "").into(),
                                s @ CowStr::Borrowed(_) => s,
                            },
                            SpanLinkType::Inline,
                        ),
                        inline::Container::ReferenceLink => Container::Link(
                            self.link_definitions
                                .get(self.inlines.src(inline.span).as_ref())
                                .cloned()
                                .unwrap_or_else(|| "".into()),
                            LinkType::Span(SpanLinkType::Reference),
                        ),
                        inline::Container::ReferenceImage => Container::Image(
                            self.link_definitions
                                .get(self.inlines.src(inline.span).as_ref())
                                .cloned()
                                .unwrap_or_else(|| "".into()),
                            SpanLinkType::Reference,
                        ),
                        inline::Container::Autolink => todo!("{:?}", c),
                    };
                    if matches!(inline.kind, inline::EventKind::Enter(_)) {
                        Event::Start(t, attributes)
                    } else {
                        Event::End(t)
                    }
                }
                inline::EventKind::Atom(a) => Event::Atom(match a {
                    inline::Atom::FootnoteReference => {
                        let tag = match self.inlines.src(inline.span) {
                            CowStr::Borrowed(s) => s,
                            CowStr::Owned(..) => panic!(),
                        };
                        let number = self
                            .footnote_references
                            .iter()
                            .position(|t| *t == tag)
                            .map_or_else(
                                || {
                                    self.footnote_references.push(tag);
                                    self.footnote_references.len()
                                },
                                |i| i + 1,
                            );
                        Atom::FootnoteReference(
                            match self.inlines.src(inline.span) {
                                CowStr::Borrowed(s) => s,
                                CowStr::Owned(..) => panic!(),
                            },
                            number,
                        )
                    }
                    inline::Atom::Ellipsis => Atom::Ellipsis,
                    inline::Atom::EnDash => Atom::EnDash,
                    inline::Atom::EmDash => Atom::EmDash,
                    inline::Atom::Nbsp => Atom::NonBreakingSpace,
                    inline::Atom::Softbreak => Atom::Softbreak,
                    inline::Atom::Hardbreak => Atom::Hardbreak,
                    inline::Atom::Escape => Atom::Escape,
                }),
                inline::EventKind::Str => Event::Str(self.inlines.src(inline.span)),
                inline::EventKind::Whitespace
                | inline::EventKind::Attributes
                | inline::EventKind::Placeholder => {
                    panic!("{:?}", inline)
                }
            })
        })
    }

    fn block(&mut self) -> Option<Event<'s>> {
        let mut attributes = Attributes::new();
        while let Some(ev) = &mut self.tree.next() {
            let content = ev.span.of(self.src);
            let event = match ev.kind {
                tree::EventKind::Atom(a) => match a {
                    block::Atom::Blankline => Event::Atom(Atom::Blankline),
                    block::Atom::ThematicBreak => Event::Atom(Atom::ThematicBreak),
                    block::Atom::Attributes => {
                        attributes.parse(content);
                        continue;
                    }
                },
                tree::EventKind::Enter(c) | tree::EventKind::Exit(c)
                    if matches!(c, block::Node::Leaf(block::Leaf::LinkDefinition)) =>
                {
                    // ignore link definitions
                    self.tree.take_inlines().last();
                    continue;
                }
                tree::EventKind::Enter(c) => match c {
                    block::Node::Leaf(l) => {
                        self.inlines.set_spans(self.tree.take_inlines());
                        self.inline_parser = Some(inline::Parser::new(self.inlines.chars()));
                        let container = Container::from_leaf_block(content, l);
                        Event::Start(container, attributes)
                    }
                    block::Node::Container(c) => {
                        let container = match c {
                            block::Container::Blockquote => Container::Blockquote,
                            block::Container::Div { .. } => Container::Div {
                                class: (!ev.span.is_empty()).then(|| content),
                            },
                            block::Container::Footnote => {
                                self.footnotes.insert(content, self.tree.take_branch());
                                continue;
                            }
                            block::Container::ListItem => panic!(),
                        };
                        Event::Start(container, attributes)
                    }
                },
                tree::EventKind::Exit(c) => match c {
                    block::Node::Leaf(l) => Event::End(Container::from_leaf_block(content, l)),
                    block::Node::Container(c) => {
                        let container = match c {
                            block::Container::Blockquote => Container::Blockquote,
                            block::Container::Div { .. } => Container::Div {
                                class: (!ev.span.is_empty()).then(|| content),
                            },
                            block::Container::Footnote => panic!(),
                            block::Container::ListItem => panic!(),
                        };
                        Event::End(container)
                    }
                },
                tree::EventKind::Inline => unreachable!(),
            };
            return Some(event);
        }
        None
    }

    fn footnote(&mut self) -> Option<Event<'s>> {
        if self.footnote_active {
            let tag = self.footnote_references.get(self.footnote_index).unwrap();
            self.footnote_index += 1;
            self.footnote_active = false;
            Some(Event::End(Container::Footnote {
                tag,
                number: self.footnote_index,
            }))
        } else if let Some(tag) = self.footnote_references.get(self.footnote_index) {
            self.tree = self
                .footnotes
                .remove(tag)
                .unwrap_or_else(block::Branch::empty);
            self.footnote_active = true;

            Some(Event::Start(
                Container::Footnote {
                    tag,
                    number: self.footnote_index + 1,
                },
                Attributes::new(),
            ))
        } else {
            None
        }
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inline()
            .or_else(|| self.block())
            .or_else(|| self.footnote())
    }
}

#[cfg(test)]
mod test {
    use super::Atom::*;
    use super::Attributes;
    use super::Container::*;
    use super::Event::*;
    use super::LinkType;
    use super::SpanLinkType;

    macro_rules! test_parse {
        ($src:expr $(,$($token:expr),* $(,)?)?) => {
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
    fn empty() {
        test_parse!("");
    }

    #[test]
    fn heading() {
        test_parse!(
            "#\n",
            Start(Heading { level: 1 }, Attributes::new()),
            End(Heading { level: 1 }),
        );
        test_parse!(
            "# abc\ndef\n",
            Start(Heading { level: 1 }, Attributes::new()),
            Str("abc".into()),
            Atom(Softbreak),
            Str("def".into()),
            End(Heading { level: 1 }),
        );
    }

    #[test]
    fn blockquote() {
        test_parse!(
            ">\n",
            Start(Blockquote, Attributes::new()),
            Atom(Blankline),
            End(Blockquote),
        );
    }

    #[test]
    fn para() {
        test_parse!(
            "para",
            Start(Paragraph, Attributes::new()),
            Str("para".into()),
            End(Paragraph),
        );
        test_parse!(
            "pa     ra",
            Start(Paragraph, Attributes::new()),
            Str("pa     ra".into()),
            End(Paragraph),
        );
        test_parse!(
            "para0\n\npara1",
            Start(Paragraph, Attributes::new()),
            Str("para0".into()),
            End(Paragraph),
            Atom(Blankline),
            Start(Paragraph, Attributes::new()),
            Str("para1".into()),
            End(Paragraph),
        );
    }

    #[test]
    fn verbatim() {
        test_parse!(
            "`abc\ndef",
            Start(Paragraph, Attributes::new()),
            Start(Verbatim, Attributes::new()),
            Str("abc\ndef".into()),
            End(Verbatim),
            End(Paragraph),
        );
        test_parse!(
            concat!(
                "> `abc\n",
                "> def\n", //
            ),
            Start(Blockquote, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Start(Verbatim, Attributes::new()),
            Str("abc\ndef".into()),
            End(Verbatim),
            End(Paragraph),
            End(Blockquote),
        );
    }

    #[test]
    fn raw_inline() {
        test_parse!(
            "``raw\nraw``{=format}",
            Start(Paragraph, Attributes::new()),
            Start(RawInline { format: "format" }, Attributes::new()),
            Str("raw\nraw".into()),
            End(RawInline { format: "format" }),
            End(Paragraph),
        );
    }

    #[test]
    fn raw_block() {
        test_parse!(
            "``` =html\n<table>\n```",
            Start(RawBlock { format: "html" }, Attributes::new()),
            Str("<table>".into()),
            Atom(Softbreak),
            End(RawBlock { format: "html" }),
        );
    }

    #[test]
    fn link_inline() {
        test_parse!(
            "[text](url)",
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Inline)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Inline))),
            End(Paragraph),
        );
        test_parse!(
            concat!(
                "> [text](url\n",
                "> url)\n", //
            ),
            Start(Blockquote, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline))),
            End(Paragraph),
            End(Blockquote),
        );
    }

    #[test]
    fn link_reference() {
        test_parse!(
            concat!(
                "[text][tag]\n",
                "\n",
                "[tag]: url\n" //
            ),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            End(Paragraph),
            Atom(Blankline),
        );
        test_parse!(
            concat!(
                "![text][tag]\n",
                "\n",
                "[tag]: url\n" //
            ),
            Start(Paragraph, Attributes::new()),
            Start(
                Image("url".into(), SpanLinkType::Reference),
                Attributes::new()
            ),
            Str("text".into()),
            End(Image("url".into(), SpanLinkType::Reference)),
            End(Paragraph),
            Atom(Blankline),
        );
    }

    #[test]
    fn link_reference_multiline() {
        test_parse!(
            concat!(
                "[text][tag]\n",
                "\n",
                "[tag]: u\n",
                " rl\n", //
            ),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            End(Paragraph),
            Atom(Blankline),
        );
        test_parse!(
            concat!(
                "[text][tag]\n",
                "\n",
                "[tag]:\n",
                " url\n", //
            ),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            End(Paragraph),
            Atom(Blankline),
        );
    }

    #[test]
    fn footnote_references() {
        test_parse!(
            "[^a][^b][^c]",
            Start(Paragraph, Attributes::new()),
            Atom(FootnoteReference("a", 1)),
            Atom(FootnoteReference("b", 2)),
            Atom(FootnoteReference("c", 3)),
            End(Paragraph),
            Start(
                Footnote {
                    tag: "a",
                    number: 1
                },
                Attributes::new()
            ),
            End(Footnote {
                tag: "a",
                number: 1
            }),
            Start(
                Footnote {
                    tag: "b",
                    number: 2
                },
                Attributes::new()
            ),
            End(Footnote {
                tag: "b",
                number: 2
            }),
            Start(
                Footnote {
                    tag: "c",
                    number: 3
                },
                Attributes::new()
            ),
            End(Footnote {
                tag: "c",
                number: 3
            }),
        );
    }

    #[test]
    fn footnote() {
        test_parse!(
            "[^a]\n\n[^a]: a\n",
            Start(Paragraph, Attributes::new()),
            Atom(FootnoteReference("a", 1)),
            End(Paragraph),
            Atom(Blankline),
            Start(
                Footnote {
                    tag: "a",
                    number: 1
                },
                Attributes::new()
            ),
            Start(Paragraph, Attributes::new()),
            Str("a".into()),
            End(Paragraph),
            End(Footnote {
                tag: "a",
                number: 1
            }),
        );
    }

    #[test]
    fn footnote_multiblock() {
        test_parse!(
            concat!(
                "[^a]\n",
                "\n",
                "[^a]: abc\n",
                "\n",
                " def", //
            ),
            Start(Paragraph, Attributes::new()),
            Atom(FootnoteReference("a", 1)),
            End(Paragraph),
            Atom(Blankline),
            Start(
                Footnote {
                    tag: "a",
                    number: 1
                },
                Attributes::new()
            ),
            Start(Paragraph, Attributes::new()),
            Str("abc".into()),
            End(Paragraph),
            Atom(Blankline),
            Start(Paragraph, Attributes::new()),
            Str("def".into()),
            End(Paragraph),
            End(Footnote {
                tag: "a",
                number: 1
            }),
        );
    }

    #[test]
    fn footnote_post() {
        test_parse!(
            concat!(
                "[^a]\n",
                "\n",
                "[^a]: note\n",
                "para\n", //
            ),
            Start(Paragraph, Attributes::new()),
            Atom(FootnoteReference("a", 1)),
            End(Paragraph),
            Atom(Blankline),
            Start(Paragraph, Attributes::new()),
            Str("para".into()),
            End(Paragraph),
            Start(
                Footnote {
                    tag: "a",
                    number: 1
                },
                Attributes::new()
            ),
            Start(Paragraph, Attributes::new()),
            Str("note".into()),
            End(Paragraph),
            End(Footnote {
                tag: "a",
                number: 1
            }),
        );
    }

    #[test]
    fn attr_block() {
        test_parse!(
            "{.some_class}\npara\n",
            Start(Paragraph, [("class", "some_class")].into_iter().collect()),
            Str("para".into()),
            End(Paragraph),
        );
    }

    #[test]
    fn attr_inline() {
        test_parse!(
            "abc _def_{.ghi}",
            Start(Paragraph, Attributes::new()),
            Str("abc ".into()),
            Start(Emphasis, [("class", "ghi")].into_iter().collect()),
            Str("def".into()),
            End(Emphasis),
            End(Paragraph),
        );
    }
}
