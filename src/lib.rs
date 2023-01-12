pub mod html;

mod attr;
mod block;
mod inline;
mod lex;
mod span;
mod tree;

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
pub enum Atom {
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
    fn from_leaf_block(content: &str, l: block::Leaf) -> Self {
        match l {
            block::Leaf::Paragraph => Self::Paragraph,
            block::Leaf::Heading => Self::Heading {
                level: content.len(),
            },
            block::Leaf::CodeBlock => panic!(),
            _ => todo!(),
        }
    }

    fn from_container_block(content: &'s str, c: block::Container) -> Self {
        match c {
            block::Container::Blockquote => Self::Blockquote,
            block::Container::Div => panic!(),
            block::Container::Footnote => Self::Footnote { tag: content },
            block::Container::ListItem => todo!(),
        }
    }
}

#[derive(Clone)]
struct InlineChars<'s, 't> {
    src: &'s str,
    inlines: std::slice::Iter<'t, Span>,
    next: std::str::Chars<'s>,
}

// Implement inlines.flat_map(|sp| sp.of(self.src).chars())
impl<'s, 't> InlineChars<'s, 't> {
    fn new(src: &'s str, inlines: &'t [Span]) -> Self {
        Self {
            src,
            inlines: inlines.iter(),
            next: "".chars(),
        }
    }
}

impl<'s, 't> Iterator for InlineChars<'s, 't> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        (&mut self.inlines)
            .flat_map(|sp| sp.of(self.src).chars())
            .next()
    }
}

trait DiscontinuousString<'s> {
    type Chars: Iterator<Item = char>;

    fn src(&self, span: Span) -> CowStr<'s>;

    fn chars(&self) -> Self::Chars;
}

impl<'s> DiscontinuousString<'s> for &'s str {
    type Chars = std::str::Chars<'s>;

    fn src(&self, span: Span) -> CowStr<'s> {
        span.of(self).into()
    }

    fn chars(&self) -> Self::Chars {
        str::chars(self)
    }
}

impl<'s> DiscontinuousString<'s> for InlineSpans<'s> {
    type Chars = InlineChars<'s, 'static>;

    /// Borrow if continuous, copy if discontiunous.
    fn src(&self, span: Span) -> CowStr<'s> {
        let mut a = 0;
        let mut s = String::new();
        for sp in &self.spans {
            let b = a + sp.len();
            if span.start() < b {
                let r = if a <= span.start() {
                    if span.end() <= b {
                        // continuous
                        return CowStr::Borrowed(
                            &sp.of(self.src)[span.start() - a..span.end() - a],
                        );
                    }
                    (span.start() - a)..sp.len()
                } else {
                    0..sp.len().min(span.end() - a)
                };
                s.push_str(&sp.of(self.src)[r]);
            }
            a = b;
        }
        assert_eq!(span.len(), s.len());
        CowStr::Owned(s)
    }

    fn chars(&self) -> Self::Chars {
        // SAFETY: do not call set_spans while chars is in use
        unsafe { std::mem::transmute(InlineChars::new(self.src, &self.spans)) }
    }
}

#[derive(Default)]
struct InlineSpans<'s> {
    src: &'s str,
    spans: Vec<Span>,
}

impl<'s> InlineSpans<'s> {
    fn new(src: &'s str) -> Self {
        Self {
            src,
            spans: Vec::new(),
        }
    }

    fn set_spans(&mut self, spans: impl Iterator<Item = Span>) {
        self.spans.clear();
        self.spans.extend(spans);
    }
}

pub struct Parser<'s> {
    src: &'s str,
    tree: block::Tree,
    inlines: InlineSpans<'s>,
    inline_parser: Option<inline::Parser<InlineChars<'s, 'static>>>,
    inline_start: usize,
    block_attributes: Attributes<'s>,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: block::parse(src),
            inlines: InlineSpans::new(src),
            inline_parser: None,
            inline_start: 0,
            block_attributes: Attributes::new(),
        }
    }
}

impl<'s> Parser<'s> {
    fn inline(&self, inline: inline::Event) -> Event<'s> {
        match inline.kind {
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
                    _ => todo!("{:?}", c),
                };
                if matches!(inline.kind, inline::EventKind::Enter(_)) {
                    Event::Start(t, Attributes::new())
                } else {
                    Event::End(t)
                }
            }
            inline::EventKind::Atom(a) => match a {
                inline::Atom::Ellipsis => Event::Atom(Atom::Ellipsis),
                inline::Atom::EnDash => Event::Atom(Atom::EnDash),
                inline::Atom::EmDash => Event::Atom(Atom::EmDash),
                inline::Atom::Nbsp => Event::Atom(Atom::NonBreakingSpace),
                inline::Atom::Softbreak => Event::Atom(Atom::Softbreak),
                inline::Atom::Hardbreak => Event::Atom(Atom::Hardbreak),
                inline::Atom::Escape => Event::Atom(Atom::Escape),
            },
            inline::EventKind::Str => Event::Str(self.inlines.src(inline.span)),
            inline::EventKind::Attributes => todo!(),
            inline::EventKind::AttributesDummy => panic!(),
        }
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(parser) = &mut self.inline_parser {
            if let Some(inline) = parser.next() {
                return Some(self.inline(inline));
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
                        self.block_attributes.parse(&content);
                        continue;
                    }
                },
                tree::EventKind::Enter(c) => match c {
                    block::Node::Leaf(l) => {
                        self.inlines.set_spans(self.tree.inlines());
                        self.inline_parser = Some(inline::Parser::new(self.inlines.chars()));
                        self.inline_start = ev.span.end();
                        let container = match l {
                            block::Leaf::CodeBlock { .. } => {
                                self.inline_start += 1; // skip newline
                                Container::CodeBlock {
                                    lang: (!ev.span.is_empty()).then(|| content),
                                }
                            }
                            _ => Container::from_leaf_block(content, l),
                        };
                        Event::Start(container, self.block_attributes.take())
                    }
                    block::Node::Container(c) => {
                        let container = match c {
                            block::Container::Div { .. } => Container::Div {
                                class: (!ev.span.is_empty()).then(|| content),
                            },
                            _ => Container::from_container_block(content, c),
                        };
                        Event::Start(container, self.block_attributes.take())
                    }
                },
                tree::EventKind::Exit(c) => match c {
                    block::Node::Leaf(l) => Event::End(Container::from_leaf_block(content, l)),
                    block::Node::Container(c) => {
                        Event::End(Container::from_container_block(content, c))
                    }
                },
                tree::EventKind::Inline => unreachable!(),
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
    use super::CowStr;
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
    fn attr_block() {
        test_parse!(
            "{.some_class}\npara\n",
            Start(Paragraph, [("class", "some_class")].into_iter().collect()),
            Str("para".into()),
            End(Paragraph),
        );
    }
}
