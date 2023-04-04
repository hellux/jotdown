//! A pull parser for [Djot](https://djot.net).
//!
//! The main entry is through [`Parser`] which implements an [`Iterator`] of [`Event`]s. The events
//! can then be used to traverse the document structure in order to e.g. construct an AST or
//! directly generate to some output format. This crate provides an [`html`] module that can be
//! used to render the events to HTML.
//!
//! # Feature flags
//!
//! - `html` (default): build the html module and a binary that converts djot to HTML.
//!
//! # Examples
//!
//! Generate HTML from Djot input:
//!
//! ```
//! # #[cfg(feature = "html")]
//! # {
//! use jotdown::Render;
//! let djot_input = "hello *world*!";
//! let events = jotdown::Parser::new(djot_input);
//! let mut html = String::new();
//! jotdown::html::Renderer::default().push(events, &mut html);
//! assert_eq!(html, "<p>hello <strong>world</strong>!</p>\n");
//! # }
//! ```
//!
//! Apply some filter to a specific type of element:
//!
//! ```
//! # #[cfg(feature = "html")]
//! # {
//! # use jotdown::Event;
//! # use jotdown::Container::Link;
//! # use jotdown::Render;
//! let events =
//!     jotdown::Parser::new("a [link](https://example.com)").map(|e| match e {
//!         Event::Start(Link(dst, ty), attrs) => {
//!             Event::Start(Link(dst.replace(".com", ".net").into(), ty), attrs)
//!         }
//!         e => e,
//!     });
//! let mut html = String::new();
//! jotdown::html::Renderer::default().push(events, &mut html);
//! assert_eq!(html, "<p>a <a href=\"https://example.net\">link</a></p>\n");
//! # }
//! ```

#![allow(clippy::blocks_in_if_conditions)]

use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io;

#[cfg(feature = "html")]
pub mod html;

mod attr;
mod block;
mod inline;
mod lex;
mod span;
mod tree;

use span::DiscontinuousString;
use span::Span;

pub use attr::{AttributeValue, AttributeValueParts, Attributes};

type CowStr<'s> = std::borrow::Cow<'s, str>;

/// A trait for rendering [`Event`]s to an output format.
///
/// The output can be written to either a [`std::fmt::Write`] or a [`std::io::Write`] object.
///
/// If ownership of the [`Event`]s cannot be given to the renderer, use [`Render::push_borrowed`]
/// or [`Render::write_borrowed`].
///
/// An implementor needs to at least implement the [`Render::render_event`] function that renders a
/// single event to the output. If anything needs to be rendered at the beginning or end of the
/// output, the [`Render::render_prologue`] and [`Render::render_epilogue`] can be implemented as
/// well.
///
/// # Examples
///
/// Push to a [`String`] (implements [`std::fmt::Write`]):
///
/// ```
/// # use jotdown::Render;
/// # let events = std::iter::empty();
/// let mut output = String::new();
/// let mut renderer = jotdown::html::Renderer::default();
/// renderer.push(events, &mut output);
/// ```
///
/// Write to standard output with buffering ([`std::io::Stdout`] implements [`std::io::Write`]):
///
/// ```
/// # use jotdown::Render;
/// # let events = std::iter::empty();
/// let mut out = std::io::BufWriter::new(std::io::stdout());
/// let mut renderer = jotdown::html::Renderer::default();
/// renderer.write(events, &mut out).unwrap();
/// ```
pub trait Render {
    /// Render a single event.
    fn render_event<'s, W>(&mut self, e: &Event<'s>, out: W) -> std::fmt::Result
    where
        W: std::fmt::Write;

    /// Render something before any events have been provided.
    ///
    /// This does nothing by default, but an implementation may choose to prepend data at the
    /// beginning of the output if needed.
    fn render_prologue<W>(&mut self, _out: W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        Ok(())
    }

    /// Render something after all events have been provided.
    ///
    /// This does nothing by default, but an implementation may choose to append extra data at the
    /// end of the output if needed.
    fn render_epilogue<W>(&mut self, _out: W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        Ok(())
    }

    /// Push owned [`Event`]s to a unicode-accepting buffer or stream.
    fn push<'s, I, W>(&mut self, mut events: I, mut out: W) -> fmt::Result
    where
        I: Iterator<Item = Event<'s>>,
        W: fmt::Write,
    {
        self.render_prologue(&mut out)?;
        events.try_for_each(|e| self.render_event(&e, &mut out))?;
        self.render_epilogue(&mut out)
    }

    /// Write owned [`Event`]s to a byte sink, encoded as UTF-8.
    ///
    /// NOTE: This performs many small writes, so IO writes should be buffered with e.g.
    /// [`std::io::BufWriter`].
    fn write<'s, I, W>(&mut self, events: I, out: W) -> io::Result<()>
    where
        I: Iterator<Item = Event<'s>>,
        W: io::Write,
    {
        let mut out = WriteAdapter {
            inner: out,
            error: Ok(()),
        };

        self.push(events, &mut out).map_err(|_| match out.error {
            Err(e) => e,
            _ => io::Error::new(io::ErrorKind::Other, "formatter error"),
        })
    }

    /// Push borrowed [`Event`]s to a unicode-accepting buffer or stream.
    ///
    /// # Examples
    ///
    /// Render a borrowed slice of [`Event`]s.
    /// ```
    /// # use jotdown::Render;
    /// # let events: &[jotdown::Event] = &[];
    /// let mut output = String::new();
    /// let mut renderer = jotdown::html::Renderer::default();
    /// renderer.push_borrowed(events.iter(), &mut output);
    /// ```
    fn push_borrowed<'s, E, I, W>(&mut self, mut events: I, mut out: W) -> fmt::Result
    where
        E: AsRef<Event<'s>>,
        I: Iterator<Item = E>,
        W: fmt::Write,
    {
        self.render_prologue(&mut out)?;
        events.try_for_each(|e| self.render_event(e.as_ref(), &mut out))?;
        self.render_epilogue(&mut out)
    }

    /// Write borrowed [`Event`]s to a byte sink, encoded as UTF-8.
    ///
    /// NOTE: This performs many small writes, so IO writes should be buffered with e.g.
    /// [`std::io::BufWriter`].
    fn write_borrowed<'s, E, I, W>(&mut self, events: I, out: W) -> io::Result<()>
    where
        E: AsRef<Event<'s>>,
        I: Iterator<Item = E>,
        W: io::Write,
    {
        let mut out = WriteAdapter {
            inner: out,
            error: Ok(()),
        };

        self.push_borrowed(events, &mut out)
            .map_err(|_| match out.error {
                Err(e) => e,
                _ => io::Error::new(io::ErrorKind::Other, "formatter error"),
            })
    }
}

struct WriteAdapter<T: io::Write> {
    inner: T,
    error: io::Result<()>,
}

impl<T: io::Write> fmt::Write for WriteAdapter<T> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.inner.write_all(s.as_bytes()).map_err(|e| {
            self.error = Err(e);
            fmt::Error
        })
    }
}

// XXX why is this not a blanket implementation?
impl<'s> AsRef<Event<'s>> for &Event<'s> {
    fn as_ref(&self) -> &Event<'s> {
        self
    }
}

/// A Djot event.
///
/// A Djot document is represented by a sequence of events. An element may consist of one or
/// multiple events. [`Container`] elements are represented by a [`Event::Start`] followed by
/// events representing its content, and finally a [`Event::End`]. Atomic elements without any
/// inside elements are represented by a single event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event<'s> {
    /// Start of a container.
    Start(Container<'s>, Attributes<'s>),
    /// End of a container.
    End(Container<'s>),
    /// A string object, text only.
    Str(CowStr<'s>),
    /// A footnote reference.
    FootnoteReference(&'s str, usize),
    /// A symbol, by default rendered literally but may be treated specially.
    Symbol(CowStr<'s>),
    /// Left single quotation mark.
    LeftSingleQuote,
    /// Right double quotation mark.
    RightSingleQuote,
    /// Left single quotation mark.
    LeftDoubleQuote,
    /// Right double quotation mark.
    RightDoubleQuote,
    /// A horizontal ellipsis, i.e. a set of three periods.
    Ellipsis,
    /// An en dash.
    EnDash,
    /// An em dash.
    EmDash,
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
    /// A thematic break, typically a horizontal rule.
    ThematicBreak(Attributes<'s>),
}

/// A container that may contain other elements.
///
/// There are three types of containers:
///
/// - inline, may only contain inline elements,
/// - block leaf, may only contain inline elements,
/// - block container, may contain any block-level elements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Container<'s> {
    /// A blockquote element.
    Blockquote,
    /// A list.
    List { kind: ListKind, tight: bool },
    /// An item of a list
    ListItem,
    /// An item of a task list, either checked or unchecked.
    TaskListItem { checked: bool },
    /// A description list element.
    DescriptionList,
    /// Details describing a term within a description list.
    DescriptionDetails,
    /// A footnote definition.
    Footnote { tag: &'s str, number: usize },
    /// A table element.
    Table,
    /// A row element of a table.
    TableRow { head: bool },
    /// A section belonging to a top level heading.
    Section { id: CowStr<'s> },
    /// A block-level divider element.
    Div { class: Option<&'s str> },
    /// A paragraph.
    Paragraph,
    /// A heading.
    Heading {
        level: u16,
        has_section: bool,
        id: CowStr<'s>,
    },
    /// A cell element of row within a table.
    TableCell { alignment: Alignment, head: bool },
    /// A caption within a table.
    Caption,
    /// A term within a description list.
    DescriptionTerm,
    /// A block with raw markup for a specific output format.
    RawBlock { format: &'s str },
    /// A block with code in a specific language.
    CodeBlock { lang: Option<&'s str> },
    /// An inline divider element.
    Span,
    /// An inline link, the first field is either a destination URL or an unresolved tag.
    Link(CowStr<'s>, LinkType),
    /// An inline image, the first field is either a destination URL or an unresolved tag. Inner
    /// Str objects compose the alternative text.
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
}

impl<'s> Container<'s> {
    /// Is a block element.
    #[must_use]
    pub fn is_block(&self) -> bool {
        match self {
            Self::Blockquote
            | Self::List { .. }
            | Self::ListItem
            | Self::TaskListItem { .. }
            | Self::DescriptionList
            | Self::DescriptionDetails
            | Self::Footnote { .. }
            | Self::Table
            | Self::TableRow { .. }
            | Self::Section { .. }
            | Self::Div { .. }
            | Self::Paragraph
            | Self::Heading { .. }
            | Self::TableCell { .. }
            | Self::Caption
            | Self::DescriptionTerm
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
            | Self::Mark => false,
        }
    }

    /// Is a block element that may contain children blocks.
    #[must_use]
    pub fn is_block_container(&self) -> bool {
        match self {
            Self::Blockquote
            | Self::List { .. }
            | Self::ListItem
            | Self::TaskListItem { .. }
            | Self::DescriptionList
            | Self::DescriptionDetails
            | Self::Footnote { .. }
            | Self::Table
            | Self::TableRow { .. }
            | Self::Section { .. }
            | Self::Div { .. } => true,
            Self::Paragraph
            | Self::Heading { .. }
            | Self::TableCell { .. }
            | Self::Caption
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
            | Self::Mark => false,
        }
    }
}

/// Alignment of a table column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Alignment {
    Unspecified,
    Left,
    Center,
    Right,
}

/// The type of an inline span link.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanLinkType {
    /// E.g. `[text](url)`
    Inline,
    /// In the form `[text][tag]` or `[tag][]`.
    Reference,
    /// Like reference, but the tag is unresolved.
    Unresolved,
}

/// The type of an inline link.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkType {
    /// E.g. `[text](url)`.
    Span(SpanLinkType),
    /// In the form `<url>`.
    AutoLink,
    /// In the form `<address>`.
    Email,
}

/// The type of a list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListKind {
    /// A bullet list.
    Unordered,
    /// An enumerated list.
    Ordered {
        numbering: OrderedListNumbering,
        style: OrderedListStyle,
        start: u64,
    },
    /// A task list.
    Task,
}

/// Numbering type of an ordered list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedListNumbering {
    /// Decimal numbering, e.g. `1)`.
    Decimal,
    /// Lowercase alphabetic numbering, e.g. `a)`.
    AlphaLower,
    /// Uppercase alphabetic numbering, e.g. `A)`.
    AlphaUpper,
    /// Lowercase roman or alphabetic numbering, e.g. `iv)`.
    RomanLower,
    /// Uppercase roman or alphabetic numbering, e.g. `IV)`.
    RomanUpper,
}

/// Style of an ordered list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedListStyle {
    /// Number is followed by a period, e.g. `1.`.
    Period,
    /// Number is followed by a closing parenthesis, e.g. `1)`.
    Paren,
    /// Number is enclosed by parentheses, e.g. `(1)`.
    ParenParen,
}

impl OrderedListNumbering {
    fn parse_number(self, n: &str) -> u64 {
        match self {
            Self::Decimal => n.parse().unwrap(),
            Self::AlphaLower | Self::AlphaUpper => {
                let d0 = u64::from(if matches!(self, Self::AlphaLower) {
                    b'a'
                } else {
                    b'A'
                });
                let weights = (1..=n.len()).scan(1, |a, _| {
                    let prev = *a;
                    *a *= 26;
                    Some(prev)
                });
                n.as_bytes()
                    .iter()
                    .rev()
                    .copied()
                    .map(u64::from)
                    .zip(weights)
                    .map(|(d, w)| w * (d - d0 + 1))
                    .sum()
            }
            Self::RomanLower | Self::RomanUpper => {
                fn value(d: char) -> u64 {
                    match d {
                        'i' | 'I' => 1,
                        'v' | 'V' => 5,
                        'x' | 'X' => 10,
                        'l' | 'L' => 50,
                        'c' | 'C' => 100,
                        'd' | 'D' => 500,
                        'm' | 'M' => 1000,
                        _ => panic!(),
                    }
                }
                let mut prev = 0;
                let mut sum = 0;
                for d in n.chars().rev() {
                    let v = value(d);
                    if v < prev {
                        sum -= v;
                    } else {
                        sum += v;
                    }
                    prev = v;
                }
                sum
            }
        }
    }
}

impl OrderedListStyle {
    fn number(self, marker: &str) -> &str {
        &marker[usize::from(matches!(self, Self::ParenParen))..marker.len() - 1]
    }
}

#[cfg(not(feature = "deterministic"))]
type Map<K, V> = std::collections::HashMap<K, V>;
#[cfg(feature = "deterministic")]
type Map<K, V> = std::collections::BTreeMap<K, V>;

#[cfg(not(feature = "deterministic"))]
type Set<T> = std::collections::HashSet<T>;
#[cfg(feature = "deterministic")]
type Set<T> = std::collections::BTreeSet<T>;

/// A parser that generates [`Event`]s from a Djot document.
///
/// When created, it will perform an initial pass and build up a tree of the document's block
/// structure that will be kept for the duration of the parser's lifetime. Then, when the iterator
/// is advanced, the parser will start from the beginning of the document and parse inline elements
/// and emit [`Event`]s.
pub struct Parser<'s> {
    src: &'s str,

    /// Block tree parsed at first.
    tree: block::Tree,

    /// Contents obtained by the prepass.
    pre_pass: PrePass<'s>,

    /// Last parsed block attributes
    block_attributes: Attributes<'s>,

    /// Current table row is a head row.
    table_head_row: bool,

    /// Footnote references in the order they were encountered, without duplicates.
    footnote_references: Vec<&'s str>,
    /// Cache of footnotes to emit at the end.
    footnotes: Map<&'s str, block::Tree>,
    /// Next or current footnote being parsed and emitted.
    footnote_index: usize,
    /// Currently within a footnote.
    footnote_active: bool,

    /// Spans to the inlines in the leaf block currently being parsed.
    inlines: span::InlineSpans<'s>,
    /// Inline parser, recreated for each new inline.
    inline_parser: Option<inline::Parser<span::InlineCharsIter<'s>>>,
}

struct Heading {
    /// Location of heading in src.
    location: usize,
    /// Automatically generated id from heading text.
    id_auto: String,
    /// Overriding id from an explicit attribute on the heading.
    id_override: Option<String>,
}

/// Because of potential future references, an initial pass is required to obtain all definitions.
struct PrePass<'s> {
    /// Link definitions and their attributes.
    link_definitions: Map<&'s str, (CowStr<'s>, attr::Attributes<'s>)>,
    /// Cache of all heading ids.
    headings: Vec<Heading>,
    /// Indices to headings sorted lexicographically.
    headings_lex: Vec<usize>,
}

impl<'s> PrePass<'s> {
    #[must_use]
    fn new(src: &'s str, mut tree: block::Tree) -> Self {
        let mut link_definitions = Map::new();
        let mut headings: Vec<Heading> = Vec::new();
        let mut used_ids: Set<&str> = Set::new();

        let mut inlines = span::InlineSpans::new(src);

        let mut attr_prev: Option<Span> = None;
        while let Some(e) = tree.next() {
            match e.kind {
                tree::EventKind::Enter(block::Node::Leaf(block::Leaf::LinkDefinition)) => {
                    // All link definition tags have to be obtained initially, as references can
                    // appear before the definition.
                    let tag = e.span.of(src);
                    let attrs =
                        attr_prev.map_or_else(Attributes::new, |sp| attr::parse(sp.of(src)));
                    let url = match tree.count_children() {
                        0 => "".into(),
                        1 => tree.take_inlines().next().unwrap().of(src).trim().into(),
                        _ => tree.take_inlines().map(|sp| sp.of(src).trim()).collect(),
                    };
                    link_definitions.insert(tag, (url, attrs));
                }
                tree::EventKind::Enter(block::Node::Leaf(block::Leaf::Heading { .. })) => {
                    // All headings ids have to be obtained initially, as references can appear
                    // before the heading. Additionally, determining the id requires inline parsing
                    // as formatting must be removed.
                    //
                    // We choose to parse all headers twice instead of caching them.
                    let attrs = attr_prev.map(|sp| attr::parse(sp.of(src)));
                    let id_override = attrs
                        .as_ref()
                        .and_then(|attrs| attrs.get("id"))
                        .map(ToString::to_string);

                    inlines.set_spans(tree.take_inlines());
                    let mut id_auto = String::new();
                    let mut last_whitespace = true;
                    inline::Parser::new(inlines.chars()).for_each(|ev| match ev.kind {
                        inline::EventKind::Str => {
                            let mut chars = inlines.slice(ev.span).chars().peekable();
                            while let Some(c) = chars.next() {
                                if c.is_whitespace() {
                                    while chars.peek().map_or(false, |c| c.is_whitespace()) {
                                        chars.next();
                                    }
                                    if !last_whitespace {
                                        last_whitespace = true;
                                        id_auto.push('-');
                                    }
                                } else if !c.is_ascii_punctuation() || matches!(c, '-' | '_') {
                                    id_auto.push(c);
                                    last_whitespace = false;
                                }
                            }
                        }
                        inline::EventKind::Atom(inline::Atom::Softbreak) => {
                            id_auto.push('-');
                        }
                        _ => {}
                    });
                    id_auto.drain(id_auto.trim_end_matches('-').len()..);

                    // ensure id unique
                    if used_ids.contains::<str>(&id_auto) || id_auto.is_empty() {
                        if id_auto.is_empty() {
                            id_auto.push('s');
                        }
                        let mut num = 1;
                        id_auto.push('-');
                        let i_num = id_auto.len();
                        write!(id_auto, "{}", num).unwrap();
                        while used_ids.contains::<str>(&id_auto) {
                            num += 1;
                            id_auto.drain(i_num..);
                            write!(id_auto, "{}", num).unwrap();
                        }
                    }

                    // SAFETY: used_ids is dropped before the id_auto strings in headings. even if
                    // the strings move due to headings reallocating, the string data on the heap
                    // will not move
                    used_ids.insert(unsafe {
                        std::mem::transmute::<&str, &'static str>(id_auto.as_ref())
                    });
                    headings.push(Heading {
                        location: e.span.start(),
                        id_auto,
                        id_override,
                    });
                }
                tree::EventKind::Atom(block::Atom::Attributes) => {
                    attr_prev = Some(e.span);
                }
                tree::EventKind::Enter(..)
                | tree::EventKind::Exit(block::Node::Container(block::Container::Section {
                    ..
                })) => {}
                _ => {
                    attr_prev = None;
                }
            }
        }

        let mut headings_lex = (0..headings.len()).collect::<Vec<_>>();
        headings_lex.sort_by_key(|i| &headings[*i].id_auto);

        Self {
            link_definitions,
            headings,
            headings_lex,
        }
    }

    fn heading_id(&self, i: usize) -> &str {
        let h = &self.headings[i];
        h.id_override.as_ref().unwrap_or(&h.id_auto)
    }

    fn heading_id_by_location(&self, location: usize) -> Option<&str> {
        self.headings
            .binary_search_by_key(&location, |h| h.location)
            .ok()
            .map(|i| self.heading_id(i))
    }

    fn heading_id_by_tag(&self, tag: &str) -> Option<&str> {
        self.headings_lex
            .binary_search_by_key(&tag, |i| &self.headings[*i].id_auto)
            .ok()
            .map(|i| self.heading_id(i))
    }
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        let tree = block::parse(src);
        let pre_pass = PrePass::new(src, tree.clone());

        Self {
            src,
            tree,
            pre_pass,
            block_attributes: Attributes::new(),
            table_head_row: false,
            footnote_references: Vec::new(),
            footnotes: Map::new(),
            footnote_index: 0,
            footnote_active: false,
            inlines: span::InlineSpans::new(src),
            inline_parser: None,
        }
    }

    fn inline(&mut self) -> Option<Event<'s>> {
        self.inline_parser.as_mut().and_then(|parser| {
            let mut inline = parser.next();

            let mut first_is_attr = false;
            let mut attributes = inline.as_ref().map_or_else(Attributes::new, |inl| {
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
                        inline::Container::ReferenceLink | inline::Container::ReferenceImage => {
                            let tag = match self.inlines.src(inline.span) {
                                CowStr::Owned(s) => s.replace('\n', " ").into(),
                                s @ CowStr::Borrowed(_) => s,
                            };
                            let link_def =
                                self.pre_pass.link_definitions.get(tag.as_ref()).cloned();

                            let (url_or_tag, ty) = if let Some((url, attrs_def)) = link_def {
                                attributes.union(attrs_def);
                                (url, SpanLinkType::Reference)
                            } else {
                                self.pre_pass.heading_id_by_tag(tag.as_ref()).map_or_else(
                                    || (tag, SpanLinkType::Unresolved),
                                    |id| (format!("#{}", id).into(), SpanLinkType::Reference),
                                )
                            };

                            if matches!(c, inline::Container::ReferenceLink) {
                                Container::Link(url_or_tag, LinkType::Span(ty))
                            } else {
                                Container::Image(url_or_tag, ty)
                            }
                        }
                        inline::Container::Autolink => {
                            let url = self.inlines.src(inline.span);
                            let ty = if url.contains('@') {
                                LinkType::Email
                            } else {
                                LinkType::AutoLink
                            };
                            Container::Link(url, ty)
                        }
                    };
                    if matches!(inline.kind, inline::EventKind::Enter(_)) {
                        Event::Start(t, attributes)
                    } else {
                        Event::End(t)
                    }
                }
                inline::EventKind::Atom(a) => match a {
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
                        Event::FootnoteReference(
                            match self.inlines.src(inline.span) {
                                CowStr::Borrowed(s) => s,
                                CowStr::Owned(..) => panic!(),
                            },
                            number,
                        )
                    }
                    inline::Atom::Symbol => Event::Symbol(self.inlines.src(inline.span)),
                    inline::Atom::Quote { ty, left } => match (ty, left) {
                        (inline::QuoteType::Single, true) => Event::LeftSingleQuote,
                        (inline::QuoteType::Single, false) => Event::RightSingleQuote,
                        (inline::QuoteType::Double, true) => Event::LeftDoubleQuote,
                        (inline::QuoteType::Double, false) => Event::RightDoubleQuote,
                    },
                    inline::Atom::Ellipsis => Event::Ellipsis,
                    inline::Atom::EnDash => Event::EnDash,
                    inline::Atom::EmDash => Event::EmDash,
                    inline::Atom::Nbsp => Event::NonBreakingSpace,
                    inline::Atom::Softbreak => Event::Softbreak,
                    inline::Atom::Hardbreak => Event::Hardbreak,
                    inline::Atom::Escape => Event::Escape,
                },
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
        while let Some(ev) = &mut self.tree.next() {
            let content = ev.span.of(self.src);
            let event = match ev.kind {
                tree::EventKind::Atom(a) => match a {
                    block::Atom::Blankline => Event::Blankline,
                    block::Atom::ThematicBreak => {
                        Event::ThematicBreak(self.block_attributes.take())
                    }
                    block::Atom::Attributes => {
                        self.block_attributes.parse(content);
                        continue;
                    }
                },
                tree::EventKind::Enter(c) | tree::EventKind::Exit(c) => {
                    let enter = matches!(ev.kind, tree::EventKind::Enter(..));
                    let cont = match c {
                        block::Node::Leaf(l) => {
                            if matches!(l, block::Leaf::LinkDefinition) {
                                // ignore link definitions
                                if enter {
                                    self.tree.take_inlines().last();
                                }
                                self.block_attributes = Attributes::new();
                                continue;
                            }
                            if enter && !matches!(l, block::Leaf::CodeBlock) {
                                self.inlines.set_spans(self.tree.take_inlines());
                                self.inline_parser =
                                    Some(inline::Parser::new(self.inlines.chars()));
                            }
                            match l {
                                block::Leaf::Paragraph => Container::Paragraph,
                                block::Leaf::Heading { has_section } => Container::Heading {
                                    level: content.len().try_into().unwrap(),
                                    has_section,
                                    id: self
                                        .pre_pass
                                        .heading_id_by_location(ev.span.start())
                                        .unwrap_or_default()
                                        .to_string()
                                        .into(),
                                },
                                block::Leaf::DescriptionTerm => Container::DescriptionTerm,
                                block::Leaf::CodeBlock => {
                                    if let Some(format) = content.strip_prefix('=') {
                                        Container::RawBlock { format }
                                    } else {
                                        Container::CodeBlock {
                                            lang: (!content.is_empty()).then(|| content),
                                        }
                                    }
                                }
                                block::Leaf::TableCell(alignment) => Container::TableCell {
                                    alignment,
                                    head: self.table_head_row,
                                },
                                block::Leaf::Caption => Container::Caption,
                                block::Leaf::LinkDefinition => unreachable!(),
                            }
                        }
                        block::Node::Container(c) => match c {
                            block::Container::Blockquote => Container::Blockquote,
                            block::Container::Div { .. } => Container::Div {
                                class: (!ev.span.is_empty()).then(|| content),
                            },
                            block::Container::Footnote => {
                                assert!(enter);
                                self.footnotes.insert(content, self.tree.take_branch());
                                self.block_attributes = Attributes::new();
                                continue;
                            }
                            block::Container::List(block::ListKind { ty, tight }) => {
                                if matches!(ty, block::ListType::Description) {
                                    Container::DescriptionList
                                } else {
                                    let kind = match ty {
                                        block::ListType::Unordered(..) => ListKind::Unordered,
                                        block::ListType::Task => ListKind::Task,
                                        block::ListType::Ordered(numbering, style) => {
                                            let start = numbering
                                                .parse_number(style.number(content))
                                                .max(1);
                                            ListKind::Ordered {
                                                numbering,
                                                style,
                                                start,
                                            }
                                        }
                                        block::ListType::Description => unreachable!(),
                                    };
                                    Container::List { kind, tight }
                                }
                            }
                            block::Container::ListItem(ty) => match ty {
                                block::ListType::Task => Container::TaskListItem {
                                    checked: content.as_bytes()[3] != b' ',
                                },
                                block::ListType::Description => Container::DescriptionDetails,
                                _ => Container::ListItem,
                            },
                            block::Container::Table => Container::Table,
                            block::Container::TableRow { head } => {
                                if enter {
                                    self.table_head_row = head;
                                }
                                Container::TableRow { head }
                            }
                            block::Container::Section => Container::Section {
                                id: self
                                    .pre_pass
                                    .heading_id_by_location(ev.span.start())
                                    .unwrap_or_default()
                                    .to_string()
                                    .into(),
                            },
                        },
                    };
                    if enter {
                        Event::Start(cont, self.block_attributes.take())
                    } else {
                        Event::End(cont)
                    }
                }
                tree::EventKind::Inline => Event::Str(content.into()), // verbatim
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
                .unwrap_or_else(block::Tree::empty);
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
    use super::Attributes;
    use super::Container::*;
    use super::Event::*;
    use super::LinkType;
    use super::ListKind;
    use super::OrderedListNumbering::*;
    use super::OrderedListStyle::*;
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
            Start(Section { id: "s-1".into() }, Attributes::new()),
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "s-1".into()
                },
                Attributes::new()
            ),
            End(Heading {
                level: 1,
                has_section: true,
                id: "s-1".into()
            }),
            End(Section { id: "s-1".into() }),
        );
        test_parse!(
            "# abc\ndef\n",
            Start(
                Section {
                    id: "abc-def".into()
                },
                Attributes::new()
            ),
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "abc-def".into()
                },
                Attributes::new()
            ),
            Str("abc".into()),
            Softbreak,
            Str("def".into()),
            End(Heading {
                level: 1,
                has_section: true,
                id: "abc-def".into(),
            }),
            End(Section {
                id: "abc-def".into()
            }),
        );
    }

    #[test]
    fn heading_attr() {
        test_parse!(
            concat!(
                "# abc\n",
                "{a=b}\n",
                "# def\n", //
            ),
            Start(Section { id: "abc".into() }, Attributes::new()),
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "abc".into()
                },
                Attributes::new()
            ),
            Str("abc".into()),
            End(Heading {
                level: 1,
                has_section: true,
                id: "abc".into(),
            }),
            End(Section { id: "abc".into() }),
            Start(
                Section { id: "def".into() },
                [("a", "b")].into_iter().collect(),
            ),
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "def".into()
                },
                Attributes::new(),
            ),
            Str("def".into()),
            End(Heading {
                level: 1,
                has_section: true,
                id: "def".into(),
            }),
            End(Section { id: "def".into() }),
        );
    }

    #[test]
    fn blockquote() {
        test_parse!(
            ">\n",
            Start(Blockquote, Attributes::new()),
            Blankline,
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
            Blankline,
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
            Str("<table>\n".into()),
            End(RawBlock { format: "html" }),
        );
    }

    #[test]
    fn symbol() {
        test_parse!(
            "abc :+1: def",
            Start(Paragraph, Attributes::new()),
            Str("abc ".into()),
            Symbol("+1".into()),
            Str(" def".into()),
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
            Blankline,
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
            Blankline,
        );
    }

    #[test]
    fn link_reference_unresolved() {
        test_parse!(
            "[text][tag]",
            Start(Paragraph, Attributes::new()),
            Start(
                Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved))),
            End(Paragraph),
        );
        test_parse!(
            "![text][tag]",
            Start(Paragraph, Attributes::new()),
            Start(
                Image("tag".into(), SpanLinkType::Unresolved),
                Attributes::new()
            ),
            Str("text".into()),
            End(Image("tag".into(), SpanLinkType::Unresolved)),
            End(Paragraph),
        );
    }

    #[test]
    fn link_reference_multiline() {
        test_parse!(
            concat!(
                "> [text][a\n", //
                "> b]\n",       //
                "\n",           //
                "[a b]: url\n", //
            ),
            Start(Blockquote, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new()
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            End(Paragraph),
            End(Blockquote),
            Blankline,
        );
    }

    #[test]
    fn link_definition_multiline() {
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
            Blankline,
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
            Blankline,
        );
    }

    #[test]
    fn link_reference_attrs() {
        test_parse!(
            concat!(
                "[text][tag]{b=c}\n",
                "\n",
                "{a=b}\n",
                "[tag]: url\n",
                "para\n",
            ),
            Start(Paragraph, Attributes::new()),
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                [("b", "c"), ("a", "b")].into_iter().collect(),
            ),
            Str("text".into()),
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            End(Paragraph),
            Blankline,
            Start(Paragraph, Attributes::new()),
            Str("para".into()),
            End(Paragraph),
        );
    }

    #[test]
    fn footnote_references() {
        test_parse!(
            "[^a][^b][^c]",
            Start(Paragraph, Attributes::new()),
            FootnoteReference("a", 1),
            FootnoteReference("b", 2),
            FootnoteReference("c", 3),
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
            FootnoteReference("a", 1),
            End(Paragraph),
            Blankline,
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
            FootnoteReference("a", 1),
            End(Paragraph),
            Blankline,
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
            Blankline,
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
            FootnoteReference("a", 1),
            End(Paragraph),
            Blankline,
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

    #[test]
    fn attr_inline_multiline() {
        test_parse!(
            concat!(
                "> _abc_{a=b\n", //
                "> c=d}\n",      //
            ),
            Start(Blockquote, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Start(Emphasis, [("a", "b"), ("c", "d")].into_iter().collect()),
            Str("abc".into()),
            End(Emphasis),
            End(Paragraph),
            End(Blockquote),
        );
    }

    #[test]
    fn list_item_unordered() {
        test_parse!(
            "- abc",
            Start(
                List {
                    kind: ListKind::Unordered,
                    tight: true,
                },
                Attributes::new(),
            ),
            Start(ListItem, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Str("abc".into()),
            End(Paragraph),
            End(ListItem),
            End(List {
                kind: ListKind::Unordered,
                tight: true,
            }),
        );
    }

    #[test]
    fn list_item_ordered_decimal() {
        test_parse!(
            "123. abc",
            Start(
                List {
                    kind: ListKind::Ordered {
                        numbering: Decimal,
                        style: Period,
                        start: 123
                    },
                    tight: true,
                },
                Attributes::new(),
            ),
            Start(ListItem, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Str("abc".into()),
            End(Paragraph),
            End(ListItem),
            End(List {
                kind: ListKind::Ordered {
                    numbering: Decimal,
                    style: Period,
                    start: 123
                },
                tight: true,
            }),
        );
    }

    #[test]
    fn list_task() {
        test_parse!(
            concat!(
                "- [ ] a\n", //
                "- [x] b\n", //
                "- [X] c\n", //
            ),
            Start(
                List {
                    kind: ListKind::Task,
                    tight: true,
                },
                Attributes::new(),
            ),
            Start(TaskListItem { checked: false }, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Str("a".into()),
            End(Paragraph),
            End(TaskListItem { checked: false }),
            Start(TaskListItem { checked: true }, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Str("b".into()),
            End(Paragraph),
            End(TaskListItem { checked: true }),
            Start(TaskListItem { checked: true }, Attributes::new()),
            Start(Paragraph, Attributes::new()),
            Str("c".into()),
            End(Paragraph),
            End(TaskListItem { checked: true }),
            End(List {
                kind: ListKind::Task,
                tight: true,
            }),
        );
    }

    #[test]
    fn numbering_alpha() {
        assert_eq!(AlphaLower.parse_number("a"), 1);
        assert_eq!(AlphaUpper.parse_number("B"), 2);
        assert_eq!(AlphaUpper.parse_number("Z"), 26);
        assert_eq!(AlphaLower.parse_number("aa"), 27);
    }
}
