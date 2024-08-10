//! A pull parser for [Djot](https://djot.net).
//!
//! The main entry is through [`Parser`] which constructs an [`Iterator`] of [`Event`]s. The events
//! can then be processed before rendering them via the [`Render`] trait. This crate provides an
//! [`html`] module that implements an HTML renderer.
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
//! let djot_input = "hello *world*!";
//! let events = jotdown::Parser::new(djot_input);
//! let html = jotdown::html::render_to_string(events);
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
//! let events =
//!     jotdown::Parser::new("a [link](https://example.com)").map(|e| match e {
//!         Event::Start(Link(dst, ty), attrs) => {
//!             Event::Start(Link(dst.replace(".com", ".net").into(), ty), attrs)
//!         }
//!         e => e,
//!     });
//! let html = jotdown::html::render_to_string(events);
//! assert_eq!(html, "<p>a <a href=\"https://example.net\">link</a></p>\n");
//! # }
//! ```

#![allow(clippy::blocks_in_conditions)]

use std::fmt;
use std::fmt::Write as FmtWrite;
use std::io;
use std::ops::Range;

#[cfg(feature = "html")]
pub mod html;

mod attr;
mod block;
mod inline;
mod lex;

pub use attr::{
    AttributeValue, AttributeValueParts, Attributes, AttributesIntoIter, AttributesIter,
    AttributesIterMut, ParseAttributesError,
};

type CowStr<'s> = std::borrow::Cow<'s, str>;

/// A trait for rendering [`Event`]s to an output format.
///
/// The output can be written to either a [`std::fmt::Write`] or a [`std::io::Write`] object.
///
/// If ownership of the [`Event`]s cannot be given to the renderer, refer to the [`RenderRef`]
/// trait instead.
///
/// # Examples
///
/// Push to a [`String`] (implements [`std::fmt::Write`]):
///
/// ```
/// # #[cfg(feature = "html")]
/// # {
/// # use jotdown::Render;
/// # let events = std::iter::empty();
/// let mut output = String::new();
/// let renderer = jotdown::html::Renderer::default();
/// renderer.push(events, &mut output);
/// # }
/// ```
///
/// Write to standard output with buffering ([`std::io::Stdout`] implements [`std::io::Write`]):
///
/// ```
/// # #[cfg(feature = "html")]
/// # {
/// # use jotdown::Render;
/// # let events = std::iter::empty();
/// let mut out = std::io::BufWriter::new(std::io::stdout());
/// let renderer = jotdown::html::Renderer::default();
/// renderer.write(events, &mut out).unwrap();
/// # }
/// ```
pub trait Render {
    /// Push owned [`Event`]s to a unicode-accepting buffer or stream.
    fn push<'s, I, W>(&self, events: I, out: W) -> fmt::Result
    where
        I: Iterator<Item = Event<'s>>,
        W: fmt::Write;

    /// Write owned [`Event`]s to a byte sink, encoded as UTF-8.
    ///
    /// NOTE: This performs many small writes, so IO writes should be buffered with e.g.
    /// [`std::io::BufWriter`].
    fn write<'s, I, W>(&self, events: I, out: W) -> io::Result<()>
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
}

/// A trait for rendering borrowed [`Event`]s to an output format.
///
/// The output can be written to either a [`std::fmt::Write`] or a [`std::io::Write`] object.
///
/// If ownership of the [`Event`]s can be given to the renderer, refer to the [`Render`] trait
/// instead.
pub trait RenderRef {
    /// Push borrowed [`Event`]s to a unicode-accepting buffer or stream.
    ///
    /// # Examples
    ///
    /// Render a borrowed slice of [`Event`]s.
    /// ```
    /// # #[cfg(feature = "html")]
    /// # {
    /// # use jotdown::RenderRef;
    /// # let events: &[jotdown::Event] = &[];
    /// let mut output = String::new();
    /// let renderer = jotdown::html::Renderer::default();
    /// renderer.push_ref(events.iter(), &mut output);
    /// # }
    /// ```
    fn push_ref<'s, E, I, W>(&self, events: I, out: W) -> fmt::Result
    where
        E: AsRef<Event<'s>>,
        I: Iterator<Item = E>,
        W: fmt::Write;

    /// Write borrowed [`Event`]s to a byte sink, encoded as UTF-8.
    ///
    /// NOTE: This performs many small writes, so IO writes should be buffered with e.g.
    /// [`std::io::BufWriter`].
    fn write_ref<'s, E, I, W>(&self, events: I, out: W) -> io::Result<()>
    where
        E: AsRef<Event<'s>>,
        I: Iterator<Item = E>,
        W: io::Write,
    {
        let mut out = WriteAdapter {
            inner: out,
            error: Ok(()),
        };

        self.push_ref(events, &mut out)
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
    FootnoteReference(&'s str),
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
    Footnote { label: &'s str },
    /// A table element.
    Table,
    /// A row element of a table.
    TableRow { head: bool },
    /// A section belonging to a top level heading.
    Section { id: CowStr<'s> },
    /// A block-level divider element.
    Div { class: &'s str },
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
    /// A link definition.
    LinkDefinition { label: &'s str },
    /// A block with raw markup for a specific output format.
    RawBlock { format: &'s str },
    /// A block with code in a specific language.
    CodeBlock { language: &'s str },
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
            | Self::LinkDefinition { .. }
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
            | Self::LinkDefinition { .. }
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
///
/// It is possible to clone the parser to e.g. avoid performing the block parsing multiple times.
#[derive(Clone)]
pub struct Parser<'s> {
    src: &'s str,

    /// Block tree parsed at first.
    blocks: std::iter::Peekable<std::vec::IntoIter<block::Event<'s>>>,

    /// Contents obtained by the prepass.
    pre_pass: PrePass<'s>,

    /// Last parsed block attributes, and its starting offset.
    block_attributes: Attributes<'s>,
    block_attributes_pos: Option<usize>,

    /// Current table row is a head row.
    table_head_row: bool,

    /// Currently within a verbatim code block.
    verbatim: bool,

    /// Inline parser.
    inline_parser: inline::Parser<'s>,
}

#[derive(Clone)]
struct Heading {
    /// Location of heading in src.
    location: u32,
    /// Automatically generated id from heading text.
    id_auto: String,
    /// Text of heading, formatting stripped.
    text: String,
    /// Overriding id from an explicit attribute on the heading.
    id_override: Option<String>,
}

/// Because of potential future references, an initial pass is required to obtain all definitions.
#[derive(Clone)]
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
    fn new(
        src: &'s str,
        mut blocks: std::slice::Iter<block::Event<'s>>,
        inline_parser: &mut inline::Parser<'s>,
    ) -> Self {
        let mut link_definitions = Map::new();
        let mut headings: Vec<Heading> = Vec::new();
        let mut used_ids: Set<String> = Set::new();

        let mut attr_prev: Option<Range<usize>> = None;
        while let Some(e) = blocks.next() {
            match e.kind {
                block::EventKind::Enter(block::Node::Leaf(block::Leaf::LinkDefinition {
                    label,
                })) => {
                    // All link definition tags have to be obtained initially, as references can
                    // appear before the definition.
                    let attrs = attr_prev.as_ref().map_or_else(Attributes::new, |sp| {
                        src[sp.clone()].try_into().expect("should be valid")
                    });
                    let url = if let Some(block::Event {
                        kind: block::EventKind::Inline,
                        span,
                    }) = blocks.next()
                    {
                        let start =
                            src[span.clone()].trim_matches(|c: char| c.is_ascii_whitespace());
                        if let Some(block::Event {
                            kind: block::EventKind::Inline,
                            span,
                        }) = blocks.next()
                        {
                            let mut url = start.to_string();
                            url.push_str(
                                src[span.clone()].trim_matches(|c: char| c.is_ascii_whitespace()),
                            );
                            while let Some(block::Event {
                                kind: block::EventKind::Inline,
                                span,
                            }) = blocks.next()
                            {
                                url.push_str(
                                    src[span.clone()]
                                        .trim_matches(|c: char| c.is_ascii_whitespace()),
                                );
                            }
                            url.into() // owned
                        } else {
                            start.into() // borrowed
                        }
                    } else {
                        "".into() // static
                    };
                    link_definitions.insert(label, (url, attrs));
                }
                block::EventKind::Enter(block::Node::Leaf(block::Leaf::Heading { .. })) => {
                    // All headings ids have to be obtained initially, as references can appear
                    // before the heading. Additionally, determining the id requires inline parsing
                    // as formatting must be removed.
                    //
                    // We choose to parse all headers twice instead of caching them.
                    let attrs = attr_prev
                        .as_ref()
                        .map(|sp| Attributes::try_from(&src[sp.clone()]).expect("should be valid"));
                    let id_override = attrs
                        .as_ref()
                        .and_then(|attrs| attrs.get("id"))
                        .map(ToString::to_string);

                    let mut id_auto = String::new();
                    let mut text = String::new();
                    let mut last_whitespace = true;
                    inline_parser.reset();
                    let mut last_end = 0;
                    loop {
                        let span_inline = blocks.next().and_then(|e| {
                            if matches!(e.kind, block::EventKind::Inline) {
                                last_end = e.span.end;
                                Some(e.span.clone())
                            } else {
                                None
                            }
                        });
                        inline_parser.feed_line(
                            span_inline.as_ref().cloned().unwrap_or(last_end..last_end),
                            span_inline.is_none(),
                        );
                        inline_parser.for_each(|ev| match ev.kind {
                            inline::EventKind::Str => {
                                text.push_str(&src[ev.span.clone()]);
                                let mut chars = src[ev.span].chars().peekable();
                                while let Some(c) = chars.next() {
                                    if c.is_ascii_whitespace() {
                                        while chars
                                            .peek()
                                            .map_or(false, |c| c.is_ascii_whitespace())
                                        {
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
                                text.push(' ');
                                id_auto.push('-');
                            }
                            _ => {}
                        });
                        if span_inline.is_none() {
                            break;
                        }
                    }
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

                    used_ids.insert(id_auto.clone());
                    headings.push(Heading {
                        location: e.span.start as u32,
                        id_auto,
                        text,
                        id_override,
                    });
                }
                block::EventKind::Atom(block::Atom::Attributes) => {
                    attr_prev = Some(e.span.clone());
                }
                block::EventKind::Enter(..)
                | block::EventKind::Exit(block::Node::Container(block::Container::Section {
                    ..
                })) => {}
                _ => {
                    attr_prev = None;
                }
            }
        }

        let mut headings_lex = (0..headings.len()).collect::<Vec<_>>();
        headings_lex.sort_by_key(|i| &headings[*i].text);

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

    fn heading_id_by_location(&self, location: u32) -> Option<&str> {
        self.headings
            .binary_search_by_key(&location, |h| h.location)
            .ok()
            .map(|i| self.heading_id(i))
    }

    fn heading_id_by_tag(&self, tag: &str) -> Option<&str> {
        self.headings_lex
            .binary_search_by_key(&tag, |i| &self.headings[*i].text)
            .ok()
            .map(|i| self.heading_id(self.headings_lex[i]))
    }
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        let blocks = block::parse(src);
        let mut inline_parser = inline::Parser::new(src);
        let pre_pass = PrePass::new(src, blocks.iter(), &mut inline_parser);

        Self {
            src,
            blocks: blocks.into_iter().peekable(),
            pre_pass,
            block_attributes: Attributes::new(),
            block_attributes_pos: None,
            table_head_row: false,
            verbatim: false,
            inline_parser,
        }
    }

    /// Turn the [`Parser`] into an iterator of tuples, each with an [`Event`] and a start/end byte
    /// offset for its corresponding input (as a [`Range<usize>`]).
    ///
    /// Generally, the range of each event does not overlap with any other event and the ranges are
    /// in same order as the events are emitted, i.e. the start offset of an event must be greater
    /// or equal to the (exclusive) end offset of all events that were emitted before that event.
    /// However, there are some exceptions to this rule:
    ///
    /// - Blank lines inbetween block attributes and the block causes the blankline events to
    ///   overlap with the block start event.
    /// - Caption events are emitted before the table rows while the input for the caption content
    ///   is located after the table rows, causing the ranges to be out of order.
    ///
    /// Characters between events, that are not part of any event range, are typically whitespace
    /// but may also consist of unattached attributes or `>` characters from blockquotes.
    ///
    /// # Examples
    ///
    /// Start and end events of containers correspond only to the start and end markers for that
    /// container, not its inner content:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::Event::*;
    /// # use jotdown::Container::*;
    /// let input = "> _hello_ [text](url)\n";
    /// assert!(matches!(
    ///     Parser::new(input)
    ///         .into_offset_iter()
    ///         .map(|(e, r)| (&input[r], e))
    ///         .collect::<Vec<_>>()
    ///         .as_slice(),
    ///     &[
    ///         (">", Start(Blockquote, ..)),
    ///         ("", Start(Paragraph, ..)),
    ///         ("_", Start(Emphasis, ..)),
    ///         ("hello", Str(..)),
    ///         ("_", End(Emphasis)),
    ///         (" ", Str(..)),
    ///         ("[", Start(Link { .. }, ..)),
    ///         ("text", Str(..)),
    ///         ("](url)", End(Link { .. })),
    ///         ("", End(Paragraph)),
    ///         ("", End(Blockquote)),
    ///     ],
    /// ));
    /// ```
    ///
    /// _Block_ attributes that belong to a container are included in the  _start_ event.  _Inline_
    /// attributes that belong to a container are included in the _end_ event:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::Event::*;
    /// # use jotdown::Container::*;
    /// let input = "
    /// {.quote}
    /// > [Hello]{lang=en} world!";
    /// assert!(matches!(
    ///     Parser::new(input)
    ///         .into_offset_iter()
    ///         .map(|(e, r)| (&input[r], e))
    ///         .collect::<Vec<_>>()
    ///         .as_slice(),
    ///     &[
    ///         ("\n", Blankline),
    ///         ("{.quote}\n>", Start(Blockquote, ..)),
    ///         ("", Start(Paragraph, ..)),
    ///         ("[", Start(Span, ..)),
    ///         ("Hello", Str(..)),
    ///         ("]{lang=en}", End(Span)),
    ///         (" world!", Str(..)),
    ///         ("", End(Paragraph)),
    ///         ("", End(Blockquote)),
    ///     ],
    /// ));
    /// ```
    ///
    /// Inline events that span multiple lines may contain characters from outer block containers
    /// (e.g. `>` characters from blockquotes or whitespace from list items):
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::Event::*;
    /// # use jotdown::Container::*;
    /// let input = "
    /// > [txt](multi
    /// > line)";
    /// assert!(matches!(
    ///     Parser::new(input)
    ///         .into_offset_iter()
    ///         .map(|(e, r)| (&input[r], e))
    ///         .collect::<Vec<_>>()
    ///         .as_slice(),
    ///     &[
    ///         ("\n", Blankline),
    ///         (">", Start(Blockquote, ..)),
    ///         ("", Start(Paragraph, ..)),
    ///         ("[", Start(Link { .. }, ..)),
    ///         ("txt", Str(..)),
    ///         ("](multi\n> line)", End(Link { .. })),
    ///         ("", End(Paragraph)),
    ///         ("", End(Blockquote)),
    ///     ],
    /// ));
    /// ```
    pub fn into_offset_iter(self) -> OffsetIter<'s> {
        OffsetIter { parser: self }
    }

    fn inline(&mut self) -> Option<(Event<'s>, Range<usize>)> {
        let next = self.inline_parser.next()?;

        let (inline, mut attributes) = match next {
            inline::Event {
                kind: inline::EventKind::Attributes { attrs, .. },
                ..
            } => (
                self.inline_parser.next(),
                self.inline_parser.store_attributes[attrs as usize].clone(),
            ),
            inline => (Some(inline), Attributes::new()),
        };

        inline.map(|inline| {
            let enter = matches!(inline.kind, inline::EventKind::Enter(_));
            let event = match inline.kind {
                inline::EventKind::Enter(c) | inline::EventKind::Exit(c) => {
                    let t = match c {
                        inline::Container::Span => Container::Span,
                        inline::Container::Verbatim => Container::Verbatim,
                        inline::Container::InlineMath => Container::Math { display: false },
                        inline::Container::DisplayMath => Container::Math { display: true },
                        inline::Container::RawFormat { format } => Container::RawInline { format },
                        inline::Container::Subscript => Container::Subscript,
                        inline::Container::Superscript => Container::Superscript,
                        inline::Container::Insert => Container::Insert,
                        inline::Container::Delete => Container::Delete,
                        inline::Container::Emphasis => Container::Emphasis,
                        inline::Container::Strong => Container::Strong,
                        inline::Container::Mark => Container::Mark,
                        inline::Container::InlineLink(url) => Container::Link(
                            self.inline_parser.store_cowstrs[url as usize].clone(),
                            LinkType::Span(SpanLinkType::Inline),
                        ),
                        inline::Container::InlineImage(url) => Container::Image(
                            self.inline_parser.store_cowstrs[url as usize].clone(),
                            SpanLinkType::Inline,
                        ),
                        inline::Container::ReferenceLink(tag)
                        | inline::Container::ReferenceImage(tag) => {
                            let tag = &self.inline_parser.store_cowstrs[tag as usize];
                            let link_def = self
                                .pre_pass
                                .link_definitions
                                .get::<str>(tag.as_ref())
                                .cloned();

                            let (url_or_tag, ty) = if let Some((url, attrs_def)) = link_def {
                                attributes.union(attrs_def);
                                (url, SpanLinkType::Reference)
                            } else {
                                self.pre_pass.heading_id_by_tag(tag.as_ref()).map_or_else(
                                    || (tag.clone(), SpanLinkType::Unresolved),
                                    |id| (format!("#{}", id).into(), SpanLinkType::Reference),
                                )
                            };

                            if matches!(c, inline::Container::ReferenceLink(..)) {
                                Container::Link(url_or_tag, LinkType::Span(ty))
                            } else {
                                Container::Image(url_or_tag, ty)
                            }
                        }
                        inline::Container::Autolink(url) => {
                            let ty = if url.contains('@') {
                                LinkType::Email
                            } else {
                                LinkType::AutoLink
                            };
                            Container::Link(url.into(), ty)
                        }
                    };
                    if enter {
                        Event::Start(t, attributes)
                    } else {
                        Event::End(t)
                    }
                }
                inline::EventKind::Atom(a) => match a {
                    inline::Atom::FootnoteReference { label } => Event::FootnoteReference(label),
                    inline::Atom::Symbol(sym) => Event::Symbol(sym.into()),
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
                inline::EventKind::Str => Event::Str(self.src[inline.span.clone()].into()),
                inline::EventKind::Attributes { .. } | inline::EventKind::Placeholder => {
                    panic!("{:?}", inline)
                }
            };
            (event, inline.span)
        })
    }

    fn block(&mut self) -> Option<(Event<'s>, Range<usize>)> {
        while let Some(mut ev) = self.blocks.next() {
            let event = match ev.kind {
                block::EventKind::Atom(a) => match a {
                    block::Atom::Blankline => Event::Blankline,
                    block::Atom::ThematicBreak => {
                        if let Some(pos) = self.block_attributes_pos.take() {
                            ev.span.start = pos;
                        }
                        Event::ThematicBreak(self.block_attributes.take())
                    }
                    block::Atom::Attributes => {
                        if self.block_attributes_pos.is_none() {
                            self.block_attributes_pos = Some(ev.span.start);
                        }
                        self.block_attributes
                            .parse(&self.src[ev.span.clone()])
                            .expect("should be valid");
                        continue;
                    }
                },
                block::EventKind::Enter(c) | block::EventKind::Exit(c) => {
                    let enter = matches!(ev.kind, block::EventKind::Enter(..));
                    let cont = match c {
                        block::Node::Leaf(l) => {
                            self.inline_parser.reset();
                            match l {
                                block::Leaf::Paragraph => Container::Paragraph,
                                block::Leaf::Heading {
                                    level,
                                    has_section,
                                    pos,
                                } => Container::Heading {
                                    level,
                                    has_section,
                                    id: self
                                        .pre_pass
                                        .heading_id_by_location(pos)
                                        .unwrap_or_default()
                                        .to_string()
                                        .into(),
                                },
                                block::Leaf::DescriptionTerm => Container::DescriptionTerm,
                                block::Leaf::CodeBlock { language } => {
                                    self.verbatim = enter;
                                    if let Some(format) = language.strip_prefix('=') {
                                        Container::RawBlock { format }
                                    } else {
                                        Container::CodeBlock { language }
                                    }
                                }
                                block::Leaf::TableCell(alignment) => Container::TableCell {
                                    alignment,
                                    head: self.table_head_row,
                                },
                                block::Leaf::Caption => Container::Caption,
                                block::Leaf::LinkDefinition { label } => {
                                    self.verbatim = enter;
                                    Container::LinkDefinition { label }
                                }
                            }
                        }
                        block::Node::Container(c) => match c {
                            block::Container::Blockquote => Container::Blockquote,
                            block::Container::Div { class } => Container::Div { class },
                            block::Container::Footnote { label } => Container::Footnote { label },
                            block::Container::List { ty, tight } => {
                                if matches!(ty, block::ListType::Description) {
                                    Container::DescriptionList
                                } else {
                                    let kind = match ty {
                                        block::ListType::Unordered(..) => ListKind::Unordered,
                                        block::ListType::Task => ListKind::Task,
                                        block::ListType::Ordered(
                                            block::ListNumber { numbering, value },
                                            style,
                                        ) => ListKind::Ordered {
                                            numbering,
                                            style,
                                            start: value,
                                        },
                                        block::ListType::Description => unreachable!(),
                                    };
                                    Container::List { kind, tight }
                                }
                            }
                            block::Container::ListItem(kind) => match kind {
                                block::ListItemKind::Task { checked } => {
                                    Container::TaskListItem { checked }
                                }
                                block::ListItemKind::Description => Container::DescriptionDetails,
                                block::ListItemKind::List => Container::ListItem,
                            },
                            block::Container::Table => Container::Table,
                            block::Container::TableRow { head } => {
                                if enter {
                                    self.table_head_row = head;
                                }
                                Container::TableRow { head }
                            }
                            block::Container::Section { pos } => Container::Section {
                                id: self
                                    .pre_pass
                                    .heading_id_by_location(pos)
                                    .unwrap_or_default()
                                    .to_string()
                                    .into(),
                            },
                        },
                    };
                    if enter {
                        if let Some(pos) = self.block_attributes_pos.take() {
                            ev.span.start = pos;
                        }
                        Event::Start(cont, self.block_attributes.take())
                    } else {
                        self.block_attributes = Attributes::new();
                        self.block_attributes_pos = None;
                        Event::End(cont)
                    }
                }
                block::EventKind::Inline => {
                    if self.verbatim {
                        Event::Str(self.src[ev.span.clone()].into())
                    } else {
                        self.inline_parser.feed_line(
                            ev.span.clone(),
                            !matches!(
                                self.blocks.peek().map(|e| &e.kind),
                                Some(block::EventKind::Inline),
                            ),
                        );
                        return self.next_span();
                    }
                }
                block::EventKind::Stale => continue,
            };
            return Some((event, ev.span));
        }
        None
    }

    fn next_span(&mut self) -> Option<(Event<'s>, Range<usize>)> {
        self.inline().or_else(|| self.block())
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_span().map(|(e, _)| e)
    }
}

/// An iterator that is identical to a [`Parser`], except that it also emits the location of each
/// event within the input.
///
/// See the documentation of [`Parser::into_offset_iter`] for more information.
pub struct OffsetIter<'s> {
    parser: Parser<'s>,
}

impl<'s> Iterator for OffsetIter<'s> {
    type Item = (Event<'s>, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        self.parser.next_span()
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
            let actual = super::Parser::new($src)
                .into_offset_iter()
                .map(|(e, r)| (e, &$src[r]))
                .collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(
                actual,
                expected,
                concat!(
                    "\n",
                    "\x1b[0;1m====================== INPUT =========================\x1b[0m\n",
                    "\x1b[2m{}{}",
                    "\x1b[0;1m================ ACTUAL vs EXPECTED ==================\x1b[0m\n",
                    "{}",
                    "\x1b[0;1m======================================================\x1b[0m\n",
                ),
                $src,
                if $src.ends_with('\n') {
                    ""
                } else {
                    "\n"
                },
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
            (Start(Section { id: "s-1".into() }, Attributes::new()), ""),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "s-1".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "s-1".into(),
                }),
                "",
            ),
            (End(Section { id: "s-1".into() }), ""),
        );
        test_parse!(
            "# abc\ndef\n",
            (
                Start(
                    Section {
                        id: "abc-def".into(),
                    },
                    Attributes::new(),
                ),
                "",
            ),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "abc-def".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("abc".into()), "abc"),
            (Softbreak, "\n"),
            (Str("def".into()), "def"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "abc-def".into(),
                }),
                "",
            ),
            (
                End(Section {
                    id: "abc-def".into(),
                }),
                "",
            ),
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
            (Start(Section { id: "abc".into() }, Attributes::new()), ""),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "abc".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("abc".into()), "abc"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "abc".into(),
                }),
                "",
            ),
            (End(Section { id: "abc".into() }), ""),
            (
                Start(
                    Section { id: "def".into() },
                    [("a", "b")].into_iter().collect(),
                ),
                "{a=b}\n",
            ),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "def".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("def".into()), "def"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "def".into(),
                }),
                "",
            ),
            (End(Section { id: "def".into() }), ""),
        );
    }

    #[test]
    fn heading_ref() {
        test_parse!(
            concat!(
                "A [link][Some Section] to another section.\n", //
                "\n",                                           //
                "# Some Section",                               //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("A ".into()), "A "),
            (
                Start(
                    Link(
                        "#Some-Section".into(),
                        LinkType::Span(SpanLinkType::Reference),
                    ),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("link".into()), "link"),
            (
                End(Link(
                    "#Some-Section".into(),
                    LinkType::Span(SpanLinkType::Reference),
                )),
                "][Some Section]",
            ),
            (Str(" to another section.".into()), " to another section."),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(
                    Section {
                        id: "Some-Section".into(),
                    },
                    Attributes::new(),
                ),
                "",
            ),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "Some-Section".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("Some Section".into()), "Some Section"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "Some-Section".into(),
                }),
                "",
            ),
            (
                End(Section {
                    id: "Some-Section".into(),
                }),
                "",
            ),
        );
        test_parse!(
            concat!(
                "[a][]\n", //
                "[b][]\n", //
                "\n",      //
                "# b\n",   //
                "\n",      //
                "# a\n",   //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("#a".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("a".into()), "a"),
            (
                End(Link("#a".into(), LinkType::Span(SpanLinkType::Reference))),
                "][]",
            ),
            (Softbreak, "\n"),
            (
                Start(
                    Link("#b".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("b".into()), "b"),
            (
                End(Link("#b".into(), LinkType::Span(SpanLinkType::Reference))),
                "][]",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Section { id: "b".into() }, Attributes::new()), ""),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "b".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("b".into()), "b"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "b".into(),
                }),
                "",
            ),
            (Blankline, "\n"),
            (End(Section { id: "b".into() }), ""),
            (Start(Section { id: "a".into() }, Attributes::new()), ""),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "a".into(),
                    },
                    Attributes::new(),
                ),
                "#",
            ),
            (Str("a".into()), "a"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "a".into(),
                }),
                "",
            ),
            (End(Section { id: "a".into() }), ""),
        );
    }

    #[test]
    fn blockquote() {
        test_parse!(
            ">\n",
            (Start(Blockquote, Attributes::new()), ">"),
            (Blankline, "\n"),
            (End(Blockquote), ""),
        );
    }

    #[test]
    fn para() {
        test_parse!(
            "para",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "pa     ra",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("pa     ra".into()), "pa     ra"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "para0\n\npara1",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para0".into()), "para0"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para1".into()), "para1"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn verbatim() {
        test_parse!(
            "`abc\ndef",
            (Start(Paragraph, Attributes::new()), ""),
            (Start(Verbatim, Attributes::new()), "`"),
            (Str("abc\ndef".into()), "abc\ndef"),
            (End(Verbatim), ""),
            (End(Paragraph), ""),
        );
        test_parse!(
            concat!(
                "> `abc\n",
                "> def\n", //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (Start(Verbatim, Attributes::new()), "`"),
            (Str("abc\n".into()), "abc\n"),
            (Str("def".into()), "def"),
            (End(Verbatim), ""),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
    }

    #[test]
    fn raw_inline() {
        test_parse!(
            "``raw\nraw``{=format}",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(RawInline { format: "format" }, Attributes::new()),
                "``",
            ),
            (Str("raw\nraw".into()), "raw\nraw"),
            (End(RawInline { format: "format" }), "``{=format}"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn raw_block() {
        test_parse!(
            "``` =html\n<table>\n```",
            (
                Start(RawBlock { format: "html" }, Attributes::new()),
                "``` =html\n",
            ),
            (Str("<table>".into()), "<table>"),
            (End(RawBlock { format: "html" }), "```"),
        );
    }

    #[test]
    fn raw_block_whitespace() {
        test_parse!(
            concat!(
                "```=html\n",  //
                "<tag1>\n",    //
                "<tag2>\n",    //
                "```\n",       //
                "\n",          //
                "paragraph\n", //
                "\n",          //
                "```=html\n",  //
                "</tag2>\n",   //
                "</tag1>\n",   //
                "```\n",       //
            ),
            (
                Start(RawBlock { format: "html" }, Attributes::new()),
                "```=html\n",
            ),
            (Str("<tag1>\n".into()), "<tag1>\n"),
            (Str("<tag2>".into()), "<tag2>"),
            (End(RawBlock { format: "html" }), "```\n"),
            (Blankline, "\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("paragraph".into()), "paragraph"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(RawBlock { format: "html" }, Attributes::new()),
                "```=html\n",
            ),
            (Str("</tag2>\n".into()), "</tag2>\n"),
            (Str("</tag1>".into()), "</tag1>"),
            (End(RawBlock { format: "html" }), "```\n"),
        );
    }

    #[test]
    fn symbol() {
        test_parse!(
            "abc :+1: def",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc ".into()), "abc "),
            (Symbol("+1".into()), ":+1:"),
            (Str(" def".into()), " def"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn link_inline() {
        test_parse!(
            "[text](url)",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Inline)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Inline))),
                "](url)",
            ),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn link_inline_multi_line() {
        test_parse!(
            concat!(
                "> [text](url\n",
                "> url)\n", //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline))),
                "](url\n> url)",
            ),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
        test_parse!(
            concat!(
                "> [text](a\n", //
                "> bc\n",       //
                "> def)\n",     //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("abcdef".into(), LinkType::Span(SpanLinkType::Inline)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("abcdef".into(), LinkType::Span(SpanLinkType::Inline))),
                "](a\n> bc\n> def)",
            ),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
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
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][tag]",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "tag" }, Attributes::new()),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "tag" }), ""),
        );
        test_parse!(
            concat!(
                "![text][tag]\n",
                "\n",
                "[tag]: url\n" //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Image("url".into(), SpanLinkType::Reference),
                    Attributes::new(),
                ),
                "![",
            ),
            (Str("text".into()), "text"),
            (End(Image("url".into(), SpanLinkType::Reference)), "][tag]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "tag" }, Attributes::new()),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "tag" }), ""),
        );
    }

    #[test]
    fn link_reference_unresolved() {
        test_parse!(
            "[text][tag]",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved))),
                "][tag]",
            ),
            (End(Paragraph), ""),
        );
        test_parse!(
            "![text][tag]",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Image("tag".into(), SpanLinkType::Unresolved),
                    Attributes::new(),
                ),
                "![",
            ),
            (Str("text".into()), "text"),
            (End(Image("tag".into(), SpanLinkType::Unresolved)), "][tag]"),
            (End(Paragraph), ""),
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
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][a\n> b]",
            ),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "a b" }, Attributes::new()),
                "[a b]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "a b" }), ""),
        );
    }

    #[test]
    fn link_reference_multiline_empty() {
        test_parse!(
            concat!(
                "> [a\n",       //
                "> b][]\n",     //
                "> [a\\\n",     //
                "> b][]\n",     //
                "\n",           //
                "[a b]: url\n", //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("a".into()), "a"),
            (Softbreak, "\n"),
            (Str("b".into()), "b"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][]",
            ),
            (Softbreak, "\n"),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("a".into()), "a"),
            (Escape, "\\"),
            (Hardbreak, "\n"),
            (Str("b".into()), "b"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][]",
            ),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "a b" }, Attributes::new()),
                "[a b]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "a b" }), ""),
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
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][tag]",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "tag" }, Attributes::new()),
                "[tag]:",
            ),
            (Str("u".into()), "u"),
            (Str("rl".into()), "rl"),
            (End(LinkDefinition { label: "tag" }), ""),
        );
        test_parse!(
            concat!(
                "[text][tag]\n",
                "\n",
                "[tag]:\n",
                " url\n",  //
                " cont\n", //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("urlcont".into(), LinkType::Span(SpanLinkType::Reference)),
                    Attributes::new(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link(
                    "urlcont".into(),
                    LinkType::Span(SpanLinkType::Reference),
                )),
                "][tag]",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(LinkDefinition { label: "tag" }, Attributes::new()),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (Str("cont".into()), "cont"),
            (End(LinkDefinition { label: "tag" }), ""),
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
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    [("b", "c"), ("a", "b")].into_iter().collect(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][tag]{b=c}",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(
                    LinkDefinition { label: "tag" },
                    [("a", "b")].into_iter().collect(),
                ),
                "{a=b}\n[tag]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "tag" }), ""),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn link_reference_attrs_class() {
        test_parse!(
            concat!(
                "[text][tag]{.link}\n",
                "\n",
                "{.def}\n",
                "[tag]: url\n",
                "para\n",
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                    [("class", "link"), ("class", "def")].into_iter().collect(),
                ),
                "[",
            ),
            (Str("text".into()), "text"),
            (
                End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
                "][tag]{.link}",
            ),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(
                    LinkDefinition { label: "tag" },
                    [("class", "def")].into_iter().collect(),
                ),
                "{.def}\n[tag]:",
            ),
            (Str("url".into()), "url"),
            (End(LinkDefinition { label: "tag" }), ""),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn autolink() {
        test_parse!(
            "<proto:url>\n",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("proto:url".into(), LinkType::AutoLink),
                    Attributes::new(),
                ),
                "<",
            ),
            (Str("proto:url".into()), "proto:url"),
            (End(Link("proto:url".into(), LinkType::AutoLink)), ">"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn email() {
        test_parse!(
            "<name@domain>\n",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Link("name@domain".into(), LinkType::Email),
                    Attributes::new(),
                ),
                "<",
            ),
            (Str("name@domain".into()), "name@domain"),
            (End(Link("name@domain".into(), LinkType::Email)), ">"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn footnote_references() {
        test_parse!(
            "[^a][^b][^c]",
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a"), "[^a]"),
            (FootnoteReference("b"), "[^b]"),
            (FootnoteReference("c"), "[^c]"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn footnote() {
        test_parse!(
            "[^a]\n\n[^a]: a\n",
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a"), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Footnote { label: "a" }, Attributes::new()), "[^a]:"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a".into()), "a"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a" }), ""),
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
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a"), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Footnote { label: "a" }, Attributes::new()), "[^a]:"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc".into()), "abc"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("def".into()), "def"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a" }), ""),
        );
    }

    #[test]
    fn footnote_post() {
        test_parse!(
            concat!(
                "[^a]\n",
                "\n",
                "[^a]: note\n",
                "cont\n",
                "\n",
                "para\n", //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a"), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Footnote { label: "a" }, Attributes::new()), "[^a]:"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("note".into()), "note"),
            (Softbreak, "\n"),
            (Str("cont".into()), "cont"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (End(Footnote { label: "a" }), ""),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
        test_parse!(
            concat!(
                "[^a]\n",       //
                "\n",           //
                "[^a]: note\n", //
                ":::\n",        //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a"), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Footnote { label: "a" }, Attributes::new()), "[^a]:"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("note".into()), "note"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a" }), ""),
            (Start(Div { class: "" }, Attributes::new()), ":::\n"),
            (End(Div { class: "" }), ""),
        );
    }

    #[test]
    fn attr_block() {
        test_parse!(
            "{.some_class}\npara\n",
            (
                Start(Paragraph, [("class", "some_class")].into_iter().collect()),
                "{.some_class}\n",
            ),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
        test_parse!(
            concat!(
                "{.a}\n",
                "{#b}\n",
                "para\n", //
            ),
            (
                Start(
                    Paragraph,
                    [("class", "a"), ("id", "b")].into_iter().collect(),
                ),
                "{.a}\n{#b}\n",
            ),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_inline() {
        test_parse!(
            "abc _def_{.ghi}",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc ".into()), "abc "),
            (
                Start(Emphasis, [("class", "ghi")].into_iter().collect()),
                "_",
            ),
            (Str("def".into()), "def"),
            (End(Emphasis), "_{.ghi}"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_inline_consecutive() {
        test_parse!(
            "_abc def_{.a}{.b #i}",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Emphasis,
                    [("class", "a b"), ("id", "i")].into_iter().collect(),
                ),
                "_",
            ),
            (Str("abc def".into()), "abc def"),
            (End(Emphasis), "_{.a}{.b #i}"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "_abc def_{.a}{%%}{.b #i}",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Emphasis,
                    [("class", "a b"), ("id", "i")].into_iter().collect(),
                ),
                "_",
            ),
            (Str("abc def".into()), "abc def"),
            (End(Emphasis), "_{.a}{%%}{.b #i}"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_inline_consecutive_invalid() {
        test_parse!(
            "_abc def_{.a}{.b #i}{.c invalid}",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Emphasis,
                    [("class", "a b"), ("id", "i")].into_iter().collect(),
                ),
                "_",
            ),
            (Str("abc def".into()), "abc def"),
            (End(Emphasis), "_{.a}{.b #i}"),
            (Str("{.c invalid}".into()), "{.c invalid}"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "_abc def_{.a}{.b #i}{%%}{.c invalid}",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Emphasis,
                    [("class", "a b"), ("id", "i")].into_iter().collect(),
                ),
                "_",
            ),
            (Str("abc def".into()), "abc def"),
            (End(Emphasis), "_{.a}{.b #i}{%%}"),
            (Str("{.c invalid}".into()), "{.c invalid}"),
            (End(Paragraph), ""),
        );
        test_parse!(
            concat!("_abc def_{.a}{.b #i}{%%}{.c\n", "invalid}\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Emphasis,
                    [("class", "a b"), ("id", "i")].into_iter().collect(),
                ),
                "_",
            ),
            (Str("abc def".into()), "abc def"),
            (End(Emphasis), "_{.a}{.b #i}{%%}"),
            (Str("{.c".into()), "{.c"),
            (Softbreak, "\n"),
            (Str("invalid}".into()), "invalid}"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_inline_multiline() {
        test_parse!(
            concat!(
                "> _abc_{a=b\n", //
                "> c=d}\n",      //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(Emphasis, [("a", "b"), ("c", "d")].into_iter().collect()),
                "_",
            ),
            (Str("abc".into()), "abc"),
            (End(Emphasis), "_{a=b\n> c=d}"),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
        test_parse!(
            concat!(
                "> a{\n",   //
                "> %%\n",   //
                "> a=a}\n", //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (Start(Span, [("a", "a")].into_iter().collect()), ""),
            (Str("a".into()), "a"),
            (End(Span), "{\n> %%\n> a=a}"),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
        test_parse!(
            concat!(
                "> a{a=\"a\n", //
                "> b\n",       //
                "> c\"}\n",    //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (Start(Span, [("a", "a b c")].into_iter().collect()), ""),
            (Str("a".into()), "a"),
            (End(Span), "{a=\"a\n> b\n> c\"}"),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
        test_parse!(
            concat!(
                "> a{a=\"\n", //
                "> b\"}\n",   //
            ),
            (Start(Blockquote, Attributes::new()), ">"),
            (Start(Paragraph, Attributes::new()), ""),
            (Start(Span, [("a", "b")].into_iter().collect()), ""),
            (Str("a".into()), "a"),
            (End(Span), "{a=\"\n> b\"}"),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
    }

    #[test]
    fn attr_inline_multiline_unclosed() {
        test_parse!(
            concat!(
                "a{\n", //
                " b\n", //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a{".into()), "a{"),
            (Softbreak, "\n"),
            (Str("b".into()), "b"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_inline_multiline_invalid() {
        test_parse!(
            concat!(
                "a{a=b\n", //
                " b\n",    //
                "}",       //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a{a=b".into()), "a{a=b"),
            (Softbreak, "\n"),
            (Str("b".into()), "b"),
            (Softbreak, "\n"),
            (Str("}".into()), "}"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn list_item_unordered() {
        test_parse!(
            "- abc",
            (
                Start(
                    List {
                        kind: ListKind::Unordered,
                        tight: true,
                    },
                    Attributes::new(),
                ),
                "",
            ),
            (Start(ListItem, Attributes::new()), "-"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc".into()), "abc"),
            (End(Paragraph), ""),
            (End(ListItem), ""),
            (
                End(List {
                    kind: ListKind::Unordered,
                    tight: true,
                }),
                "",
            ),
        );
    }

    #[test]
    fn list_item_ordered_decimal() {
        test_parse!(
            "123. abc",
            (
                Start(
                    List {
                        kind: ListKind::Ordered {
                            numbering: Decimal,
                            style: Period,
                            start: 123,
                        },
                        tight: true,
                    },
                    Attributes::new(),
                ),
                "",
            ),
            (Start(ListItem, Attributes::new()), "123."),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc".into()), "abc"),
            (End(Paragraph), ""),
            (End(ListItem), ""),
            (
                End(List {
                    kind: ListKind::Ordered {
                        numbering: Decimal,
                        style: Period,
                        start: 123,
                    },
                    tight: true,
                }),
                "",
            ),
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
            (
                Start(
                    List {
                        kind: ListKind::Task,
                        tight: true,
                    },
                    Attributes::new(),
                ),
                "",
            ),
            (
                Start(TaskListItem { checked: false }, Attributes::new()),
                "- [ ]",
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a".into()), "a"),
            (End(Paragraph), ""),
            (End(TaskListItem { checked: false }), ""),
            (
                Start(TaskListItem { checked: true }, Attributes::new()),
                "- [x]",
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("b".into()), "b"),
            (End(Paragraph), ""),
            (End(TaskListItem { checked: true }), ""),
            (
                Start(TaskListItem { checked: true }, Attributes::new()),
                "- [X]",
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("c".into()), "c"),
            (End(Paragraph), ""),
            (End(TaskListItem { checked: true }), ""),
            (
                End(List {
                    kind: ListKind::Task,
                    tight: true,
                }),
                "",
            ),
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
