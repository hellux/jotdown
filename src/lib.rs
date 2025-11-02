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
use std::io;
use std::ops::Range;

#[cfg(feature = "html")]
pub mod html;

mod attr;
mod block;
mod inline;
mod lex;

pub use attr::{
    AttributeKind, AttributeValue, AttributeValueParts, Attributes, ParseAttributesError,
};

type CowStr<'s> = std::borrow::Cow<'s, str>;

/// A trait for rendering [`Event`]s to an output format.
///
/// The output can be written to either a [`std::fmt::Write`] or a [`std::io::Write`] object.
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
    ///
    /// Always paired with a matching [`Event::End`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "{#a}\n",
    ///     "[word]{#b}\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::Paragraph,
    ///             [(AttributeKind::Id, "a".into())].into_iter().collect(),
    ///         ),
    ///         Event::Start(
    ///             Container::Span,
    ///             [(AttributeKind::Id, "b".into())].into_iter().collect(),
    ///         ),
    ///         Event::Str("word".into()),
    ///         Event::End(Container::Span),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p id=\"a\"><span id=\"b\">word</span></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Start(Container<'s>, Attributes<'s>),
    /// End of a container.
    ///
    /// Always paired with a matching [`Event::Start`].
    End(Container<'s>),
    /// A string object, text only.
    ///
    /// The strings from the parser will always be borrowed, but users may replace them with owned
    /// variants before rendering.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "str";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("str".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>str</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Str(CowStr<'s>),
    /// A footnote reference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "txt[^nb].";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("txt".into()),
    ///         Event::FootnoteReference("nb".into()),
    ///         Event::Str(".".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>txt<a id=\"fnref1\" href=\"#fn1\" role=\"doc-noteref\"><sup>1</sup></a>.</p>\n",
    ///     "<section role=\"doc-endnotes\">\n",
    ///     "<hr>\n",
    ///     "<ol>\n",
    ///     "<li id=\"fn1\">\n",
    ///     "<p><a href=\"#fnref1\" role=\"doc-backlink\">↩\u{fe0e}</a></p>\n",
    ///     "</li>\n",
    ///     "</ol>\n",
    ///     "</section>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    FootnoteReference(CowStr<'s>),
    /// A symbol, by default rendered literally but may be treated specially.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "a :sym:";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("a ".into()),
    ///         Event::Symbol("sym".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>a :sym:</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Symbol(CowStr<'s>),
    /// Left single quotation mark.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = r#"'quote'"#;
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::LeftSingleQuote,
    ///         Event::Str("quote".into()),
    ///         Event::RightSingleQuote,
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>‘quote’</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    LeftSingleQuote,
    /// Right single quotation mark.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = r#"'}Tis Socrates'"#;
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::RightSingleQuote,
    ///         Event::Str("Tis Socrates".into()),
    ///         Event::RightSingleQuote,
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>’Tis Socrates’</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    RightSingleQuote,
    /// Left single quotation mark.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = r#""Hello," he said"#;
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::LeftDoubleQuote,
    ///         Event::Str("Hello,".into()),
    ///         Event::RightDoubleQuote,
    ///         Event::Str(" he said".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>“Hello,” he said</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    LeftDoubleQuote,
    /// Right double quotation mark.
    RightDoubleQuote,
    /// A horizontal ellipsis, i.e. a set of three periods.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "yes...";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("yes".into()),
    ///         Event::Ellipsis,
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>yes…</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Ellipsis,
    /// An en dash.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "57--33";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("57".into()),
    ///         Event::EnDash,
    ///         Event::Str("33".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>57–33</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    EnDash,
    /// An em dash.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "oxen---and";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("oxen".into()),
    ///         Event::EmDash,
    ///         Event::Str("and".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>oxen—and</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    EmDash,
    /// A space that must not break a line.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "no\\ break";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("no".into()),
    ///         Event::Escape,
    ///         Event::NonBreakingSpace,
    ///         Event::Str("break".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>no&nbsp;break</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    NonBreakingSpace,
    /// A newline that may or may not break a line in the output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "soft\n",
    ///     "break\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("soft".into()),
    ///         Event::Softbreak,
    ///         Event::Str("break".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>soft\n",
    ///     "break</p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Softbreak,
    /// A newline that must break a line in the output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "hard\\\n",
    ///     "break\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("hard".into()),
    ///         Event::Escape,
    ///         Event::Hardbreak,
    ///         Event::Str("break".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>hard<br>\n",
    ///     "break</p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Hardbreak,
    /// An escape character, not visible in output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "\\*a\\*";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Escape,
    ///         Event::Str("*a".into()),
    ///         Event::Escape,
    ///         Event::Str("*".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>*a*</p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Escape,
    /// A blank line, not visible in output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "para0\n",
    ///     "\n",
    ///     "para1\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("para0".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("para1".into()),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>para0</p>\n",
    ///     "<p>para1</p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Blankline,
    /// A thematic break, typically a horizontal rule.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "para0\n",
    ///     "\n",
    ///     " * * * *\n",
    ///     "para1\n",
    ///     "\n",
    ///     "{.c}\n",
    ///     "----\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("para0".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::ThematicBreak(Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("para1".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::ThematicBreak(
    ///             [(AttributeKind::Class, "c".into())]
    ///                 .into_iter()
    ///                 .collect(),
    ///         ),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>para0</p>\n",
    ///     "<hr>\n",
    ///     "<p>para1</p>\n",
    ///     "<hr class=\"c\">\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    ThematicBreak(Attributes<'s>),
    /// Dangling attributes not attached to anything.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "{#a}\n",
    ///     "\n",
    ///     "inline {#b}\n",
    ///     "\n",
    ///     "{#c}\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Attributes(
    ///             [(AttributeKind::Id, "a".into())]
    ///                 .into_iter()
    ///                 .collect(),
    ///         ),
    ///         Event::Blankline,
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("inline ".into()),
    ///         Event::Attributes(
    ///             [(AttributeKind::Id, "b".into())]
    ///                 .into_iter()
    ///                 .collect(),
    ///         ),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::Attributes(
    ///             [(AttributeKind::Id, "c".into())]
    ///                 .into_iter()
    ///                 .collect(),
    ///         ),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "\n",
    ///     "<p>inline </p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Attributes(Attributes<'s>),
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "> a\n",
    ///     "> b\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Blockquote, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("a".into()),
    ///         Event::Softbreak,
    ///         Event::Str("b".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::Blockquote),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<blockquote>\n",
    ///     "<p>a\n",
    ///     "b</p>\n",
    ///     "</blockquote>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Blockquote,
    /// A list.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "- a\n",
    ///     "\n",
    ///     "- b\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::List {
    ///                 kind: ListKind::Unordered(ListBulletType::Dash),
    ///                 tight: false,
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(Container::ListItem, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("a".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::End(Container::ListItem),
    ///         Event::Start(Container::ListItem, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("b".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::ListItem),
    ///         Event::End(Container::List {
    ///             kind: ListKind::Unordered(ListBulletType::Dash),
    ///             tight: false
    ///         }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<ul>\n",
    ///     "<li>\n",
    ///     "<p>a</p>\n",
    ///     "</li>\n",
    ///     "<li>\n",
    ///     "<p>b</p>\n",
    ///     "</li>\n",
    ///     "</ul>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    List { kind: ListKind, tight: bool },
    /// An item of a list
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "- a";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::List {
    ///                 kind: ListKind::Unordered(ListBulletType::Dash),
    ///                 tight: true,
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(Container::ListItem, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("a".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::ListItem),
    ///         Event::End(Container::List {
    ///             kind: ListKind::Unordered(ListBulletType::Dash),
    ///             tight: true,
    ///         }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<ul>\n",
    ///     "<li>\n",
    ///     "a\n",
    ///     "</li>\n",
    ///     "</ul>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    ListItem,
    /// An item of a task list, either checked or unchecked.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "- [x] a";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::List {
    ///                 kind: ListKind::Task(ListBulletType::Dash),
    ///                 tight: true
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::TaskListItem { checked: true },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("a".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::TaskListItem { checked: true }),
    ///         Event::End(Container::List {
    ///             kind: ListKind::Task(ListBulletType::Dash),
    ///             tight: true,
    ///         }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<ul class=\"task-list\">\n",
    ///     "<li>\n",
    ///     "<input disabled=\"\" type=\"checkbox\" checked=\"\"/>\n",
    ///     "a\n",
    ///     "</li>\n",
    ///     "</ul>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    TaskListItem { checked: bool },
    /// A description list.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     ": orange\n",
    ///     "\n",
    ///     " citrus fruit\n",
    ///     ": apple\n",
    ///     "\n",
    ///     " malus fruit\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::DescriptionList, Attributes::new()),
    ///         Event::Start(Container::DescriptionTerm, Attributes::new()),
    ///         Event::Str("orange".into()),
    ///         Event::End(Container::DescriptionTerm),
    ///         Event::Blankline,
    ///         Event::Start(Container::DescriptionDetails, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("citrus fruit".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::DescriptionDetails),
    ///         Event::Start(Container::DescriptionTerm, Attributes::new()),
    ///         Event::Str("apple".into()),
    ///         Event::End(Container::DescriptionTerm),
    ///         Event::Blankline,
    ///         Event::Start(Container::DescriptionDetails, Attributes::new()),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("malus fruit".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::DescriptionDetails),
    ///         Event::End(Container::DescriptionList),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<dl>\n",
    ///     "<dt>orange</dt>\n",
    ///     "<dd>\n",
    ///     "<p>citrus fruit</p>\n",
    ///     "</dd>\n",
    ///     "<dt>apple</dt>\n",
    ///     "<dd>\n",
    ///     "<p>malus fruit</p>\n",
    ///     "</dd>\n",
    ///     "</dl>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    DescriptionList,
    /// Details describing a term within a description list.
    DescriptionDetails,
    /// A footnote definition.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "txt[^nb]\n",
    ///     "\n",
    ///     "[^nb]: actually..\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("txt".into()),
    ///         Event::FootnoteReference("nb".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::Start(
    ///             Container::Footnote { label: "nb".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("actually..".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::Footnote { label: "nb".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>txt<a id=\"fnref1\" href=\"#fn1\" role=\"doc-noteref\"><sup>1</sup></a></p>\n",
    ///     "<section role=\"doc-endnotes\">\n",
    ///     "<hr>\n",
    ///     "<ol>\n",
    ///     "<li id=\"fn1\">\n",
    ///     "<p>actually..<a href=\"#fnref1\" role=\"doc-backlink\">↩\u{fe0e}</a></p>\n",
    ///     "</li>\n",
    ///     "</ol>\n",
    ///     "</section>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Footnote { label: CowStr<'s> },
    /// A table element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "| a | b |\n",
    ///     "|---|--:|\n",
    ///     "| 1 | 2 |\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Table, Attributes::new()),
    ///         Event::Start(
    ///             Container::TableRow { head: true },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::TableCell {
    ///                 alignment: Alignment::Unspecified,
    ///                 head: true
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("a".into()),
    ///         Event::End(Container::TableCell {
    ///             alignment: Alignment::Unspecified,
    ///             head: true,
    ///         }),
    ///         Event::Start(
    ///             Container::TableCell {
    ///                 alignment: Alignment::Right,
    ///                 head: true,
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("b".into()),
    ///         Event::End(Container::TableCell {
    ///             alignment: Alignment::Right,
    ///             head: true,
    ///         }),
    ///         Event::End(Container::TableRow { head: true } ),
    ///         Event::Start(
    ///             Container::TableRow { head: false },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::TableCell {
    ///                 alignment: Alignment::Unspecified,
    ///                 head: false
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("1".into()),
    ///         Event::End(Container::TableCell {
    ///             alignment: Alignment::Unspecified,
    ///             head: false,
    ///         }),
    ///         Event::Start(
    ///             Container::TableCell {
    ///                 alignment: Alignment::Right,
    ///                 head: false,
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("2".into()),
    ///         Event::End(Container::TableCell {
    ///             alignment: Alignment::Right,
    ///             head: false,
    ///         }),
    ///         Event::End(Container::TableRow { head: false } ),
    ///         Event::End(Container::Table),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<table>\n",
    ///     "<tr>\n",
    ///     "<th>a</th>\n",
    ///     "<th style=\"text-align: right;\">b</th>\n",
    ///     "</tr>\n",
    ///     "<tr>\n",
    ///     "<td>1</td>\n",
    ///     "<td style=\"text-align: right;\">2</td>\n",
    ///     "</tr>\n",
    ///     "</table>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Table,
    /// A row element of a table.
    TableRow { head: bool },
    /// A section belonging to a top level heading.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "# outer\n",
    ///     "\n",
    ///     "## inner\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::Section { id: "outer".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::Heading {
    ///                 level: 1,
    ///                 has_section: true,
    ///                 id: "outer".into(),
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("outer".into()),
    ///         Event::End(Container::Heading {
    ///             level: 1,
    ///             has_section: true,
    ///             id: "outer".into(),
    ///         }),
    ///         Event::Blankline,
    ///         Event::Start(
    ///             Container::Section { id: "inner".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::Heading {
    ///                 level: 2,
    ///                 has_section: true,
    ///                 id: "inner".into(),
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("inner".into()),
    ///         Event::End(Container::Heading {
    ///             level: 2,
    ///             has_section: true,
    ///             id: "inner".into(),
    ///         }),
    ///         Event::End(Container::Section { id: "inner".into() }),
    ///         Event::End(Container::Section { id: "outer".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<section id=\"outer\">\n",
    ///     "<h1>outer</h1>\n",
    ///     "<section id=\"inner\">\n",
    ///     "<h2>inner</h2>\n",
    ///     "</section>\n",
    ///     "</section>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Section { id: CowStr<'s> },
    /// A block-level divider element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "::: note\n",
    ///     "this is a note\n",
    ///     ":::\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::Div { class: "note".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("this is a note".into()),
    ///         Event::End(Container::Paragraph),
    ///         Event::End(Container::Div { class: "note".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<div class=\"note\">\n",
    ///     "<p>this is a note</p>\n",
    ///     "</div>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Div { class: CowStr<'s> },
    /// A paragraph.
    Paragraph,
    /// A heading.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "# heading";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::Section { id: "heading".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::Heading {
    ///                 level: 1,
    ///                 has_section: true,
    ///                 id: "heading".into(),
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("heading".into()),
    ///         Event::End(Container::Heading {
    ///             level: 1,
    ///             has_section: true,
    ///             id: "heading".into(),
    ///         }),
    ///         Event::End(Container::Section { id: "heading".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<section id=\"heading\">\n",
    ///     "<h1>heading</h1>\n",
    ///     "</section>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Heading {
        level: u16,
        has_section: bool,
        id: CowStr<'s>,
    },
    /// A cell element of row within a table.
    TableCell { alignment: Alignment, head: bool },
    /// A caption within a table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "|a|\n",
    ///     "^ caption\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Table, Attributes::new()),
    ///         Event::Start(Container::Caption, Attributes::new()),
    ///         Event::Str("caption".into()),
    ///         Event::End(Container::Caption),
    ///         Event::Start(
    ///             Container::TableRow { head: false },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Start(
    ///             Container::TableCell {
    ///                 alignment: Alignment::Unspecified,
    ///                 head: false
    ///             },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("a".into()),
    ///         Event::End(Container::TableCell {
    ///             alignment: Alignment::Unspecified,
    ///             head: false,
    ///         }),
    ///         Event::End(Container::TableRow { head: false } ),
    ///         Event::End(Container::Table),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<table>\n",
    ///     "<caption>caption</caption>\n",
    ///     "<tr>\n",
    ///     "<td>a</td>\n",
    ///     "</tr>\n",
    ///     "</table>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Caption,
    /// A term within a description list.
    DescriptionTerm,
    /// A link definition.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "[label]: url";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::LinkDefinition { label: "label".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("url".into()),
    ///         Event::End(Container::LinkDefinition { label: "label".into() }),
    ///     ],
    /// );
    /// let html = "\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    LinkDefinition { label: CowStr<'s> },
    /// A block with raw markup for a specific output format.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "```=html\n",
    ///     "<tag>x</tag>\n",
    ///     "```\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::RawBlock { format: "html".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("<tag>x</tag>".into()),
    ///         Event::End(Container::RawBlock { format: "html".into() }),
    ///     ],
    /// );
    /// let html = "<tag>x</tag>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    RawBlock { format: CowStr<'s> },
    /// A block with code in a specific language.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "```html\n",
    ///     "<tag>x</tag>\n",
    ///     "```\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(
    ///             Container::CodeBlock { language: "html".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("<tag>x</tag>\n".into()),
    ///         Event::End(Container::CodeBlock { language: "html".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<pre><code class=\"language-html\">&lt;tag&gt;x&lt;/tag&gt;\n",
    ///     "</code></pre>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    CodeBlock { language: CowStr<'s> },
    /// An inline divider element.
    ///
    /// # Examples
    ///
    /// Can be used to add attributes:
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "word{#a}\n",
    ///     "[two words]{#b}\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::Span,
    ///             [(AttributeKind::Id, "a".into())].into_iter().collect(),
    ///         ),
    ///         Event::Str("word".into()),
    ///         Event::End(Container::Span),
    ///         Event::Softbreak,
    ///         Event::Start(
    ///             Container::Span,
    ///             [(AttributeKind::Id, "b".into())].into_iter().collect(),
    ///         ),
    ///         Event::Str("two words".into()),
    ///         Event::End(Container::Span),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p><span id=\"a\">word</span>\n",
    ///     "<span id=\"b\">two words</span></p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Span,
    /// An inline link, the first field is either a destination URL or an unresolved tag.
    ///
    /// # Examples
    ///
    /// URLs or email addresses can be enclosed with angled brackets to create a hyperlink:
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "<https://example.com>\n",
    ///     "<me@example.com>\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::Link(
    ///                 "https://example.com".into(),
    ///                 LinkType::AutoLink,
    ///             ),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("https://example.com".into()),
    ///         Event::End(Container::Link(
    ///             "https://example.com".into(),
    ///             LinkType::AutoLink,
    ///         )),
    ///         Event::Softbreak,
    ///         Event::Start(
    ///             Container::Link(
    ///                 "me@example.com".into(),
    ///                 LinkType::Email,
    ///             ),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("me@example.com".into()),
    ///         Event::End(Container::Link(
    ///             "me@example.com".into(),
    ///             LinkType::Email,
    ///         )),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p><a href=\"https://example.com\">https://example.com</a>\n",
    ///     "<a href=\"mailto:me@example.com\">me@example.com</a></p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    ///
    /// Anchor text and the URL can be specified inline:
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "[anchor](url)\n";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::Link(
    ///                 "url".into(),
    ///                 LinkType::Span(SpanLinkType::Inline),
    ///             ),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("anchor".into()),
    ///         Event::End(
    ///             Container::Link("url".into(),
    ///             LinkType::Span(SpanLinkType::Inline)),
    ///         ),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><a href=\"url\">anchor</a></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    ///
    /// Alternatively, the URL can be retrieved from a link definition using hard brackets, if it
    /// exists:
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "[a][label]\n",
    ///     "[b][non-existent]\n",
    ///     "\n",
    ///     "[label]: url\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::Link(
    ///                 "url".into(),
    ///                 LinkType::Span(SpanLinkType::Reference),
    ///             ),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("a".into()),
    ///         Event::End(
    ///             Container::Link("url".into(),
    ///             LinkType::Span(SpanLinkType::Reference)),
    ///         ),
    ///         Event::Softbreak,
    ///         Event::Start(
    ///             Container::Link(
    ///                 "non-existent".into(),
    ///                 LinkType::Span(SpanLinkType::Unresolved),
    ///             ),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("b".into()),
    ///         Event::End(
    ///             Container::Link("non-existent".into(),
    ///             LinkType::Span(SpanLinkType::Unresolved)),
    ///         ),
    ///         Event::End(Container::Paragraph),
    ///         Event::Blankline,
    ///         Event::Start(
    ///             Container::LinkDefinition { label: "label".into() },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("url".into()),
    ///         Event::End(Container::LinkDefinition { label: "label".into() }),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p><a href=\"url\">a</a>\n",
    ///     "<a>b</a></p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Link(CowStr<'s>, LinkType),
    /// An inline image, the first field is either a destination URL or an unresolved tag.
    ///
    /// # Examples
    ///
    /// Inner Str objects compose the alternative text:
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "![alt text](img.png)";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::Image("img.png".into(), SpanLinkType::Inline),
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str("alt text".into()),
    ///         Event::End(
    ///             Container::Image("img.png".into(), SpanLinkType::Inline),
    ///         ),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><img alt=\"alt text\" src=\"img.png\"></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Image(CowStr<'s>, SpanLinkType),
    /// An inline verbatim string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "inline `verbatim`";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("inline ".into()),
    ///         Event::Start(Container::Verbatim, Attributes::new()),
    ///         Event::Str("verbatim".into()),
    ///         Event::End(Container::Verbatim),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p>inline <code>verbatim</code></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Verbatim,
    /// An inline or display math element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = concat!(
    ///     "inline $`a\\cdot{}b` or\n",
    ///     "display $$`\\frac{a}{b}`\n",
    /// );
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Str("inline ".into()),
    ///         Event::Start(
    ///             Container::Math { display: false },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str(r"a\cdot{}b".into()),
    ///         Event::End(Container::Math { display: false }),
    ///         Event::Str(" or".into()),
    ///         Event::Softbreak,
    ///         Event::Str("display ".into()),
    ///         Event::Start(
    ///             Container::Math { display: true },
    ///             Attributes::new(),
    ///         ),
    ///         Event::Str(r"\frac{a}{b}".into()),
    ///         Event::End(Container::Math { display: true }),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = concat!(
    ///     "<p>inline <span class=\"math inline\">\\(a\\cdot{}b\\)</span> or\n",
    ///     "display <span class=\"math display\">\\[\\frac{a}{b}\\]</span></p>\n",
    /// );
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Math { display: bool },
    /// Inline raw markup for a specific output format.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "`<tag>a</tag>`{=html}";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(
    ///             Container::RawInline { format: "html".into() }, Attributes::new(),
    ///         ),
    ///         Event::Str("<tag>a</tag>".into()),
    ///         Event::End(Container::RawInline { format: "html".into() }),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><tag>a</tag></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    RawInline { format: CowStr<'s> },
    /// A subscripted element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "~SUB~";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Subscript, Attributes::new()),
    ///         Event::Str("SUB".into()),
    ///         Event::End(Container::Subscript),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><sub>SUB</sub></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Subscript,
    /// A superscripted element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "^SUP^";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Superscript, Attributes::new()),
    ///         Event::Str("SUP".into()),
    ///         Event::End(Container::Superscript),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><sup>SUP</sup></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Superscript,
    /// An inserted inline element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "{+INS+}";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Insert, Attributes::new()),
    ///         Event::Str("INS".into()),
    ///         Event::End(Container::Insert),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><ins>INS</ins></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Insert,
    /// A deleted inline element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "{-DEL-}";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Delete, Attributes::new()),
    ///         Event::Str("DEL".into()),
    ///         Event::End(Container::Delete),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><del>DEL</del></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Delete,
    /// An inline element emphasized with a bold typeface.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "*STRONG*";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Strong, Attributes::new()),
    ///         Event::Str("STRONG".into()),
    ///         Event::End(Container::Strong),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><strong>STRONG</strong></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Strong,
    /// An emphasized inline element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "_EM_";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Emphasis, Attributes::new()),
    ///         Event::Str("EM".into()),
    ///         Event::End(Container::Emphasis),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><em>EM</em></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Emphasis,
    /// A highlighted inline element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// let src = "{=MARK=}";
    /// let events: Vec<_> = Parser::new(src).collect();
    /// assert_eq!(
    ///     &events,
    ///     &[
    ///         Event::Start(Container::Paragraph, Attributes::new()),
    ///         Event::Start(Container::Mark, Attributes::new()),
    ///         Event::Str("MARK".into()),
    ///         Event::End(Container::Mark),
    ///         Event::End(Container::Paragraph),
    ///     ],
    /// );
    /// let html = "<p><mark>MARK</mark></p>\n";
    /// assert_eq!(&html::render_to_string(events.into_iter()), html);
    /// ```
    Mark,
}

impl Container<'_> {
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

/// Character used to create an unordered list item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListBulletType {
    /// `-`
    Dash,
    /// `*`
    Star,
    /// `+`
    Plus,
}

impl TryFrom<u8> for ListBulletType {
    type Error = ();

    fn try_from(c: u8) -> Result<Self, Self::Error> {
        match c {
            b'-' => Ok(Self::Dash),
            b'*' => Ok(Self::Star),
            b'+' => Ok(Self::Plus),
            _ => Err(()),
        }
    }
}

impl TryFrom<char> for ListBulletType {
    type Error = ();

    fn try_from(c: char) -> Result<Self, Self::Error> {
        u8::try_from(u32::from(c))
            .map_err(|_| ())
            .and_then(Self::try_from)
    }
}

impl From<ListBulletType> for u8 {
    fn from(t: ListBulletType) -> Self {
        match t {
            ListBulletType::Dash => b'-',
            ListBulletType::Star => b'*',
            ListBulletType::Plus => b'+',
        }
    }
}

impl From<ListBulletType> for char {
    fn from(t: ListBulletType) -> Self {
        u8::from(t).into()
    }
}

/// The type of a list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListKind {
    /// A bullet list.
    Unordered(ListBulletType),
    /// An enumerated list.
    Ordered {
        numbering: OrderedListNumbering,
        style: OrderedListStyle,
        start: u64,
    },
    /// A task list.
    Task(ListBulletType),
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

    /// Last parsed block attributes, and its span.
    block_attributes: Option<(Attributes<'s>, Range<usize>)>,

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
        use std::fmt::Write;
        let mut link_definitions = Map::new();
        let mut headings: Vec<Heading> = Vec::new();
        let mut used_ids: Set<String> = Set::new();

        let mut attr_prev: Vec<Range<usize>> = Vec::new();
        while let Some(e) = blocks.next() {
            match e.kind {
                block::EventKind::Enter(block::Node::Leaf(block::Leaf::LinkDefinition {
                    label,
                })) => {
                    // All link definition tags have to be obtained initially, as references can
                    // appear before the definition.
                    let attrs = Attributes::from_iter(attr_prev.iter().flat_map(|sp| {
                        Attributes::try_from(&src[sp.clone()]).expect("should be valid")
                    }));
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
                    let attrs = Attributes::from_iter(attr_prev.iter().flat_map(|sp| {
                        Attributes::try_from(&src[sp.clone()]).expect("should be valid")
                    }));
                    let id_override = attrs.get_value("id").map(|s| s.to_string());

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
                    attr_prev.push(e.span.clone());
                }
                block::EventKind::Enter(..)
                | block::EventKind::Exit(block::Node::Container(block::Container::Section {
                    ..
                })) => {}
                _ => {
                    attr_prev = Vec::new();
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
            block_attributes: None,
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
    /// However, there is an exception to this rule:
    ///
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

        let event = inline.map(|inline| {
            let enter = matches!(inline.kind, inline::EventKind::Enter(_));
            let event = match inline.kind {
                inline::EventKind::Enter(c) | inline::EventKind::Exit(c) => {
                    let t = match c {
                        inline::Container::Span => Container::Span,
                        inline::Container::Verbatim => Container::Verbatim,
                        inline::Container::InlineMath => Container::Math { display: false },
                        inline::Container::DisplayMath => Container::Math { display: true },
                        inline::Container::RawFormat { format } => Container::RawInline {
                            format: format.into(),
                        },
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
                            let link_def =
                                self.pre_pass.link_definitions.get(tag.as_ref()).cloned();

                            let (url_or_tag, ty) = if let Some((url, mut attrs_def)) = link_def {
                                if enter {
                                    attrs_def.append(&mut attributes);
                                    attributes = attrs_def;
                                }
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
                        Event::Start(t, attributes.take())
                    } else {
                        Event::End(t)
                    }
                }
                inline::EventKind::Atom(a) => match a {
                    inline::Atom::FootnoteReference { label } => {
                        Event::FootnoteReference(label.into())
                    }
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
                inline::EventKind::Empty => {
                    debug_assert!(!attributes.is_empty());
                    Event::Attributes(attributes.take())
                }
                inline::EventKind::Str => Event::Str(self.src[inline.span.clone()].into()),
                inline::EventKind::Attributes { .. } | inline::EventKind::Placeholder => {
                    panic!("{:?}", inline)
                }
            };
            (event, inline.span)
        });

        debug_assert!(
            attributes.is_empty(),
            "unhandled attributes: {:?}",
            attributes
        );

        event
    }

    fn block(&mut self) -> Option<(Event<'s>, Range<usize>)> {
        while let Some(ev) = self.blocks.peek() {
            let mut ev_span = ev.span.clone();
            let mut pop = true;
            let event = match ev.kind {
                block::EventKind::Atom(a) => match a {
                    block::Atom::Blankline => {
                        debug_assert_eq!(self.block_attributes, None);
                        Event::Blankline
                    }
                    block::Atom::ThematicBreak => {
                        let attrs = if let Some((attrs, span)) = self.block_attributes.take() {
                            ev_span.start = span.start;
                            attrs
                        } else {
                            Attributes::new()
                        };
                        Event::ThematicBreak(attrs)
                    }
                    block::Atom::Attributes => {
                        let (mut attrs, mut span) = self
                            .block_attributes
                            .take()
                            .unwrap_or_else(|| (Attributes::new(), ev_span.clone()));
                        attrs
                            .parse(&self.src[ev_span.clone()])
                            .expect("should be valid");
                        span.end = ev_span.end;
                        self.blocks.next().unwrap();
                        if matches!(
                            self.blocks.peek().map(|e| &e.kind),
                            Some(block::EventKind::Atom(block::Atom::Blankline))
                        ) {
                            return Some((Event::Attributes(attrs), span));
                        }
                        self.block_attributes = Some((attrs, span));
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
                                        Container::RawBlock {
                                            format: format.into(),
                                        }
                                    } else {
                                        Container::CodeBlock {
                                            language: language.into(),
                                        }
                                    }
                                }
                                block::Leaf::TableCell(alignment) => Container::TableCell {
                                    alignment,
                                    head: self.table_head_row,
                                },
                                block::Leaf::Caption => Container::Caption,
                                block::Leaf::LinkDefinition { label } => {
                                    self.verbatim = enter;
                                    Container::LinkDefinition {
                                        label: label.into(),
                                    }
                                }
                            }
                        }
                        block::Node::Container(c) => match c {
                            block::Container::Blockquote => Container::Blockquote,
                            block::Container::Div { class } => Container::Div {
                                class: class.into(),
                            },
                            block::Container::Footnote { label } => Container::Footnote {
                                label: label.into(),
                            },
                            block::Container::List { ty, tight } => {
                                if matches!(ty, block::ListType::Description) {
                                    Container::DescriptionList
                                } else {
                                    let kind = match ty {
                                        block::ListType::Unordered(c) => ListKind::Unordered(
                                            c.try_into().expect("should be bullet character"),
                                        ),
                                        block::ListType::Task(c) => ListKind::Task(
                                            c.try_into().expect("should be bullet character"),
                                        ),
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
                        let attrs = if let Some((attrs, span)) = self.block_attributes.take() {
                            ev_span.start = span.start;
                            attrs
                        } else {
                            Attributes::new()
                        };
                        Event::Start(cont, attrs)
                    } else if let Some((attrs, sp)) = self.block_attributes.take() {
                        pop = false;
                        ev_span = sp;
                        Event::Attributes(attrs)
                    } else {
                        Event::End(cont)
                    }
                }
                block::EventKind::Inline => {
                    if self.verbatim {
                        Event::Str(self.src[ev_span.clone()].into())
                    } else {
                        self.blocks.next().unwrap();
                        self.inline_parser.feed_line(
                            ev_span.clone(),
                            !matches!(
                                self.blocks.peek().map(|e| &e.kind),
                                Some(block::EventKind::Inline),
                            ),
                        );
                        return self.next_span();
                    }
                }
                block::EventKind::Stale => {
                    self.blocks.next().unwrap();
                    continue;
                }
            };
            if pop {
                self.blocks.next().unwrap();
            }
            return Some((event, ev_span));
        }
        None
    }

    fn next_span(&mut self) -> Option<(Event<'s>, Range<usize>)> {
        self.inline().or_else(|| self.block()).or_else(|| {
            self.block_attributes
                .take()
                .map(|(attrs, span)| (Event::Attributes(attrs), span))
        })
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
    use super::AttributeKind;
    use super::Attributes;
    use super::Container::*;
    use super::Event::*;
    use super::LinkType;
    use super::ListBulletType::*;
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
                    [(AttributeKind::Pair { key: "a".into() }, "b")]
                        .into_iter()
                        .collect(),
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
                Start(
                    RawInline {
                        format: "format".into()
                    },
                    Attributes::new()
                ),
                "``",
            ),
            (Str("raw\nraw".into()), "raw\nraw"),
            (
                End(RawInline {
                    format: "format".into()
                }),
                "``{=format}"
            ),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn raw_block() {
        test_parse!(
            "``` =html\n<table>\n```",
            (
                Start(
                    RawBlock {
                        format: "html".into()
                    },
                    Attributes::new()
                ),
                "``` =html\n",
            ),
            (Str("<table>".into()), "<table>"),
            (
                End(RawBlock {
                    format: "html".into()
                }),
                "```"
            ),
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
                Start(
                    RawBlock {
                        format: "html".into()
                    },
                    Attributes::new()
                ),
                "```=html\n",
            ),
            (Str("<tag1>\n".into()), "<tag1>\n"),
            (Str("<tag2>".into()), "<tag2>"),
            (
                End(RawBlock {
                    format: "html".into()
                }),
                "```\n"
            ),
            (Blankline, "\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("paragraph".into()), "paragraph"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(
                    RawBlock {
                        format: "html".into()
                    },
                    Attributes::new()
                ),
                "```=html\n",
            ),
            (Str("</tag2>\n".into()), "</tag2>\n"),
            (Str("</tag1>".into()), "</tag1>"),
            (
                End(RawBlock {
                    format: "html".into()
                }),
                "```\n"
            ),
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
                Start(
                    LinkDefinition {
                        label: "tag".into()
                    },
                    Attributes::new()
                ),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
                Start(
                    LinkDefinition {
                        label: "tag".into()
                    },
                    Attributes::new()
                ),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
                Start(
                    LinkDefinition {
                        label: "a b".into()
                    },
                    Attributes::new()
                ),
                "[a b]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "a b".into()
                }),
                ""
            ),
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
                Start(
                    LinkDefinition {
                        label: "a b".into()
                    },
                    Attributes::new()
                ),
                "[a b]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "a b".into()
                }),
                ""
            ),
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
                Start(
                    LinkDefinition {
                        label: "tag".into()
                    },
                    Attributes::new()
                ),
                "[tag]:",
            ),
            (Str("u".into()), "u"),
            (Str("rl".into()), "rl"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
                Start(
                    LinkDefinition {
                        label: "tag".into()
                    },
                    Attributes::new()
                ),
                "[tag]:",
            ),
            (Str("url".into()), "url"),
            (Str("cont".into()), "cont"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
                    [
                        (AttributeKind::Pair { key: "a".into() }, "b"),
                        (AttributeKind::Pair { key: "b".into() }, "c"),
                    ]
                    .into_iter()
                    .collect(),
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
                    LinkDefinition {
                        label: "tag".into()
                    },
                    [(AttributeKind::Pair { key: "a".into() }, "b")]
                        .into_iter()
                        .collect(),
                ),
                "{a=b}\n[tag]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
                    [
                        (AttributeKind::Class, "def"),
                        (AttributeKind::Class, "link"),
                    ]
                    .into_iter()
                    .collect(),
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
                    LinkDefinition {
                        label: "tag".into()
                    },
                    [(AttributeKind::Class, "def")].into_iter().collect(),
                ),
                "{.def}\n[tag]:",
            ),
            (Str("url".into()), "url"),
            (
                End(LinkDefinition {
                    label: "tag".into()
                }),
                ""
            ),
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
            (FootnoteReference("a".into()), "[^a]"),
            (FootnoteReference("b".into()), "[^b]"),
            (FootnoteReference("c".into()), "[^c]"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn footnote() {
        test_parse!(
            "[^a]\n\n[^a]: a\n",
            (Start(Paragraph, Attributes::new()), ""),
            (FootnoteReference("a".into()), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(Footnote { label: "a".into() }, Attributes::new()),
                "[^a]:"
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a".into()), "a"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a".into() }), ""),
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
            (FootnoteReference("a".into()), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(Footnote { label: "a".into() }, Attributes::new()),
                "[^a]:"
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("abc".into()), "abc"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("def".into()), "def"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a".into() }), ""),
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
            (FootnoteReference("a".into()), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(Footnote { label: "a".into() }, Attributes::new()),
                "[^a]:"
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("note".into()), "note"),
            (Softbreak, "\n"),
            (Str("cont".into()), "cont"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (End(Footnote { label: "a".into() }), ""),
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
            (FootnoteReference("a".into()), "[^a]"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Start(Footnote { label: "a".into() }, Attributes::new()),
                "[^a]:"
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (Str("note".into()), "note"),
            (End(Paragraph), ""),
            (End(Footnote { label: "a".into() }), ""),
            (Start(Div { class: "".into() }, Attributes::new()), ":::\n"),
            (End(Div { class: "".into() }), ""),
        );
    }

    #[test]
    fn attr_block() {
        test_parse!(
            "{.some_class}\npara\n",
            (
                Start(
                    Paragraph,
                    [(AttributeKind::Class, "some_class")].into_iter().collect(),
                ),
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
                    [(AttributeKind::Class, "a"), (AttributeKind::Id, "b")]
                        .into_iter()
                        .collect(),
                ),
                "{.a}\n{#b}\n",
            ),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
        );
    }

    #[test]
    fn attr_block_dangling() {
        test_parse!(
            "{.a}",
            (
                Attributes([(AttributeKind::Class, "a")].into_iter().collect()),
                "{.a}",
            ),
        );
        test_parse!(
            "para\n\n{.a}",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("para".into()), "para"),
            (End(Paragraph), ""),
            (Blankline, "\n"),
            (
                Attributes([(AttributeKind::Class, "a")].into_iter().collect()),
                "{.a}",
            ),
        );
        test_parse!(
            "{.a}\n{.b}\n",
            (
                Attributes(
                    [(AttributeKind::Class, "a"), (AttributeKind::Class, "b")]
                        .into_iter()
                        .collect()
                ),
                "{.a}\n{.b}\n",
            ),
        );
    }

    #[test]
    fn attr_block_dangling_end_of_block() {
        test_parse!(
            concat!(
                "# h\n",  //
                "\n",     //
                "{%cmt}", //
            ),
            (Start(Section { id: "h".into() }, Attributes::new()), ""),
            (
                Start(
                    Heading {
                        level: 1,
                        has_section: true,
                        id: "h".into(),
                    },
                    Attributes::new(),
                ),
                "#"
            ),
            (Str("h".into()), "h"),
            (
                End(Heading {
                    level: 1,
                    has_section: true,
                    id: "h".into(),
                }),
                ""
            ),
            (Blankline, "\n"),
            (
                Attributes([(AttributeKind::Comment, "cmt")].into_iter().collect()),
                "{%cmt}"
            ),
            (End(Section { id: "h".into() }), ""),
        );
        test_parse!(
            concat!(
                ":::\n",    //
                "{%cmt}\n", //
                ":::\n",    //
            ),
            (Start(Div { class: "".into() }, Attributes::new()), ":::\n"),
            (
                Attributes([(AttributeKind::Comment, "cmt")].into_iter().collect()),
                "{%cmt}\n"
            ),
            (End(Div { class: "".into() }), ":::\n"),
        );
    }

    #[test]
    fn attr_block_blankline() {
        test_parse!(
            "{.a}\n\n{.b}\n\n{.c}\npara",
            (
                Attributes([(AttributeKind::Class, "a")].into_iter().collect()),
                "{.a}\n",
            ),
            (Blankline, "\n"),
            (
                Attributes([(AttributeKind::Class, "b")].into_iter().collect()),
                "{.b}\n",
            ),
            (Blankline, "\n"),
            (
                Start(
                    Paragraph,
                    [(AttributeKind::Class, "c")].into_iter().collect(),
                ),
                "{.c}\n",
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
                Start(
                    Emphasis,
                    [(AttributeKind::Class, "ghi")].into_iter().collect(),
                ),
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
                    [
                        (AttributeKind::Class, "a"),
                        (AttributeKind::Class, "b"),
                        (AttributeKind::Id, "i"),
                    ]
                    .into_iter()
                    .collect(),
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
                    [
                        (AttributeKind::Class, "a"),
                        (AttributeKind::Comment, ""),
                        (AttributeKind::Class, "b"),
                        (AttributeKind::Id, "i"),
                    ]
                    .into_iter()
                    .collect(),
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
                    [
                        (AttributeKind::Class, "a"),
                        (AttributeKind::Class, "b"),
                        (AttributeKind::Id, "i"),
                    ]
                    .into_iter()
                    .collect(),
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
                    [
                        (AttributeKind::Class, "a"),
                        (AttributeKind::Class, "b"),
                        (AttributeKind::Id, "i"),
                        (AttributeKind::Comment, ""),
                    ]
                    .into_iter()
                    .collect(),
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
                    [
                        (AttributeKind::Class, "a"),
                        (AttributeKind::Class, "b"),
                        (AttributeKind::Id, "i"),
                        (AttributeKind::Comment, ""),
                    ]
                    .into_iter()
                    .collect(),
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
                Start(
                    Emphasis,
                    [
                        (AttributeKind::Pair { key: "a".into() }, "b"),
                        (AttributeKind::Pair { key: "c".into() }, "d"),
                    ]
                    .into_iter()
                    .collect(),
                ),
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
            (
                Start(
                    Span,
                    [
                        (AttributeKind::Comment, ""),
                        (AttributeKind::Pair { key: "a".into() }, "a"),
                    ]
                    .into_iter()
                    .collect(),
                ),
                "",
            ),
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
            (
                Start(
                    Span,
                    [(AttributeKind::Pair { key: "a".into() }, "a b c")]
                        .into_iter()
                        .collect(),
                ),
                "",
            ),
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
            (
                Start(
                    Span,
                    [(AttributeKind::Pair { key: "a".into() }, "b")]
                        .into_iter()
                        .collect(),
                ),
                "",
            ),
            (Str("a".into()), "a"),
            (End(Span), "{a=\"\n> b\"}"),
            (End(Paragraph), ""),
            (End(Blockquote), ""),
        );
    }

    #[test]
    fn attr_inline_multiline_comment() {
        test_parse!(
            concat!(
                "a{%a\n", //
                "b\n",    //
                "c%}\n",  //
            ),
            (Start(Paragraph, Attributes::new()), ""),
            (
                Start(
                    Span,
                    [(AttributeKind::Comment, "a\nb\nc")].into_iter().collect(),
                ),
                "",
            ),
            (Str("a".into()), "a"),
            (End(Span), "{%a\nb\nc%}"),
            (End(Paragraph), ""),
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
    fn attr_inline_dangling() {
        test_parse!(
            "*a\n{%}",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("*a".into()), "*a"),
            (Softbreak, "\n"),
            (
                Attributes([(AttributeKind::Comment, "")].into_iter().collect()),
                "{%}",
            ),
            (End(Paragraph), ""),
        );
        test_parse!(
            "a {.b} c",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a ".into()), "a "),
            (
                Attributes([(AttributeKind::Class, "b")].into_iter().collect()),
                "{.b}",
            ),
            (Str(" c".into()), " c"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "a {%cmt} c",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a ".into()), "a "),
            (
                Attributes([(AttributeKind::Comment, "cmt")].into_iter().collect()),
                "{%cmt}",
            ),
            (Str(" c".into()), " c"),
            (End(Paragraph), ""),
        );
        test_parse!(
            "a {%cmt}",
            (Start(Paragraph, Attributes::new()), ""),
            (Str("a ".into()), "a "),
            (
                Attributes([(AttributeKind::Comment, "cmt")].into_iter().collect()),
                "{%cmt}",
            ),
            (End(Paragraph), ""),
        );
        test_parse!(
            "{%cmt} a",
            (Start(Paragraph, Attributes::new()), ""),
            (
                Attributes([(AttributeKind::Comment, "cmt")].into_iter().collect()),
                "{%cmt}",
            ),
            (Str(" a".into()), " a"),
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
                        kind: ListKind::Unordered(Dash),
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
                    kind: ListKind::Unordered(Dash),
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
                        kind: ListKind::Task(Dash),
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
                    kind: ListKind::Task(Dash),
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
