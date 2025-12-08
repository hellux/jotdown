//! An HTML renderer that takes an iterator of [`Event`]s and emits HTML.

use crate::Alignment;
use crate::Container;
use crate::CowStr;
use crate::Event;
use crate::LinkType;
use crate::ListKind;
use crate::Map;
use crate::OrderedListNumbering::*;
use crate::Render;
use crate::SpanLinkType;

/// Render events into a string.
///
/// This is a convenience function for rendering documents whole without any customizations.
///
/// # Examples
///
/// ```
/// assert_eq!(jotdown::html::render_to_string("hello"), "<p>hello</p>\n");
/// ```
pub fn render_to_string(doc: &str) -> String {
    use crate::RenderExt;
    let mut r = Renderer::default();

    r.render_document(doc).unwrap();

    r.into_inner()
}

#[derive(Clone)]
/// Options for indentation of HTML output.
pub struct Indentation {
    /// String to use for each indentation level.
    ///
    /// NOTE: The resulting HTML output may be invalid depending on the contents of this string.
    ///
    /// # Examples
    ///
    /// Defaults to a single tab character:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = "> a\n";
    ///
    /// let renderer = Renderer::indented(Indentation::default());
    /// let html = renderer.render_to_string(src);
    /// assert_eq!(
    ///     html,
    ///     concat!(
    ///         "<blockquote>\n",
    ///         "\t<p>a</p>\n",
    ///         "</blockquote>\n",
    ///     ),
    /// );
    /// ```
    ///
    /// To indent with e.g. 4 spaces, set to `"    "`:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = "> a\n";
    /// let renderer = Renderer::indented(Indentation {
    ///     string: "    ".to_string(),
    ///     ..Indentation::default()
    /// });
    /// let html = renderer.render_to_string(src);
    /// assert_eq!(
    ///     html,
    ///     concat!(
    ///         "<blockquote>\n",
    ///         "    <p>a</p>\n",
    ///         "</blockquote>\n",
    ///     ),
    /// );
    /// ```
    pub string: String,
    /// Number of indentation levels to use for the outermost elements.
    ///
    /// # Examples
    ///
    /// Defaults to zero:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = "> a\n";
    ///
    /// let renderer = Renderer::indented(Indentation::default());
    /// let html = renderer.render_to_string(src);
    /// assert_eq!(
    ///     html,
    ///     concat!(
    ///         "<blockquote>\n",
    ///         "\t<p>a</p>\n",
    ///         "</blockquote>\n",
    ///     ),
    /// );
    /// ```
    ///
    /// Set to a non-zero value to use a starting indent:
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = "> a\n";
    /// let renderer = Renderer::indented(Indentation {
    ///     initial_level: 2,
    ///     ..Indentation::default()
    /// });
    /// let html = renderer.render_to_string(src);
    /// assert_eq!(
    ///     html,
    ///     concat!(
    ///         "\t\t<blockquote>\n",
    ///         "\t\t\t<p>a</p>\n",
    ///         "\t\t</blockquote>\n",
    ///     ),
    /// );
    /// ```
    pub initial_level: usize,
}

impl Default for Indentation {
    fn default() -> Self {
        Self {
            string: "\t".to_string(),
            initial_level: 0,
        }
    }
}

/// [`Render`] implementor that writes HTML output.
///
/// By default, block elements are placed on separate lines. To configure the formatting of the
/// output, see the [`Renderer::minified`] and [`Renderer::indented`] constructors.
pub struct Renderer<'s, W> {
    indent: Option<Indentation>,
    writer: Writer<'s>,
    output: W,
}

impl<'s> Renderer<'s, String> {
    fn new(indent: Option<Indentation>) -> Self {
        Self {
            writer: Writer::new(&indent),
            indent,
            output: String::new(),
        }
    }

    /// Create a renderer that emits no whitespace between elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = concat!(
    ///     "- a\n",
    ///     "\n",
    ///     "  - b\n",
    ///     "\n",
    ///     "  - c\n",
    /// );
    /// let renderer = Renderer::minified();
    /// let actual = renderer.render_to_string(src);
    /// let expected =
    ///     "<ul><li>a<ul><li><p>b</p></li><li><p>c</p></li></ul></li></ul>";
    /// assert_eq!(actual, expected);
    /// ```
    #[must_use]
    pub fn minified() -> Self {
        Self::new(None)
    }

    /// Create a renderer that indents lines based on their block element depth.
    ///
    /// See the [`Indentation`] struct for indentation options.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = concat!(
    ///     "- a\n",
    ///     "\n",
    ///     "  - b\n",
    ///     "\n",
    ///     "  - c\n",
    /// );
    /// let renderer = Renderer::indented(Indentation::default());
    /// let actual = renderer.render_to_string(src);
    /// let expected = concat!(
    ///     "<ul>\n",
    ///     "\t<li>\n",
    ///     "\t\ta\n",
    ///     "\t\t<ul>\n",
    ///     "\t\t\t<li>\n",
    ///     "\t\t\t\t<p>b</p>\n",
    ///     "\t\t\t</li>\n",
    ///     "\t\t\t<li>\n",
    ///     "\t\t\t\t<p>c</p>\n",
    ///     "\t\t\t</li>\n",
    ///     "\t\t</ul>\n",
    ///     "\t</li>\n",
    ///     "</ul>\n",
    /// );
    /// assert_eq!(actual, expected);
    /// ```
    #[must_use]
    pub fn indented(indent: Indentation) -> Self {
        Self::new(Some(indent))
    }

    pub fn render_to_string(self, input: &str) -> String {
        use super::RenderExt;
        let mut s = self.with_fmt_writer(String::new());
        s.render_document(input).expect("Can't fail");

        s.into_inner()
    }

    pub fn render_events_to_string<I>(self, events: I) -> String
    where
        I: Iterator<Item = Event<'s>>,
    {
        use super::RenderExt;
        let mut s = self.with_fmt_writer(String::new());
        s.render_events(events).expect("Can't fail");

        s.into_inner()
    }
}

impl<'s> Default for Renderer<'s, String> {
    /// Place block elements on separate lines.
    ///
    /// This is the default behavior and matches the reference implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jotdown::*;
    /// # use jotdown::html::*;
    /// let src = concat!(
    ///     "- a\n",
    ///     "\n",
    ///     "  - b\n",
    ///     "\n",
    ///     "  - c\n",
    /// );
    /// let renderer = Renderer::default();
    /// let actual = renderer.render_to_string(src);
    /// let expected = concat!(
    ///     "<ul>\n",
    ///     "<li>\n",
    ///     "a\n",
    ///     "<ul>\n",
    ///     "<li>\n",
    ///     "<p>b</p>\n",
    ///     "</li>\n",
    ///     "<li>\n",
    ///     "<p>c</p>\n",
    ///     "</li>\n",
    ///     "</ul>\n",
    ///     "</li>\n",
    ///     "</ul>\n",
    /// );
    /// assert_eq!(actual, expected);
    /// ```
    fn default() -> Self {
        Renderer::new(Some(Indentation {
            string: String::new(),
            initial_level: 0,
        }))
    }
}

impl<'s, W> Renderer<'s, W> {
    pub fn into_inner(self) -> W {
        self.output
    }
}

pub struct WriteAdapter<T: std::io::Write>(T);

struct WriteAdapterInner<T: std::io::Write> {
    inner: T,
    error: std::io::Result<()>,
}

impl<T: std::io::Write> WriteAdapterInner<T> {
    fn new(output: T) -> Self {
        Self {
            inner: output,
            error: Ok(()),
        }
    }
}
impl<T: std::io::Write> std::fmt::Write for WriteAdapterInner<T> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.inner.write_all(s.as_bytes()).map_err(|e| {
            self.error = Err(e);
            std::fmt::Error
        })
    }
}

impl<'s, W> Renderer<'s, W> {
    pub fn with_io_writer<NewWriter>(
        self,
        output: NewWriter,
    ) -> Renderer<'s, WriteAdapter<NewWriter>>
    where
        NewWriter: std::io::Write,
    {
        let Renderer {
            indent,
            writer,
            output: _,
        } = self;

        let output = WriteAdapter(output);
        Renderer {
            indent,
            writer,
            output,
        }
    }

    pub fn with_fmt_writer<NewWriter>(self, output: NewWriter) -> Renderer<'s, NewWriter>
    where
        NewWriter: std::fmt::Write,
    {
        let Renderer {
            indent,
            writer,
            output: _,
        } = self;

        Renderer {
            indent,
            writer,
            output,
        }
    }
}

impl<'s, W> Render<'s> for Renderer<'s, W>
where
    W: std::fmt::Write,
{
    type Error = std::fmt::Error;

    fn begin(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Called iteratively with every single event emitted by parsing djot document
    fn emit(&mut self, event: Event<'s>) -> Result<(), Self::Error> {
        self.writer
            .render_event(event, &mut self.output, &self.indent)
    }

    /// Called at the end of rendering a djot document
    fn finish(&mut self) -> Result<(), Self::Error> {
        self.writer.render_epilogue(&mut self.output, &self.indent)
    }
}

impl<'s, W> Render<'s> for Renderer<'s, WriteAdapter<W>>
where
    W: std::io::Write,
{
    type Error = std::io::Error;

    fn begin(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Called iteratively with every single event emitted by parsing djot document
    fn emit(&mut self, event: Event<'s>) -> Result<(), Self::Error> {
        let mut adapter = WriteAdapterInner::new(&mut self.output.0);
        self.writer
            .render_event(event, &mut adapter, &self.indent)
            .map_err(|_| adapter.error.expect_err("Inner adapter always sets error"))
    }

    /// Called at the end of rendering a djot document
    fn finish(&mut self) -> Result<(), Self::Error> {
        let mut adapter = WriteAdapterInner::new(&mut self.output.0);
        self.writer
            .render_epilogue(&mut adapter, &self.indent)
            .map_err(|_| adapter.error.expect_err("Inner adapter always sets error"))
    }
}

enum Raw {
    None,
    Html,
    Other,
}

impl Default for Raw {
    fn default() -> Self {
        Self::None
    }
}

struct Writer<'s> {
    depth: usize,
    raw: Raw,
    img_alt_text: usize,
    list_tightness: Vec<bool>,
    first_line: bool,
    ignore: bool,
    containers: Vec<Container<'s>>,
    footnotes: Footnotes<'s>,
}

impl<'s> Writer<'s> {
    fn new(indent: &Option<Indentation>) -> Self {
        let depth = if let Some(indent) = indent {
            indent.initial_level
        } else {
            0
        };
        Self {
            depth,
            raw: Raw::default(),
            img_alt_text: 0,
            list_tightness: Vec::new(),
            first_line: true,
            ignore: false,
            containers: vec![],
            footnotes: Footnotes::default(),
        }
    }

    fn block<W>(
        &mut self,
        mut out: W,
        indent: &Option<Indentation>,
        depth_change: isize,
    ) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if indent.is_none() {
            return Ok(());
        }

        if !self.first_line {
            out.write_char('\n')?;
        }

        let next_depth = (self.depth as isize + depth_change) as usize;
        if depth_change < 0 {
            self.depth = next_depth;
        }
        self.indent(&mut out, indent)?;
        if depth_change > 0 {
            self.depth = next_depth;
        }

        Ok(())
    }

    fn indent<W>(&self, mut out: W, indent: &Option<Indentation>) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if let Some(indent) = indent {
            if !indent.string.is_empty() {
                for _ in 0..self.depth {
                    out.write_str(&indent.string)?;
                }
            }
        }
        Ok(())
    }

    fn render_event<W>(
        &mut self,
        e: Event<'s>,
        out: W,
        indent: &Option<Indentation>,
    ) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        let c = if e == Event::End {
            self.containers.pop()
        } else {
            None
        };

        let push = if let Event::Start(c, ..) = &e {
            Some(c.clone())
        } else {
            None
        };

        let res = self.render_event_inner(e, c, out, indent);

        if let Some(p) = push {
            self.containers.push(p);
        }

        res
    }

    fn render_event_inner<W>(
        &mut self,
        e: Event<'s>,
        end_container: Option<Container>,
        mut out: W,
        indent: &Option<Indentation>,
    ) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if let Event::Start(Container::Footnote { label }, ..) = e {
            self.footnotes.start(label.clone(), Vec::new());
            return Ok(());
        } else if let Some(events) = self.footnotes.current() {
            if matches!(e, Event::End)
                && matches!(
                    end_container.as_ref().expect("Missing container"),
                    Container::Footnote { .. }
                )
            {
                self.footnotes.end();
            } else {
                events.push(e.clone());
            }
            return Ok(());
        }

        if let Event::Start(Container::LinkDefinition { .. }, ..) = e {
            self.ignore = true;
            return Ok(());
        }

        if matches!(e, Event::End)
            && matches!(
                end_container.as_ref().expect("Missing container"),
                Container::LinkDefinition { .. }
            )
        {
            self.ignore = false;
            return Ok(());
        }

        if self.ignore {
            return Ok(());
        }

        match e {
            Event::Start(c, attrs) => {
                if c.is_block() {
                    self.block(&mut out, indent, c.is_block_container().into())?;
                }
                if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                    return Ok(());
                }
                match &c {
                    Container::Blockquote => out.write_str("<blockquote")?,
                    Container::List { kind, tight } => {
                        self.list_tightness.push(*tight);
                        match kind {
                            ListKind::Unordered(..) | ListKind::Task(..) => out.write_str("<ul")?,
                            ListKind::Ordered {
                                numbering, start, ..
                            } => {
                                out.write_str("<ol")?;
                                if *start > 1 {
                                    write!(out, r#" start="{}""#, start)?;
                                }
                                if let Some(ty) = match numbering {
                                    Decimal => None,
                                    AlphaLower => Some('a'),
                                    AlphaUpper => Some('A'),
                                    RomanLower => Some('i'),
                                    RomanUpper => Some('I'),
                                } {
                                    write!(out, r#" type="{}""#, ty)?;
                                }
                            }
                        }
                    }
                    Container::ListItem | Container::TaskListItem { .. } => {
                        out.write_str("<li")?;
                    }
                    Container::DescriptionList => out.write_str("<dl")?,
                    Container::DescriptionDetails => out.write_str("<dd")?,
                    Container::Footnote { .. } => unreachable!(),
                    Container::Table => out.write_str("<table")?,
                    Container::TableRow { .. } => out.write_str("<tr")?,
                    Container::Section { .. } => out.write_str("<section")?,
                    Container::Div { .. } => out.write_str("<div")?,
                    Container::Paragraph => {
                        if matches!(self.list_tightness.last(), Some(true)) {
                            return Ok(());
                        }
                        out.write_str("<p")?;
                    }
                    Container::Heading { level, .. } => write!(out, "<h{}", level)?,
                    Container::TableCell { head: false, .. } => out.write_str("<td")?,
                    Container::TableCell { head: true, .. } => out.write_str("<th")?,
                    Container::Caption => out.write_str("<caption")?,
                    Container::DescriptionTerm => out.write_str("<dt")?,
                    Container::CodeBlock { .. } => out.write_str("<pre")?,
                    Container::Span | Container::Math { .. } => out.write_str("<span")?,
                    Container::Link(dst, ty) => {
                        if matches!(ty, LinkType::Span(SpanLinkType::Unresolved)) {
                            out.write_str("<a")?;
                        } else {
                            out.write_str(r#"<a href=""#)?;
                            if matches!(ty, LinkType::Email) {
                                out.write_str("mailto:")?;
                            }
                            write_attr(dst, &mut out)?;
                            out.write_char('"')?;
                        }
                    }
                    Container::Image(..) => {
                        self.img_alt_text += 1;
                        if self.img_alt_text == 1 {
                            out.write_str("<img")?;
                        } else {
                            return Ok(());
                        }
                    }
                    Container::Verbatim => out.write_str("<code")?,
                    Container::RawBlock { format } | Container::RawInline { format } => {
                        self.raw = if format == "html" {
                            Raw::Html
                        } else {
                            Raw::Other
                        };
                        return Ok(());
                    }
                    Container::Subscript => out.write_str("<sub")?,
                    Container::Superscript => out.write_str("<sup")?,
                    Container::Insert => out.write_str("<ins")?,
                    Container::Delete => out.write_str("<del")?,
                    Container::Strong => out.write_str("<strong")?,
                    Container::Emphasis => out.write_str("<em")?,
                    Container::Mark => out.write_str("<mark")?,
                    Container::LinkDefinition { .. } => return Ok(()),
                }

                let mut id_written = false;
                let mut class_written = false;
                for (a, v) in attrs.unique_pairs() {
                    write!(out, r#" {}=""#, a)?;
                    v.parts().try_for_each(|part| write_attr(part, &mut out))?;
                    match a {
                        "class" => {
                            class_written = true;
                            write_class(&c, true, &mut out)?;
                        }
                        "id" => id_written = true,
                        _ => {}
                    }
                    out.write_char('"')?;
                }

                if let Container::Heading {
                    id,
                    has_section: false,
                    ..
                }
                | Container::Section { id } = &c
                {
                    if !id_written {
                        out.write_str(r#" id=""#)?;
                        write_attr(id, &mut out)?;
                        out.write_char('"')?;
                    }
                } else if (matches!(c.clone(), Container::Div { class } if !class.is_empty())
                    || matches!(
                        c,
                        Container::Math { .. }
                            | Container::List {
                                kind: ListKind::Task(..),
                                ..
                            }
                    ))
                    && !class_written
                {
                    out.write_str(r#" class=""#)?;
                    write_class(&c, false, &mut out)?;
                    out.write_char('"')?;
                }

                match c {
                    Container::TableCell { alignment, .. }
                        if !matches!(alignment, Alignment::Unspecified) =>
                    {
                        let a = match alignment {
                            Alignment::Unspecified => unreachable!(),
                            Alignment::Left => "left",
                            Alignment::Center => "center",
                            Alignment::Right => "right",
                        };
                        write!(out, r#" style="text-align: {};">"#, a)?;
                    }
                    Container::CodeBlock { language } => {
                        if language.is_empty() {
                            out.write_str("><code>")?;
                        } else {
                            out.write_str(r#"><code class="language-"#)?;
                            write_attr(&language, &mut out)?;
                            out.write_str(r#"">"#)?;
                        }
                    }
                    Container::Image(..) => {
                        if self.img_alt_text == 1 {
                            out.write_str(r#" alt=""#)?;
                        }
                    }
                    Container::Math { display } => {
                        out.write_str(if display { r">\[" } else { r">\(" })?;
                    }
                    Container::TaskListItem { checked } => {
                        out.write_char('>')?;
                        self.block(&mut out, indent, 0)?;
                        if checked {
                            out.write_str(r#"<input disabled="" type="checkbox" checked=""/>"#)?;
                        } else {
                            out.write_str(r#"<input disabled="" type="checkbox"/>"#)?;
                        }
                    }
                    _ => out.write_char('>')?,
                }
            }
            Event::End => {
                let c = end_container.expect("Missing removed container");
                if c.is_block_container() {
                    self.block(&mut out, indent, -1)?;
                }
                if self.img_alt_text > 0 && !matches!(c, Container::Image { .. }) {
                    return Ok(());
                }
                match c {
                    Container::Blockquote => out.write_str("</blockquote>")?,
                    Container::List { kind, .. } => {
                        self.list_tightness.pop();
                        match kind {
                            ListKind::Unordered(..) | ListKind::Task(..) => {
                                out.write_str("</ul>")?;
                            }
                            ListKind::Ordered { .. } => out.write_str("</ol>")?,
                        }
                    }
                    Container::ListItem | Container::TaskListItem { .. } => {
                        out.write_str("</li>")?;
                    }
                    Container::DescriptionList => out.write_str("</dl>")?,
                    Container::DescriptionDetails => out.write_str("</dd>")?,
                    Container::Footnote { .. } => unreachable!(),
                    Container::Table => out.write_str("</table>")?,
                    Container::TableRow { .. } => out.write_str("</tr>")?,
                    Container::Section { .. } => out.write_str("</section>")?,
                    Container::Div { .. } => out.write_str("</div>")?,
                    Container::Paragraph => {
                        if matches!(self.list_tightness.last(), Some(true)) {
                            return Ok(());
                        }
                        if !self.footnotes.in_epilogue() {
                            out.write_str("</p>")?;
                        }
                    }
                    Container::Heading { level, .. } => write!(out, "</h{}>", level)?,
                    Container::TableCell { head: false, .. } => out.write_str("</td>")?,
                    Container::TableCell { head: true, .. } => out.write_str("</th>")?,
                    Container::Caption => out.write_str("</caption>")?,
                    Container::DescriptionTerm => out.write_str("</dt>")?,
                    Container::CodeBlock { .. } => out.write_str("</code></pre>")?,
                    Container::Span => out.write_str("</span>")?,
                    Container::Link { .. } => out.write_str("</a>")?,
                    Container::Image(src, _) => {
                        if self.img_alt_text == 1 {
                            if !src.is_empty() {
                                out.write_str(r#"" src=""#)?;
                                write_attr(&src, &mut out)?;
                            }
                            out.write_str(r#"">"#)?;
                        }
                        self.img_alt_text -= 1;
                    }
                    Container::Verbatim => out.write_str("</code>")?,
                    Container::Math { display } => {
                        out.write_str(if display { r"\]</span>" } else { r"\)</span>" })?;
                    }
                    Container::RawBlock { .. } | Container::RawInline { .. } => {
                        self.raw = Raw::None;
                    }
                    Container::Subscript => out.write_str("</sub>")?,
                    Container::Superscript => out.write_str("</sup>")?,
                    Container::Insert => out.write_str("</ins>")?,
                    Container::Delete => out.write_str("</del>")?,
                    Container::Strong => out.write_str("</strong>")?,
                    Container::Emphasis => out.write_str("</em>")?,
                    Container::Mark => out.write_str("</mark>")?,
                    Container::LinkDefinition { .. } => unreachable!(),
                }
            }
            Event::Str(s) => match self.raw {
                Raw::None if self.img_alt_text > 0 => write_attr(&s, &mut out)?,
                Raw::None => write_text(&s, &mut out)?,
                Raw::Html => out.write_str(&s)?,
                Raw::Other => {}
            },
            Event::FootnoteReference(label) => {
                let number = self.footnotes.reference(label.clone());
                if self.img_alt_text == 0 {
                    write!(
                        out,
                        r##"<a id="fnref{}" href="#fn{}" role="doc-noteref"><sup>{}</sup></a>"##,
                        number, number, number
                    )?;
                }
            }
            Event::Symbol(sym) => write!(out, ":{}:", sym)?,
            Event::LeftSingleQuote => out.write_str("‘")?,
            Event::RightSingleQuote => out.write_str("’")?,
            Event::LeftDoubleQuote => out.write_str("“")?,
            Event::RightDoubleQuote => out.write_str("”")?,
            Event::Ellipsis => out.write_str("…")?,
            Event::EnDash => out.write_str("–")?,
            Event::EmDash => out.write_str("—")?,
            Event::NonBreakingSpace => out.write_str("&nbsp;")?,
            Event::Hardbreak => {
                out.write_str("<br>")?;
                self.block(out, indent, 0)?;
            }
            Event::Softbreak => {
                out.write_char('\n')?;
                self.indent(&mut out, indent)?;
            }
            Event::Escape | Event::Blankline | Event::Attributes(..) => {}
            Event::ThematicBreak(attrs) => {
                self.block(&mut out, indent, 0)?;
                out.write_str("<hr")?;
                for (a, v) in attrs.unique_pairs() {
                    write!(out, r#" {}=""#, a)?;
                    v.parts().try_for_each(|part| write_attr(part, &mut out))?;
                    out.write_char('"')?;
                }
                out.write_str(">")?;
            }
        }
        self.first_line = false;

        Ok(())
    }

    fn render_epilogue<W>(&mut self, mut out: W, indent: &Option<Indentation>) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if self.footnotes.reference_encountered() {
            self.block(&mut out, indent, 0)?;
            out.write_str("<section role=\"doc-endnotes\">")?;
            self.block(&mut out, indent, 0)?;
            out.write_str("<hr>")?;
            self.block(&mut out, indent, 0)?;
            out.write_str("<ol>")?;

            while let Some((number, events)) = self.footnotes.next() {
                self.block(&mut out, indent, 0)?;
                write!(out, "<li id=\"fn{}\">", number)?;

                let mut unclosed_para = false;
                for e in events.into_iter().flatten() {
                    if matches!(&e, Event::Blankline | Event::Escape) {
                        continue;
                    }
                    if unclosed_para {
                        // not a footnote, so no need to add href before para close
                        out.write_str("</p>")?;
                    }
                    let is_end_paragraph = matches!(e, Event::End)
                        && self.containers.last() == Some(&Container::Paragraph);
                    self.render_event(e, &mut out, indent)?;
                    unclosed_para =
                        is_end_paragraph && !matches!(self.list_tightness.last(), Some(true));
                }
                if !unclosed_para {
                    // create a new paragraph
                    self.block(&mut out, indent, 0)?;
                    out.write_str("<p>")?;
                }
                write!(
                    out,
                    "<a href=\"#fnref{}\" role=\"doc-backlink\">\u{21A9}\u{FE0E}</a></p>",
                    number,
                )?;

                self.block(&mut out, indent, 0)?;
                out.write_str("</li>")?;
            }

            self.block(&mut out, indent, 0)?;
            out.write_str("</ol>")?;
            self.block(&mut out, indent, 0)?;
            out.write_str("</section>")?;
        }

        if indent.is_some() {
            out.write_char('\n')?;
        }

        Ok(())
    }
}

fn write_class<W>(c: &Container, mut first_written: bool, out: &mut W) -> std::fmt::Result
where
    W: std::fmt::Write,
{
    if let Some(cls) = match c {
        Container::List {
            kind: ListKind::Task(..),
            ..
        } => Some("task-list"),
        Container::Math { display: false } => Some("math inline"),
        Container::Math { display: true } => Some("math display"),
        _ => None,
    } {
        first_written = true;
        out.write_str(cls)?;
    }
    if let Container::Div { class } = c {
        if !class.is_empty() {
            if first_written {
                out.write_char(' ')?;
            }
            out.write_str(class)?;
        }
    }
    Ok(())
}

fn write_text<W>(s: &str, out: W) -> std::fmt::Result
where
    W: std::fmt::Write,
{
    write_escape(s, false, out)
}

fn write_attr<W>(s: &str, out: W) -> std::fmt::Result
where
    W: std::fmt::Write,
{
    write_escape(s, true, out)
}

fn write_escape<W>(mut s: &str, escape_quotes: bool, mut out: W) -> std::fmt::Result
where
    W: std::fmt::Write,
{
    let mut ent = "";
    while let Some(i) = s.find(|c| {
        match c {
            '<' => Some("&lt;"),
            '>' => Some("&gt;"),
            '&' => Some("&amp;"),
            '"' if escape_quotes => Some("&quot;"),
            _ => None,
        }
        .map_or(false, |s| {
            ent = s;
            true
        })
    }) {
        out.write_str(&s[..i])?;
        out.write_str(ent)?;
        s = &s[i + 1..];
    }
    out.write_str(s)
}

/// Helper to aggregate footnotes for rendering at the end of the document. It will cache footnote
/// events until they should be emitted at the end.
///
/// When footnotes should be rendered, they can be pulled with the [`Footnotes::next`] function in
/// the order they were first referenced.
#[derive(Default)]
struct Footnotes<'s> {
    /// Stack of current open footnotes, with label and staging buffer.
    open: Vec<(CowStr<'s>, Vec<Event<'s>>)>,
    /// Footnote references in the order they were first encountered.
    references: Vec<CowStr<'s>>,
    /// Events for each footnote.
    events: Map<CowStr<'s>, Vec<Event<'s>>>,
    /// Number of last footnote that was emitted.
    number: usize,
}

impl<'s> Footnotes<'s> {
    /// Returns `true` if any reference has been encountered.
    fn reference_encountered(&self) -> bool {
        !self.references.is_empty()
    }

    /// Returns `true` if within the epilogue, i.e. if any footnotes have been pulled.
    fn in_epilogue(&self) -> bool {
        self.number > 0
    }

    /// Add a footnote reference.
    fn reference(&mut self, label: CowStr<'s>) -> usize {
        self.references
            .iter()
            .position(|t| *t == label)
            .map_or_else(
                || {
                    self.references.push(label);
                    self.references.len()
                },
                |i| i + 1,
            )
    }

    /// Start aggregating a footnote.
    fn start(&mut self, label: CowStr<'s>, events: Vec<Event<'s>>) {
        self.open.push((label, events));
    }

    /// Obtain the current (most recently started) footnote.
    fn current(&mut self) -> Option<&mut Vec<Event<'s>>> {
        self.open.last_mut().map(|(_, e)| e)
    }

    /// End the current (most recently started) footnote.
    fn end(&mut self) {
        let (label, stage) = self.open.pop().unwrap();
        self.events.insert(label, stage);
    }
}

impl<'s> Iterator for Footnotes<'s> {
    type Item = (usize, Option<Vec<Event<'s>>>);

    fn next(&mut self) -> Option<Self::Item> {
        self.references.get(self.number).map(|label| {
            self.number += 1;
            (self.number, self.events.remove(label))
        })
    }
}
