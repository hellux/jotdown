//! An HTML renderer that takes an iterator of [`Event`]s and emits HTML.

use crate::Alignment;
use crate::Container;
use crate::Event;
use crate::LinkType;
use crate::ListKind;
use crate::Map;
use crate::OrderedListNumbering::*;
use crate::Render;
use crate::SpanLinkType;

/// [`Render`] implementor that writes HTML output.
#[derive(Default)]
pub struct Renderer {}

impl Render for Renderer {
    fn push<'s, I, W>(&self, mut events: I, mut out: W) -> std::fmt::Result
    where
        I: Iterator<Item = Event<'s>>,
        W: std::fmt::Write,
    {
        let mut w = Writer::default();
        events.try_for_each(|e| w.render_event(&e, &mut out))?;
        w.render_epilogue(&mut out)
    }

    fn push_borrowed<'s, E, I, W>(&self, mut events: I, mut out: W) -> std::fmt::Result
    where
        E: AsRef<Event<'s>>,
        I: Iterator<Item = E>,
        W: std::fmt::Write,
    {
        let mut w = Writer::default();
        events.try_for_each(|e| w.render_event(e.as_ref(), &mut out))?;
        w.render_epilogue(&mut out)
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

#[derive(Default)]
struct Writer<'s> {
    raw: Raw,
    img_alt_text: usize,
    list_tightness: Vec<bool>,
    not_first_line: bool,
    ignore: bool,
    footnotes: Footnotes<'s>,
}

impl<'s> Writer<'s> {
    fn render_event<W>(&mut self, e: &Event<'s>, mut out: W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if let Event::Start(Container::Footnote { label }, ..) = e {
            self.footnotes.start(label, Vec::new());
            return Ok(());
        } else if let Some(events) = self.footnotes.current() {
            if matches!(e, Event::End(Container::Footnote { .. })) {
                self.footnotes.end();
            } else {
                events.push(e.clone());
            }
            return Ok(());
        }

        if matches!(&e, Event::Start(Container::LinkDefinition { .. }, ..)) {
            self.ignore = true;
            return Ok(());
        }

        if matches!(&e, Event::End(Container::LinkDefinition { .. })) {
            self.ignore = false;
            return Ok(());
        }

        if self.ignore {
            return Ok(());
        }

        match e {
            Event::Start(c, attrs) => {
                if c.is_block() && self.not_first_line {
                    out.write_char('\n')?;
                }
                if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                    return Ok(());
                }
                match &c {
                    Container::Blockquote => out.write_str("<blockquote")?,
                    Container::List { kind, tight } => {
                        self.list_tightness.push(*tight);
                        match kind {
                            ListKind::Unordered | ListKind::Task => out.write_str("<ul")?,
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
                        self.raw = if format == &"html" {
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

                for (a, v) in attrs.into_iter().filter(|(a, _)| *a != "class") {
                    write!(out, r#" {}=""#, a)?;
                    v.parts().try_for_each(|part| write_attr(part, &mut out))?;
                    out.write_char('"')?;
                }

                if let Container::Heading {
                    id,
                    has_section: false,
                    ..
                }
                | Container::Section { id } = &c
                {
                    if !attrs.into_iter().any(|(a, _)| a == "id") {
                        out.write_str(r#" id=""#)?;
                        write_attr(id, &mut out)?;
                        out.write_char('"')?;
                    }
                }

                if attrs.into_iter().any(|(a, _)| a == "class")
                    || matches!(
                        c,
                        Container::Div { class } if !class.is_empty())
                    || matches!(c, |Container::Math { .. }| Container::List {
                        kind: ListKind::Task,
                        ..
                    } | Container::TaskListItem { .. })
                {
                    out.write_str(r#" class=""#)?;
                    let mut first_written = false;
                    if let Some(cls) = match c {
                        Container::List {
                            kind: ListKind::Task,
                            ..
                        } => Some("task-list"),
                        Container::TaskListItem { checked: false } => Some("unchecked"),
                        Container::TaskListItem { checked: true } => Some("checked"),
                        Container::Math { display: false } => Some("math inline"),
                        Container::Math { display: true } => Some("math display"),
                        _ => None,
                    } {
                        first_written = true;
                        out.write_str(cls)?;
                    }
                    for cls in attrs
                        .into_iter()
                        .filter(|(a, _)| a == &"class")
                        .map(|(_, cls)| cls)
                    {
                        if first_written {
                            out.write_char(' ')?;
                        }
                        first_written = true;
                        cls.parts()
                            .try_for_each(|part| write_attr(part, &mut out))?;
                    }
                    // div class goes after classes from attrs
                    if let Container::Div { class } = c {
                        if !class.is_empty() {
                            if first_written {
                                out.write_char(' ')?;
                            }
                            out.write_str(class)?;
                        }
                    }
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
                            write_attr(language, &mut out)?;
                            out.write_str(r#"">"#)?;
                        }
                    }
                    Container::Image(..) => {
                        if self.img_alt_text == 1 {
                            out.write_str(r#" alt=""#)?;
                        }
                    }
                    Container::Math { display } => {
                        out.write_str(if *display { r#">\["# } else { r#">\("# })?;
                    }
                    _ => out.write_char('>')?,
                }
            }
            Event::End(c) => {
                if c.is_block_container() {
                    out.write_char('\n')?;
                }
                if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                    return Ok(());
                }
                match c {
                    Container::Blockquote => out.write_str("</blockquote>")?,
                    Container::List { kind, .. } => {
                        self.list_tightness.pop();
                        match kind {
                            ListKind::Unordered | ListKind::Task => out.write_str("</ul>")?,
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
                    Container::Link(..) => out.write_str("</a>")?,
                    Container::Image(src, ..) => {
                        if self.img_alt_text == 1 {
                            if !src.is_empty() {
                                out.write_str(r#"" src=""#)?;
                                write_attr(src, &mut out)?;
                            }
                            out.write_str(r#"">"#)?;
                        }
                        self.img_alt_text -= 1;
                    }
                    Container::Verbatim => out.write_str("</code>")?,
                    Container::Math { display } => {
                        out.write_str(if *display {
                            r#"\]</span>"#
                        } else {
                            r#"\)</span>"#
                        })?;
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
                Raw::None if self.img_alt_text > 0 => write_attr(s, &mut out)?,
                Raw::None => write_text(s, &mut out)?,
                Raw::Html => out.write_str(s)?,
                Raw::Other => {}
            },
            Event::FootnoteReference(label) => {
                let number = self.footnotes.reference(label);
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
            Event::Hardbreak => out.write_str("<br>\n")?,
            Event::Softbreak => out.write_char('\n')?,
            Event::Escape | Event::Blankline => {}
            Event::ThematicBreak(attrs) => {
                if self.not_first_line {
                    out.write_char('\n')?;
                }
                out.write_str("<hr")?;
                for (a, v) in attrs {
                    write!(out, r#" {}=""#, a)?;
                    v.parts().try_for_each(|part| write_attr(part, &mut out))?;
                    out.write_char('"')?;
                }
                out.write_str(">")?;
            }
        }
        self.not_first_line = true;

        Ok(())
    }

    fn render_epilogue<W>(&mut self, mut out: W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if self.footnotes.reference_encountered() {
            out.write_str("\n<section role=\"doc-endnotes\">\n<hr>\n<ol>")?;

            while let Some((number, events)) = self.footnotes.next() {
                write!(out, "\n<li id=\"fn{}\">", number)?;

                let mut unclosed_para = false;
                for e in events.iter().flatten() {
                    if matches!(&e, Event::Blankline | Event::Escape) {
                        continue;
                    }
                    if unclosed_para {
                        // not a footnote, so no need to add href before para close
                        out.write_str("</p>")?;
                    }
                    self.render_event(e, &mut out)?;
                    unclosed_para = matches!(e, Event::End(Container::Paragraph { .. }))
                        && !matches!(self.list_tightness.last(), Some(true));
                }
                if !unclosed_para {
                    // create a new paragraph
                    out.write_str("\n<p>")?;
                }
                write!(
                    out,
                    r##"<a href="#fnref{}" role="doc-backlink">↩︎︎</a></p>"##,
                    number,
                )?;

                out.write_str("\n</li>")?;
            }

            out.write_str("\n</ol>\n</section>")?;
        }

        out.write_char('\n')?;

        Ok(())
    }
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
    open: Vec<(&'s str, Vec<Event<'s>>)>,
    /// Footnote references in the order they were first encountered.
    references: Vec<&'s str>,
    /// Events for each footnote.
    events: Map<&'s str, Vec<Event<'s>>>,
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
    fn reference(&mut self, label: &'s str) -> usize {
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
    fn start(&mut self, label: &'s str, events: Vec<Event<'s>>) {
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
