//! An HTML renderer that takes an iterator of [`Event`]s and emits HTML.
//!
//! The HTML can be written to either a [`std::fmt::Write`] or a [`std::io::Write`] object.
//!
//! # Examples
//!
//! Push to a [`String`] (implements [`std::fmt::Write`]):
//!
//! ```
//! # use jotdown::Render;
//! # let events = std::iter::empty();
//! let mut html = String::new();
//! jotdown::html::Renderer.push(events, &mut html);
//! ```
//!
//! Write to standard output with buffering ([`std::io::Stdout`] implements [`std::io::Write`]):
//!
//! ```
//! # use jotdown::Render;
//! # let events = std::iter::empty();
//! let mut out = std::io::BufWriter::new(std::io::stdout());
//! jotdown::html::Renderer.write(events, &mut out).unwrap();
//! ```

use crate::Alignment;
use crate::Container;
use crate::Event;
use crate::LinkType;
use crate::ListKind;
use crate::OrderedListNumbering::*;
use crate::Render;
use crate::SpanLinkType;

pub struct Renderer;

impl Render for Renderer {
    fn push<'s, I: Iterator<Item = Event<'s>>, W: std::fmt::Write>(
        &self,
        events: I,
        out: W,
    ) -> std::fmt::Result {
        Writer::new(events, out).write()
    }
}

enum Raw {
    None,
    Html,
    Other,
}

struct FilteredEvents<I> {
    events: I,
}

impl<'s, I: Iterator<Item = Event<'s>>> Iterator for FilteredEvents<I> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut ev = self.events.next();
        while matches!(ev, Some(Event::Blankline | Event::Escape)) {
            ev = self.events.next();
        }
        ev
    }
}

struct Writer<'s, I: Iterator<Item = Event<'s>>, W> {
    events: std::iter::Peekable<FilteredEvents<I>>,
    out: W,
    raw: Raw,
    img_alt_text: usize,
    list_tightness: Vec<bool>,
    encountered_footnote: bool,
    footnote_number: Option<std::num::NonZeroUsize>,
    first_line: bool,
    close_para: bool,
}

impl<'s, I: Iterator<Item = Event<'s>>, W: std::fmt::Write> Writer<'s, I, W> {
    fn new(events: I, out: W) -> Self {
        Self {
            events: FilteredEvents { events }.peekable(),
            out,
            raw: Raw::None,
            img_alt_text: 0,
            list_tightness: Vec::new(),
            encountered_footnote: false,
            footnote_number: None,
            first_line: true,
            close_para: false,
        }
    }

    fn write(&mut self) -> std::fmt::Result {
        while let Some(e) = self.events.next() {
            let close_para = self.close_para;
            if close_para {
                self.close_para = false;
                if !matches!(&e, Event::End(Container::Footnote { .. })) {
                    // no need to add href before para close
                    self.out.write_str("</p>")?;
                }
            }

            match e {
                Event::Start(c, attrs) => {
                    if c.is_block() && !self.first_line {
                        self.out.write_char('\n')?;
                    }
                    if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                        continue;
                    }
                    match &c {
                        Container::Blockquote => self.out.write_str("<blockquote")?,
                        Container::List { kind, tight } => {
                            self.list_tightness.push(*tight);
                            match kind {
                                ListKind::Unordered | ListKind::Task => {
                                    self.out.write_str("<ul")?
                                }
                                ListKind::Ordered {
                                    numbering, start, ..
                                } => {
                                    self.out.write_str("<ol")?;
                                    if *start > 1 {
                                        write!(self.out, r#" start="{}""#, start)?;
                                    }
                                    if let Some(ty) = match numbering {
                                        Decimal => None,
                                        AlphaLower => Some('a'),
                                        AlphaUpper => Some('A'),
                                        RomanLower => Some('i'),
                                        RomanUpper => Some('I'),
                                    } {
                                        write!(self.out, r#" type="{}""#, ty)?;
                                    }
                                }
                            }
                        }
                        Container::ListItem | Container::TaskListItem { .. } => {
                            self.out.write_str("<li")?;
                        }
                        Container::DescriptionList => self.out.write_str("<dl")?,
                        Container::DescriptionDetails => self.out.write_str("<dd")?,
                        Container::Footnote { number, .. } => {
                            assert!(self.footnote_number.is_none());
                            self.footnote_number = Some((*number).try_into().unwrap());
                            if !self.encountered_footnote {
                                self.encountered_footnote = true;
                                self.out
                                    .write_str("<section role=\"doc-endnotes\">\n<hr>\n<ol>\n")?;
                            }
                            write!(self.out, "<li id=\"fn{}\">", number)?;
                            continue;
                        }
                        Container::Table => self.out.write_str("<table")?,
                        Container::TableRow { .. } => self.out.write_str("<tr")?,
                        Container::Section { .. } => self.out.write_str("<section")?,
                        Container::Div { .. } => self.out.write_str("<div")?,
                        Container::Paragraph => {
                            if matches!(self.list_tightness.last(), Some(true)) {
                                continue;
                            }
                            self.out.write_str("<p")?;
                        }
                        Container::Heading { level, .. } => write!(self.out, "<h{}", level)?,
                        Container::TableCell { head: false, .. } => self.out.write_str("<td")?,
                        Container::TableCell { head: true, .. } => self.out.write_str("<th")?,
                        Container::Caption => self.out.write_str("<caption")?,
                        Container::DescriptionTerm => self.out.write_str("<dt")?,
                        Container::CodeBlock { .. } => self.out.write_str("<pre")?,
                        Container::Span | Container::Math { .. } => self.out.write_str("<span")?,
                        Container::Link(dst, ty) => {
                            if matches!(ty, LinkType::Span(SpanLinkType::Unresolved)) {
                                self.out.write_str("<a")?;
                            } else {
                                self.out.write_str(r#"<a href=""#)?;
                                if matches!(ty, LinkType::Email) {
                                    self.out.write_str("mailto:")?;
                                }
                                self.write_attr(dst)?;
                                self.out.write_char('"')?;
                            }
                        }
                        Container::Image(..) => {
                            self.img_alt_text += 1;
                            if self.img_alt_text == 1 {
                                self.out.write_str("<img")?;
                            } else {
                                continue;
                            }
                        }
                        Container::Verbatim => self.out.write_str("<code")?,
                        Container::RawBlock { format } | Container::RawInline { format } => {
                            self.raw = if format == &"html" {
                                Raw::Html
                            } else {
                                Raw::Other
                            };
                            continue;
                        }
                        Container::Subscript => self.out.write_str("<sub")?,
                        Container::Superscript => self.out.write_str("<sup")?,
                        Container::Insert => self.out.write_str("<ins")?,
                        Container::Delete => self.out.write_str("<del")?,
                        Container::Strong => self.out.write_str("<strong")?,
                        Container::Emphasis => self.out.write_str("<em")?,
                        Container::Mark => self.out.write_str("<mark")?,
                    }

                    for (a, v) in attrs.iter().filter(|(a, _)| *a != "class") {
                        write!(self.out, r#" {}=""#, a)?;
                        v.parts().try_for_each(|part| self.write_attr(part))?;
                        self.out.write_char('"')?;
                    }

                    if let Container::Heading {
                        id,
                        has_section: false,
                        ..
                    }
                    | Container::Section { id } = &c
                    {
                        if !attrs.iter().any(|(a, _)| a == "id") {
                            self.out.write_str(r#" id=""#)?;
                            self.write_attr(id)?;
                            self.out.write_char('"')?;
                        }
                    }

                    if attrs.iter().any(|(a, _)| a == "class")
                        || matches!(
                            c,
                            Container::Div { class: Some(_) }
                                | Container::Math { .. }
                                | Container::List {
                                    kind: ListKind::Task,
                                    ..
                                }
                                | Container::TaskListItem { .. }
                        )
                    {
                        self.out.write_str(r#" class=""#)?;
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
                            self.out.write_str(cls)?;
                        }
                        for cls in attrs
                            .iter()
                            .filter(|(a, _)| a == &"class")
                            .map(|(_, cls)| cls)
                        {
                            if first_written {
                                self.out.write_char(' ')?;
                            }
                            first_written = true;
                            cls.parts().try_for_each(|part| self.write_attr(part))?;
                        }
                        // div class goes after classes from attrs
                        if let Container::Div { class: Some(cls) } = c {
                            if first_written {
                                self.out.write_char(' ')?;
                            }
                            self.out.write_str(cls)?;
                        }
                        self.out.write_char('"')?;
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
                            write!(self.out, r#" style="text-align: {};">"#, a)?;
                        }
                        Container::CodeBlock { lang } => {
                            if let Some(l) = lang {
                                self.out.write_str(r#"><code class="language-"#)?;
                                self.write_attr(l)?;
                                self.out.write_str(r#"">"#)?;
                            } else {
                                self.out.write_str("><code>")?;
                            }
                        }
                        Container::Image(..) => {
                            if self.img_alt_text == 1 {
                                self.out.write_str(r#" alt=""#)?;
                            }
                        }
                        Container::Math { display } => {
                            self.out
                                .write_str(if display { r#">\["# } else { r#">\("# })?;
                        }
                        _ => self.out.write_char('>')?,
                    }
                }
                Event::End(c) => {
                    if c.is_block_container() && !matches!(c, Container::Footnote { .. }) {
                        self.out.write_char('\n')?;
                    }
                    if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                        continue;
                    }
                    match c {
                        Container::Blockquote => self.out.write_str("</blockquote>")?,
                        Container::List {
                            kind: ListKind::Unordered | ListKind::Task,
                            ..
                        } => {
                            self.list_tightness.pop();
                            self.out.write_str("</ul>")?;
                        }
                        Container::List {
                            kind: ListKind::Ordered { .. },
                            ..
                        } => self.out.write_str("</ol>")?,
                        Container::ListItem | Container::TaskListItem { .. } => {
                            self.out.write_str("</li>")?;
                        }
                        Container::DescriptionList => self.out.write_str("</dl>")?,
                        Container::DescriptionDetails => self.out.write_str("</dd>")?,
                        Container::Footnote { number, .. } => {
                            if !close_para {
                                // create a new paragraph
                                self.out.write_str("\n<p>")?;
                            }
                            write!(
                                self.out,
                                r##"<a href="#fnref{}" role="doc-backlink">↩︎︎</a></p>"##,
                                number,
                            )?;
                            self.out.write_str("\n</li>")?;
                            self.footnote_number = None;
                        }
                        Container::Table => self.out.write_str("</table>")?,
                        Container::TableRow { .. } => self.out.write_str("</tr>")?,
                        Container::Section { .. } => self.out.write_str("</section>")?,
                        Container::Div { .. } => self.out.write_str("</div>")?,
                        Container::Paragraph => {
                            if matches!(self.list_tightness.last(), Some(true)) {
                                continue;
                            }
                            if self.footnote_number.is_none() {
                                self.out.write_str("</p>")?;
                            } else {
                                self.close_para = true;
                            }
                        }
                        Container::Heading { level, .. } => write!(self.out, "</h{}>", level)?,
                        Container::TableCell { head: false, .. } => self.out.write_str("</td>")?,
                        Container::TableCell { head: true, .. } => self.out.write_str("</th>")?,
                        Container::Caption => self.out.write_str("</caption>")?,
                        Container::DescriptionTerm => self.out.write_str("</dt>")?,
                        Container::CodeBlock { .. } => self.out.write_str("</code></pre>")?,
                        Container::Span => self.out.write_str("</span>")?,
                        Container::Link(..) => self.out.write_str("</a>")?,
                        Container::Image(src, ..) => {
                            if self.img_alt_text == 1 {
                                if !src.is_empty() {
                                    self.out.write_str(r#"" src=""#)?;
                                    self.write_attr(&src)?;
                                }
                                self.out.write_str(r#"">"#)?;
                            }
                            self.img_alt_text -= 1;
                        }
                        Container::Verbatim => self.out.write_str("</code>")?,
                        Container::Math { display } => {
                            self.out.write_str(if display {
                                r#"\]</span>"#
                            } else {
                                r#"\)</span>"#
                            })?;
                        }
                        Container::RawBlock { .. } | Container::RawInline { .. } => {
                            self.raw = Raw::None;
                        }
                        Container::Subscript => self.out.write_str("</sub>")?,
                        Container::Superscript => self.out.write_str("</sup>")?,
                        Container::Insert => self.out.write_str("</ins>")?,
                        Container::Delete => self.out.write_str("</del>")?,
                        Container::Strong => self.out.write_str("</strong>")?,
                        Container::Emphasis => self.out.write_str("</em>")?,
                        Container::Mark => self.out.write_str("</mark>")?,
                    }
                }
                Event::Str(s) => match self.raw {
                    Raw::None if self.img_alt_text > 0 => self.write_attr(&s)?,
                    Raw::None => self.write_text(&s)?,
                    Raw::Html => self.out.write_str(&s)?,
                    Raw::Other => {}
                },
                Event::FootnoteReference(_tag, number) => {
                    if self.img_alt_text == 0 {
                        write!(
                            self.out,
                            r##"<a id="fnref{}" href="#fn{}" role="doc-noteref"><sup>{}</sup></a>"##,
                            number, number, number
                        )?;
                    }
                }
                Event::Symbol(sym) => write!(self.out, ":{}:", sym)?,
                Event::LeftSingleQuote => self.out.write_str("&lsquo;")?,
                Event::RightSingleQuote => self.out.write_str("&rsquo;")?,
                Event::LeftDoubleQuote => self.out.write_str("&ldquo;")?,
                Event::RightDoubleQuote => self.out.write_str("&rdquo;")?,
                Event::Ellipsis => self.out.write_str("&hellip;")?,
                Event::EnDash => self.out.write_str("&ndash;")?,
                Event::EmDash => self.out.write_str("&mdash;")?,
                Event::NonBreakingSpace => self.out.write_str("&nbsp;")?,
                Event::Hardbreak => self.out.write_str("<br>\n")?,
                Event::Softbreak => self.out.write_char('\n')?,
                Event::Escape | Event::Blankline => unreachable!("filtered out"),
                Event::ThematicBreak(attrs) => {
                    self.out.write_str("\n<hr")?;
                    for (a, v) in attrs.iter() {
                        write!(self.out, r#" {}=""#, a)?;
                        v.parts().try_for_each(|part| self.write_attr(part))?;
                        self.out.write_char('"')?;
                    }
                    self.out.write_str(">")?;
                }
            }
            self.first_line = false;
        }
        if self.encountered_footnote {
            self.out.write_str("\n</ol>\n</section>")?;
        }
        self.out.write_char('\n')?;
        Ok(())
    }

    fn write_escape(&mut self, mut s: &str, escape_quotes: bool) -> std::fmt::Result {
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
            self.out.write_str(&s[..i])?;
            self.out.write_str(ent)?;
            s = &s[i + 1..];
        }
        self.out.write_str(s)
    }

    fn write_text(&mut self, s: &str) -> std::fmt::Result {
        self.write_escape(s, false)
    }

    fn write_attr(&mut self, s: &str) -> std::fmt::Result {
        self.write_escape(s, true)
    }
}
