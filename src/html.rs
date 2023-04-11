//! An HTML renderer that takes an iterator of [`Event`]s and emits HTML.

use crate::Alignment;
use crate::Container;
use crate::Event;
use crate::LinkType;
use crate::ListKind;
use crate::OrderedListNumbering::*;
use crate::Render;
use crate::SpanLinkType;

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
pub struct Renderer {
    raw: Raw,
    img_alt_text: usize,
    list_tightness: Vec<bool>,
    encountered_footnote: bool,
    footnote_number: Option<std::num::NonZeroUsize>,
    not_first_line: bool,
    close_para: bool,
}

impl Render for Renderer {
    fn render_event<'s, W>(&mut self, e: &Event<'s>, mut out: W) -> std::fmt::Result
    where
        W: std::fmt::Write,
    {
        if matches!(&e, Event::Blankline | Event::Escape) {
            return Ok(());
        }

        let close_para = self.close_para;
        if close_para {
            self.close_para = false;
            if !matches!(&e, Event::End(Container::Footnote { .. })) {
                // no need to add href before para close
                out.write_str("</p>")?;
            }
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
                    Container::Footnote { number, .. } => {
                        debug_assert!(self.footnote_number.is_none());
                        self.footnote_number = Some((*number).try_into().unwrap());
                        if !self.encountered_footnote {
                            self.encountered_footnote = true;
                            out.write_str("<section role=\"doc-endnotes\">\n<hr>\n<ol>\n")?;
                        }
                        write!(out, "<li id=\"fn{}\">", number)?;
                        return Ok(());
                    }
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
                }

                for (a, v) in attrs.iter().filter(|(a, _)| *a != "class") {
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
                    if !attrs.iter().any(|(a, _)| a == "id") {
                        out.write_str(r#" id=""#)?;
                        write_attr(id, &mut out)?;
                        out.write_char('"')?;
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
                        .iter()
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
                    if let Container::Div { class: Some(cls) } = c {
                        if first_written {
                            out.write_char(' ')?;
                        }
                        out.write_str(cls)?;
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
                    Container::CodeBlock { lang } => {
                        if let Some(l) = lang {
                            out.write_str(r#"><code class="language-"#)?;
                            write_attr(l, &mut out)?;
                            out.write_str(r#"">"#)?;
                        } else {
                            out.write_str("><code>")?;
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
                if c.is_block_container() && !matches!(c, Container::Footnote { .. }) {
                    out.write_char('\n')?;
                }
                if self.img_alt_text > 0 && !matches!(c, Container::Image(..)) {
                    return Ok(());
                }
                match c {
                    Container::Blockquote => out.write_str("</blockquote>")?,
                    Container::List {
                        kind: ListKind::Unordered | ListKind::Task,
                        ..
                    } => {
                        self.list_tightness.pop();
                        out.write_str("</ul>")?;
                    }
                    Container::List {
                        kind: ListKind::Ordered { .. },
                        ..
                    } => out.write_str("</ol>")?,
                    Container::ListItem | Container::TaskListItem { .. } => {
                        out.write_str("</li>")?;
                    }
                    Container::DescriptionList => out.write_str("</dl>")?,
                    Container::DescriptionDetails => out.write_str("</dd>")?,
                    Container::Footnote { number, .. } => {
                        if !close_para {
                            // create a new paragraph
                            out.write_str("\n<p>")?;
                        }
                        write!(
                            out,
                            r##"<a href="#fnref{}" role="doc-backlink">↩︎︎</a></p>"##,
                            number,
                        )?;
                        out.write_str("\n</li>")?;
                        self.footnote_number = None;
                    }
                    Container::Table => out.write_str("</table>")?,
                    Container::TableRow { .. } => out.write_str("</tr>")?,
                    Container::Section { .. } => out.write_str("</section>")?,
                    Container::Div { .. } => out.write_str("</div>")?,
                    Container::Paragraph => {
                        if matches!(self.list_tightness.last(), Some(true)) {
                            return Ok(());
                        }
                        if self.footnote_number.is_none() {
                            out.write_str("</p>")?;
                        } else {
                            self.close_para = true;
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
                }
            }
            Event::Str(s) => match self.raw {
                Raw::None if self.img_alt_text > 0 => write_attr(s, &mut out)?,
                Raw::None => write_text(s, &mut out)?,
                Raw::Html => out.write_str(s)?,
                Raw::Other => {}
            },
            Event::FootnoteReference(_tag, number) => {
                if self.img_alt_text == 0 {
                    write!(
                        out,
                        r##"<a id="fnref{}" href="#fn{}" role="doc-noteref"><sup>{}</sup></a>"##,
                        number, number, number
                    )?;
                }
            }
            Event::Symbol(sym) => write!(out, ":{}:", sym)?,
            Event::LeftSingleQuote => out.write_str("&lsquo;")?,
            Event::RightSingleQuote => out.write_str("&rsquo;")?,
            Event::LeftDoubleQuote => out.write_str("&ldquo;")?,
            Event::RightDoubleQuote => out.write_str("&rdquo;")?,
            Event::Ellipsis => out.write_str("&hellip;")?,
            Event::EnDash => out.write_str("&ndash;")?,
            Event::EmDash => out.write_str("&mdash;")?,
            Event::NonBreakingSpace => out.write_str("&nbsp;")?,
            Event::Hardbreak => out.write_str("<br>\n")?,
            Event::Softbreak => out.write_char('\n')?,
            Event::Escape | Event::Blankline => unreachable!("filtered out"),
            Event::ThematicBreak(attrs) => {
                out.write_str("\n<hr")?;
                for (a, v) in attrs.iter() {
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
        if self.encountered_footnote {
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
