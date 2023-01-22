use crate::Atom;
use crate::Container;
use crate::Event;
use crate::ListKind;
use crate::OrderedListNumbering::*;

/// Generate HTML from parsed events and push it to a unicode-accepting buffer or stream.
pub fn push<'s, I: Iterator<Item = Event<'s>>, W: std::fmt::Write>(out: W, events: I) {
    Writer::new(events, out).write().unwrap();
}

/// Generate HTML from parsed events and write it to a byte sink, encoded as UTF-8.
///
/// NOTE: This performs many small writes, so IO writes should be buffered with e.g.
/// [`std::io::BufWriter`].
pub fn write<'s, I: Iterator<Item = Event<'s>>, W: std::io::Write>(
    mut out: W,
    events: I,
) -> std::io::Result<()> {
    struct Adapter<'a, T: ?Sized + 'a> {
        inner: &'a mut T,
        error: std::io::Result<()>,
    }

    impl<T: std::io::Write + ?Sized> std::fmt::Write for Adapter<'_, T> {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            match self.inner.write_all(s.as_bytes()) {
                Ok(()) => Ok(()),
                Err(e) => {
                    self.error = Err(e);
                    Err(std::fmt::Error)
                }
            }
        }
    }

    let mut output = Adapter {
        inner: &mut out,
        error: Ok(()),
    };

    Writer::new(events, &mut output)
        .write()
        .map_err(|_| output.error.unwrap_err())
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
        while matches!(ev, Some(Event::Atom(Atom::Blankline | Atom::Escape))) {
            ev = self.events.next();
        }
        ev
    }
}

struct Writer<'s, I: Iterator<Item = Event<'s>>, W> {
    events: std::iter::Peekable<FilteredEvents<I>>,
    out: W,
    raw: Raw,
    text_only: bool,
    list_tightness: Vec<bool>,
    encountered_footnote: bool,
    footnote_number: Option<std::num::NonZeroUsize>,
    footnote_backlink_written: bool,
}

impl<'s, I: Iterator<Item = Event<'s>>, W: std::fmt::Write> Writer<'s, I, W> {
    fn new(events: I, out: W) -> Self {
        Self {
            events: FilteredEvents { events }.peekable(),
            out,
            raw: Raw::None,
            text_only: false,
            list_tightness: Vec::new(),
            encountered_footnote: false,
            footnote_number: None,
            footnote_backlink_written: false,
        }
    }

    fn write(&mut self) -> std::fmt::Result {
        while let Some(e) = self.events.next() {
            match e {
                Event::Start(c, attrs) => {
                    if c.is_block() {
                        self.out.write_char('\n')?;
                    }
                    if self.text_only && !matches!(c, Container::Image(..)) {
                        continue;
                    }
                    match &c {
                        Container::Blockquote => self.out.write_str("<blockquote")?,
                        Container::List {
                            kind: ListKind::Unordered | ListKind::Task,
                            ..
                        } => {
                            self.out.write_str("<ul")?;
                        }
                        Container::List {
                            kind:
                                ListKind::Ordered {
                                    numbering, start, ..
                                },
                            ..
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
                        Container::ListItem | Container::TaskListItem { .. } => {
                            self.out.write_str("<li")?;
                        }
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
                            self.footnote_backlink_written = false;
                            continue;
                        }
                        Container::Table => self.out.write_str("<table")?,
                        Container::TableRow => self.out.write_str("<tr")?,
                        Container::Div { .. } => self.out.write_str("<div")?,
                        Container::Paragraph => {
                            if matches!(self.list_tightness.last(), Some(true)) {
                                continue;
                            }
                            self.out.write_str("<p")?;
                        }
                        Container::Heading { level } => write!(self.out, "<h{}", level)?,
                        Container::TableCell => self.out.write_str("<td")?,
                        Container::DescriptionTerm => self.out.write_str("<dt")?,
                        Container::CodeBlock { .. } => self.out.write_str("<pre")?,
                        Container::Span | Container::Math { .. } => self.out.write_str("<span")?,
                        Container::Link(dst, ..) => {
                            if dst.is_empty() {
                                self.out.write_str("<a")?;
                            } else {
                                write!(self.out, r#"<a href="{}""#, dst)?;
                            }
                        }
                        Container::Image(..) => {
                            self.text_only = true;
                            self.out.write_str("<img")?;
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
                        Container::SingleQuoted => self.out.write_str("&lsquo;")?,
                        Container::DoubleQuoted => self.out.write_str("&ldquo;")?,
                        _ => panic!(),
                    }

                    if matches!(c, Container::SingleQuoted | Container::DoubleQuoted) {
                        continue; // TODO add span to allow attributes?
                    }

                    for (a, v) in attrs.iter().filter(|(a, _)| *a != "class") {
                        write!(self.out, r#" {}="{}""#, a, v)?;
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
                            self.out.write_str(cls)?;
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
                        Container::CodeBlock { lang } => {
                            if let Some(l) = lang {
                                write!(self.out, r#"><code class="language-{}">"#, l)?;
                            } else {
                                self.out.write_str("><code>")?;
                            }
                        }
                        Container::Image(..) => {
                            self.out.write_str(r#" alt=""#)?;
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
                    if self.text_only && !matches!(c, Container::Image(..)) {
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
                        Container::DescriptionDetails => self.out.write_str("</dd>")?,
                        Container::Footnote { number, .. } => {
                            if !self.footnote_backlink_written {
                                write!(
                                    self.out,
                                    "\n<p><a href=\"#fnref{}\" role=\"doc-backlink\">↩︎︎</a></p>",
                                    number,
                                )?;
                            }
                            self.out.write_str("\n</li>")?;
                            self.footnote_number = None;
                        }
                        Container::Table => self.out.write_str("</table>")?,
                        Container::TableRow => self.out.write_str("</tr>")?,
                        Container::Div { .. } => self.out.write_str("</div>")?,
                        Container::Paragraph => {
                            if matches!(self.list_tightness.last(), Some(true)) {
                                continue;
                            }
                            if let Some(num) = self.footnote_number {
                                if matches!(
                                    self.events.peek(),
                                    Some(Event::End(Container::Footnote { .. }))
                                ) {
                                    write!(
                                        self.out,
                                        r##"<a href="#fnref{}" role="doc-backlink">↩︎︎</a>"##,
                                        num
                                    )?;
                                    self.footnote_backlink_written = true;
                                }
                            }
                            self.out.write_str("</p>")?;
                        }
                        Container::Heading { level } => write!(self.out, "</h{}>", level)?,
                        Container::TableCell => self.out.write_str("</td>")?,
                        Container::DescriptionTerm => self.out.write_str("</dt>")?,
                        Container::CodeBlock { .. } => self.out.write_str("</code></pre>")?,
                        Container::Span => self.out.write_str("</span>")?,
                        Container::Link(..) => self.out.write_str("</a>")?,
                        Container::Image(src, ..) => {
                            self.text_only = false;
                            if src.is_empty() {
                                self.out.write_str(r#"">"#)?;
                            } else {
                                write!(self.out, r#"" src="{}">"#, src)?;
                            }
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
                        Container::SingleQuoted => self.out.write_str("&rsquo;")?,
                        Container::DoubleQuoted => self.out.write_str("&rdquo;")?,
                        _ => panic!(),
                    }
                }
                Event::Str(s) => {
                    let mut s: &str = s.as_ref();
                    match self.raw {
                        Raw::None => {
                            let mut ent = "";
                            while let Some(i) = s.chars().position(|c| {
                                if let Some(s) = match c {
                                    '<' => Some("&lt;"),
                                    '>' => Some("&gt;"),
                                    '&' => Some("&amp;"),
                                    '"' => Some("&quot;"),
                                    _ => None,
                                } {
                                    ent = s;
                                    true
                                } else {
                                    false
                                }
                            }) {
                                self.out.write_str(&s[..i])?;
                                self.out.write_str(ent)?;
                                s = &s[i + 1..];
                            }
                            self.out.write_str(s)?;
                        }
                        Raw::Html => {
                            self.out.write_str(s)?;
                        }
                        Raw::Other => {}
                    }
                }

                Event::Atom(a) => match a {
                    Atom::FootnoteReference(_tag, number) => {
                        write!(
                            self.out,
                            r##"<a id="fnref{}" href="#fn{}" role="doc-noteref"><sup>{}</sup></a>"##,
                            number, number, number
                        )?;
                    }
                    Atom::Ellipsis => self.out.write_str("&hellip;")?,
                    Atom::EnDash => self.out.write_str("&ndash;")?,
                    Atom::EmDash => self.out.write_str("&mdash;")?,
                    Atom::ThematicBreak => self.out.write_str("\n<hr>")?,
                    Atom::NonBreakingSpace => self.out.write_str("&nbsp;")?,
                    Atom::Hardbreak => self.out.write_str("<br>\n")?,
                    Atom::Softbreak => self.out.write_char('\n')?,
                    Atom::Escape | Atom::Blankline => unreachable!("filtered out"),
                },
            }
        }
        if self.encountered_footnote {
            self.out.write_str("\n</ol>\n</section>")?;
        }
        self.out.write_char('\n')?;
        Ok(())
    }
}
