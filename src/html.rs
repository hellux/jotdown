use crate::Atom;
use crate::Container;
use crate::Event;

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

struct Writer<I, W> {
    events: I,
    out: W,
    raw: Raw,
}

impl<'s, I: Iterator<Item = Event<'s>>, W: std::fmt::Write> Writer<I, W> {
    fn new(events: I, out: W) -> Self {
        Self {
            events,
            out,
            raw: Raw::None,
        }
    }

    fn write(&mut self) -> std::fmt::Result {
        for e in &mut self.events {
            match e {
                Event::Start(c, _attrs) => {
                    if c.is_block() {
                        self.out.write_char('\n')?;
                    }
                    match c {
                        Container::Blockquote => self.out.write_str("<blockquote>")?,
                        Container::List(..) => todo!(),
                        Container::ListItem => self.out.write_str("<li>")?,
                        Container::DescriptionList => self.out.write_str("<dl>")?,
                        Container::DescriptionDetails => self.out.write_str("<dd>")?,
                        Container::Footnote { .. } => todo!(),
                        Container::Table => self.out.write_str("<table>")?,
                        Container::TableRow => self.out.write_str("<tr>")?,
                        Container::Div { class } => {
                            if let Some(c) = class {
                                write!(self.out, r#"<div class="{}">"#, c)?;
                            } else {
                                self.out.write_str("<div>")?;
                            }
                        }
                        Container::Paragraph => self.out.write_str("<p>")?,
                        Container::Heading { level } => write!(self.out, "<h{}>", level)?,
                        Container::TableCell => self.out.write_str("<td>")?,
                        Container::DescriptionTerm => self.out.write_str("<dt>")?,
                        Container::CodeBlock { lang } => {
                            if let Some(l) = lang {
                                write!(self.out, r#"<pre><code class="language-{}">"#, l)?;
                            } else {
                                self.out.write_str("<pre><code>")?;
                            }
                        }
                        Container::Span => self.out.write_str("<span>")?,
                        Container::Link(..) => todo!(),
                        Container::Image(..) => todo!(),
                        Container::Verbatim => self.out.write_str("<code>")?,
                        Container::Math { display } => self.out.write_str(if display {
                            r#"<span class="math display">\["#
                        } else {
                            r#"<span class="math inline">\("#
                        })?,
                        Container::RawBlock { format } | Container::RawInline { format } => {
                            self.raw = if format == "html" {
                                Raw::Html
                            } else {
                                Raw::Other
                            }
                        }
                        Container::Subscript => self.out.write_str("<sub>")?,
                        Container::Superscript => self.out.write_str("<sup>")?,
                        Container::Insert => self.out.write_str("<ins>")?,
                        Container::Delete => self.out.write_str("<del>")?,
                        Container::Strong => self.out.write_str("<strong>")?,
                        Container::Emphasis => self.out.write_str("<em>")?,
                        Container::Mark => self.out.write_str("<mark>")?,
                        Container::SingleQuoted => self.out.write_str("&lsquo;")?,
                        Container::DoubleQuoted => self.out.write_str("&ldquo;")?,
                    }
                }
                Event::End(c) => {
                    if c.is_block_container() && !matches!(c, Container::Footnote { .. }) {
                        self.out.write_char('\n')?;
                    }
                    match c {
                        Container::Blockquote => self.out.write_str("</blockquote>")?,
                        Container::List(..) => todo!(),
                        Container::ListItem => self.out.write_str("</li>")?,
                        Container::DescriptionList => self.out.write_str("</dl>")?,
                        Container::DescriptionDetails => self.out.write_str("</dd>")?,
                        Container::Footnote { .. } => todo!(),
                        Container::Table => self.out.write_str("</table>")?,
                        Container::TableRow => self.out.write_str("</tr>")?,
                        Container::Div { .. } => self.out.write_str("</div>")?,
                        Container::Paragraph => self.out.write_str("</p>")?,
                        Container::Heading { level } => write!(self.out, "</h{}>", level)?,
                        Container::TableCell => self.out.write_str("</td>")?,
                        Container::DescriptionTerm => self.out.write_str("</dt>")?,
                        Container::CodeBlock { .. } => self.out.write_str("</code></pre>")?,
                        Container::Span => self.out.write_str("</span>")?,
                        Container::Link(..) => todo!(),
                        Container::Image(..) => todo!(),
                        Container::Verbatim => self.out.write_str("</code>")?,
                        Container::Math { .. } => self.out.write_str("</span>")?,
                        Container::RawBlock { .. } | Container::RawInline { .. } => {
                            self.raw = Raw::None
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
                    Atom::Ellipsis => self.out.write_str("&hellip;")?,
                    Atom::EnDash => self.out.write_str("&ndash;")?,
                    Atom::EmDash => self.out.write_str("&mdash;")?,
                    Atom::ThematicBreak => self.out.write_str("\n<hr>")?,
                    Atom::NonBreakingSpace => self.out.write_str("&nbsp;")?,
                    Atom::Hardbreak => self.out.write_str("<br>\n")?,
                    Atom::Softbreak => self.out.write_char('\n')?,
                    Atom::Blankline | Atom::Escape => {}
                },
            }
        }
        Ok(())
    }
}
