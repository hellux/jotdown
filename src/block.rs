use crate::Span;
use crate::EOF;

use crate::tree;

use Container::*;
use Leaf::*;

pub type Tree = tree::Tree<Block, Atom>;

#[must_use]
pub fn parse(src: &str) -> Tree {
    Parser::new(src).parse()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Block {
    /// A leaf block, containing only inline elements.
    Leaf(Leaf),

    /// A container block, containing children blocks.
    Container(Container),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leaf {
    /// Span is empty, before first character of paragraph.
    /// Each inline is a line.
    Paragraph,

    /// Span is `#` characters.
    /// Each inline is a line.
    Heading { level: u8 },

    /// Span is first `|` character.
    /// Each inline is a line (row).
    Table,

    /// Span is the link tag.
    /// Inlines are lines of the URL.
    LinkDefinition,

    /// Span is language specifier.
    /// Each inline is a line.
    CodeBlock { fence_length: u8, c: u8 },

    /// Span is from first to last character.
    /// No inlines.
    ThematicBreak,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Container {
    /// Span is first `>` character.
    Blockquote,

    /// Span is class specifier.
    Div { fence_length: u8 },

    /// Span is the list marker.
    ListItem { indent: u8 },

    /// Span is first `[^` instance.
    Footnote { indent: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    /// Inline content with unparsed inline elements.
    Inline,

    /// A line with no non-whitespace characters.
    Blankline,

    /// A list of attributes.
    Attributes,
}

struct Parser<'s> {
    src: &'s str,
    tree: tree::Builder<Block, Atom>,
}

impl<'s> Parser<'s> {
    #[must_use]
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            tree: tree::Builder::new(),
        }
    }

    #[must_use]
    pub fn parse(mut self) -> Tree {
        let mut lines = lines(self.src).collect::<Vec<_>>();
        let mut line_pos = 0;
        while line_pos < lines.len() {
            let line_count = self.parse_block(&mut lines[line_pos..]);
            if line_count == 0 {
                break;
            }
            line_pos += line_count;
        }
        self.tree.finish()
    }

    /// Recursively parse a block and all of its children. Return number of lines the block uses.
    fn parse_block(&mut self, lines: &mut [Span]) -> usize {
        let blanklines = lines
            .iter()
            .take_while(|sp| sp.of(self.src).trim().is_empty())
            .map(|sp| self.tree.elem(Atom::Blankline, *sp))
            .count();
        let lines = &mut lines[blanklines..];

        Block::parse(lines.iter().map(|sp| sp.of(self.src))).map_or(
            blanklines,
            |(kind, span, line_count)| {
                let lines = {
                    let l = lines.len().min(line_count);
                    &mut lines[..l]
                };
                let truncated = lines.len() < line_count;
                let span = span.translate(lines[0].start());

                // skip part of first inline that is shared with the block span
                lines[0] = lines[0].with_start(span.end());

                // remove junk from footnotes / link defs
                if matches!(
                    kind,
                    Block::Leaf(LinkDefinition) | Block::Container(Footnote { .. })
                ) {
                    assert_eq!(&lines[0].of(self.src).chars().as_str()[0..2], "]:");
                    lines[0] = lines[0].skip(2);
                }

                // skip closing fence of code blocks / divs
                let lines = if !truncated
                    && matches!(
                        kind,
                        Block::Leaf(CodeBlock { .. }) | Block::Container(Div { .. })
                    ) {
                    let l = lines.len();
                    &mut lines[..l - 1]
                } else {
                    lines
                };

                match &kind {
                    Block::Leaf(l) => {
                        self.tree.enter(kind, span);

                        // trim starting whitespace of the block contents
                        lines[0] = lines[0].trim_start(self.src);

                        // skip first inline if empty (e.g. code block)
                        let lines = if lines[0].is_empty() {
                            &mut lines[1..]
                        } else {
                            lines
                        };

                        // trim ending whitespace of block if not verbatim
                        if !matches!(l, Leaf::CodeBlock { .. }) {
                            let last = &mut lines[line_count - 1];
                            *last = last.trim_end(self.src);
                        }

                        lines
                            .iter()
                            .for_each(|line| self.tree.elem(Atom::Inline, *line));
                    }
                    Block::Container(c) => {
                        let (skip_chars, skip_lines_suffix) = match &c {
                            Blockquote => (2, 0),
                            ListItem { indent } | Footnote { indent } => (*indent, 0),
                            Div { .. } => (0, 1),
                        };
                        let line_count_inner = lines.len() - skip_lines_suffix;

                        // update spans, remove indentation / container prefix
                        lines
                            .iter_mut()
                            .skip(1)
                            .take(line_count_inner)
                            .for_each(|sp| {
                                let skip = (sp
                                    .of(self.src)
                                    .chars()
                                    .take_while(|c| c.is_whitespace())
                                    .count()
                                    + usize::from(skip_chars))
                                .min(sp.len());
                                *sp = sp.skip(skip);
                            });

                        self.tree.enter(kind, span);
                        let mut l = 0;
                        while l < line_count_inner {
                            l += self.parse_block(&mut lines[l..line_count_inner]);
                        }
                    }
                }
                self.tree.exit();
                blanklines + line_count
            },
        )
    }
}

impl Block {
    /// Parse a single block. Return number of lines the block uses.
    fn parse<'b, I: Iterator<Item = &'b str>>(mut lines: I) -> Option<(Block, Span, usize)> {
        lines.next().map(|l| {
            let (kind, sp) = Block::start(l);
            let has_end_delimiter = matches!(
                kind,
                Self::Leaf(CodeBlock { .. }) | Self::Container(Div { .. })
            );
            let line_count_match = lines.take_while(|l| kind.continues(l)).count();
            let line_count = 1 + line_count_match + usize::from(has_end_delimiter);
            (kind, sp, line_count)
        })
    }

    /// Determine what type of block a line can start.
    fn start(line: &str) -> (Self, Span) {
        let start = line.chars().take_while(|c| c.is_whitespace()).count();
        let line_t = &line[start..];
        let mut chars = line_t.chars();

        match chars.next().unwrap_or(EOF) {
            '#' => chars
                .find(|c| *c != '#')
                .map_or(true, char::is_whitespace)
                .then(|| {
                    u8::try_from(line_t.len() - chars.as_str().len() - 1)
                        .ok()
                        .map(|level| {
                            (
                                Self::Leaf(Heading { level }),
                                Span::by_len(start, level.into()),
                            )
                        })
                })
                .flatten(),
            '>' => {
                if let Some(c) = chars.next() {
                    c.is_whitespace().then(|| {
                        (
                            Self::Container(Blockquote),
                            Span::by_len(start, line_t.len() - chars.as_str().len() - 1),
                        )
                    })
                } else {
                    Some((
                        Self::Container(Blockquote),
                        Span::by_len(start, line_t.len() - chars.as_str().len()),
                    ))
                }
            }
            '|' => (&line_t[line_t.len() - 1..] == "|"
                && &line_t[line_t.len() - 2..line_t.len() - 1] != "\\")
                .then(|| (Self::Leaf(Table), Span::by_len(start, 1))),
            '[' => chars.as_str().find("]:").map(|l| {
                let tag = &chars.as_str()[0..l];
                let (tag, is_footnote) = if let Some(tag) = tag.strip_prefix('^') {
                    (tag, true)
                } else {
                    (tag, false)
                };
                dbg!(line, line_t, tag);
                (
                    if is_footnote {
                        Self::Container(Footnote {
                            indent: u8::try_from(start).unwrap(),
                        })
                    } else {
                        Self::Leaf(LinkDefinition)
                    },
                    Span::from_slice(line, tag),
                )
            }),
            '-' | '*' if Self::is_thematic_break(chars.clone()) => Some((
                Self::Leaf(ThematicBreak),
                Span::from_slice(line, line_t.trim()),
            )),
            '-' => chars.next().map_or(true, char::is_whitespace).then(|| {
                let task_list = chars.next() == Some('[')
                    && matches!(chars.next(), Some('X' | ' '))
                    && chars.next() == Some(']')
                    && chars.next().map_or(true, char::is_whitespace);
                (
                    Self::Container(ListItem {
                        indent: u8::try_from(start).unwrap(),
                    }),
                    Span::by_len(start, if task_list { 3 } else { 1 }),
                )
            }),
            '+' | '*' | ':' if chars.next().map_or(true, char::is_whitespace) => Some((
                Self::Container(ListItem {
                    indent: u8::try_from(start).unwrap(),
                }),
                Span::by_len(start, 1),
            )),
            f @ ('`' | ':' | '~') => {
                let fence_length = (&mut chars).take_while(|c| *c == f).count() + 1;
                let lang = line_t[fence_length..].trim();
                let valid_spec =
                    !lang.chars().any(char::is_whitespace) && !lang.chars().any(|c| c == '`');
                (valid_spec && fence_length >= 3)
                    .then(|| {
                        u8::try_from(fence_length).ok().map(|fence_length| {
                            (
                                match f {
                                    ':' => Self::Container(Div { fence_length }),
                                    _ => Self::Leaf(CodeBlock {
                                        fence_length,
                                        c: f as u8,
                                    }),
                                },
                                Span::from_slice(line, lang),
                            )
                        })
                    })
                    .flatten()
            }
            _ => None,
        }
        .unwrap_or((Self::Leaf(Paragraph), Span::new(0, 0)))
    }

    fn is_thematic_break(chars: std::str::Chars) -> bool {
        let mut n = 1;
        for c in chars {
            if matches!(c, '-' | '*') {
                n += 1;
            } else if !c.is_whitespace() {
                return false;
            }
        }
        n >= 3
    }

    /// Determine if this line continues a block of a certain type.
    fn continues(self, line: &str) -> bool {
        //let start = Self::start(line); // TODO allow starting new block without blank line
        match self {
            Self::Leaf(Paragraph | Heading { .. } | Table) => !line.trim().is_empty(),
            Self::Leaf(LinkDefinition) => line.starts_with(' ') && !line.trim().is_empty(),
            Self::Leaf(ThematicBreak) => false,
            Self::Container(Blockquote) => line.trim().starts_with('>'),
            Self::Container(Footnote { indent } | ListItem { indent }) => {
                let spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                !line.trim().is_empty() && spaces >= (indent).into()
            }
            Self::Container(Div { fence_length }) | Self::Leaf(CodeBlock { fence_length, .. }) => {
                let fence = match self {
                    Self::Container(..) => ':',
                    Self::Leaf(CodeBlock { c, .. }) => c as char,
                    Self::Leaf(..) => unreachable!(),
                };
                let mut c = line.chars();
                !((&mut c).take((fence_length).into()).all(|c| c == fence)
                    && c.next().map_or(true, char::is_whitespace))
            }
        }
    }
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Block::Leaf(e) => std::fmt::Debug::fmt(e, f),
            Block::Container(c) => std::fmt::Debug::fmt(c, f),
        }
    }
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Inline")
    }
}

/// Similar to `std::str::split('\n')` but newline is included and spans are used instead of `str`.
fn lines(src: &str) -> impl Iterator<Item = Span> + '_ {
    let mut chars = src.chars();
    std::iter::from_fn(move || {
        if chars.as_str().is_empty() {
            None
        } else {
            let start = src.len() - chars.as_str().len();
            chars.find(|c| *c == '\n');
            let end = src.len() - chars.as_str().len();
            if start == end {
                None
            } else {
                Some(Span::new(start, end))
            }
        }
    })
}

#[cfg(test)]
mod test {
    use crate::tree::EventKind::*;

    use super::Atom::*;
    use super::Block;
    use super::Block::*;
    use super::Container::*;
    use super::Leaf::*;

    macro_rules! test_parse {
            ($src:expr $(,$($event:expr),* $(,)?)?) => {
                let t = super::Parser::new($src).parse();
                let actual = t.map(|ev| (ev.kind, ev.span.of($src))).collect::<Vec<_>>();
                let expected = &[$($($event),*,)?];
                assert_eq!(actual, expected, "\n\n{}\n\n", $src);
            };
        }

    #[test]
    fn parse_para_oneline() {
        test_parse!(
            "para\n",
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_para_multiline() {
        test_parse!(
            "para0\npara1\n",
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "para0\n"),
            (Element(Inline), "para1"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_heading_multi() {
        test_parse!(
            concat!(
                    "# 2\n",
                    "\n",
                    " #   8\n",
                    "  12\n",
                    "15\n", //
                ),
            (Enter(Leaf(Heading { level: 1 })), "#"),
            (Element(Inline), "2"),
            (Exit(Leaf(Heading { level: 1 })), "#"),
            (Element(Blankline), "\n"),
            (Enter(Leaf(Heading { level: 1 })), "#"),
            (Element(Inline), "8\n"),
            (Element(Inline), "  12\n"),
            (Element(Inline), "15"),
            (Exit(Leaf(Heading { level: 1 })), "#"),
        );
    }

    #[test]
    fn parse_blockquote() {
        test_parse!(
            "> a\n",
            (Enter(Container(Blockquote)), ">"),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Blockquote)), ">"),
        );
        test_parse!(
            "> \n",
            (Enter(Container(Blockquote)), ">"),
            (Element(Blankline), " \n"),
            (Exit(Container(Blockquote)), ">"),
        );
        test_parse!(
            ">",
            (Enter(Container(Blockquote)), ">"),
            (Element(Blankline), ""),
            (Exit(Container(Blockquote)), ">"),
        );
        test_parse!(
            concat!(
                "> a\n",
                ">\n",
                "> ## hl\n",
                ">\n",
                ">  para\n", //
            ),
            (Enter(Container(Blockquote)), ">"),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Element(Blankline), ""),
            (Enter(Leaf(Heading { level: 2 })), "##"),
            (Element(Inline), "hl"),
            (Exit(Leaf(Heading { level: 2 })), "##"),
            (Element(Blankline), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "para"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Blockquote)), ">"),
        );
    }

    #[test]
    fn parse_blockquote_empty() {
        test_parse!(
            "> \n",
            (Enter(Container(Blockquote)), ">"),
            (Element(Blankline), "\n"),
            (Exit(Container(Blockquote)), ">"),
        );
        test_parse!(
            ">",
            (Enter(Container(Blockquote)), ">"),
            (Element(Blankline), ""),
            (Exit(Container(Blockquote)), ">"),
        );
    }

    #[test]
    fn parse_code_block() {
        test_parse!(
            concat!("```\n", "l0\n"),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                "",
            ),
            (Element(Inline), "l0\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                "",
            ),
        );
        test_parse!(
            concat!(
                "```\n",
                "l0\n",
                "```\n",
                "\n",
                "para\n", //
            ),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
            (Element(Inline), "l0\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
            (Element(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
        test_parse!(
            concat!(
                "````  lang\n",
                "l0\n",
                "```\n",
                " l1\n",
                "````", //
            ),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 4,
                    c: b'`'
                })),
                "lang"
            ),
            (Element(Inline), "l0\n"),
            (Element(Inline), "```\n"),
            (Element(Inline), " l1\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 4,
                    c: b'`'
                })),
                "lang"
            ),
        );
        test_parse!(
            concat!(
                "```\n", //
                "a\n",   //
                "```\n", //
                "```\n", //
                "bbb\n", //
                "```\n", //
            ),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
            (Element(Inline), "a\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
            (Element(Inline), "bbb\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'`'
                })),
                ""
            ),
        );
        test_parse!(
            concat!(
                "~~~\n",
                "code\n",
                "  block\n",
                "~~~\n", //
            ),
            (
                Enter(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'~'
                })),
                "",
            ),
            (Element(Inline), "code\n"),
            (Element(Inline), "  block\n"),
            (
                Exit(Leaf(CodeBlock {
                    fence_length: 3,
                    c: b'~'
                })),
                "",
            ),
        );
    }

    #[test]
    fn parse_link_definition() {
        test_parse!(
            "[tag]: url\n",
            (Enter(Leaf(LinkDefinition)), "tag"),
            (Element(Inline), "url"),
            (Exit(Leaf(LinkDefinition)), "tag"),
        );
    }

    #[test]
    fn parse_footnote() {
        test_parse!(
            "[^tag]: description\n",
            (Enter(Container(Footnote { indent: 0 })), "tag"),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "description"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Footnote { indent: 0 })), "tag"),
        );
    }

    macro_rules! test_block {
        ($src:expr, $kind:expr, $str:expr, $len:expr $(,)?) => {
            let lines = super::lines($src).map(|sp| sp.of($src));
            let (kind, sp, len) = Block::parse(lines).unwrap();
            assert_eq!(
                (kind, sp.of($src), len),
                ($kind, $str, $len),
                "\n\n{}\n\n",
                $src
            );
        };
    }

    #[test]
    fn block_multiline() {
        test_block!(
            "# heading\n spanning two lines\n",
            Leaf(Heading { level: 1 }),
            "#",
            2
        );
    }

    #[test]
    fn block_blockquote() {
        test_block!(
            concat!(
                "> a\n",    //
                ">\n",      //
                "  >  b\n", //
                ">\n",      //
                "> c\n",    //
            ),
            Block::Container(Blockquote),
            ">",
            5,
        );
    }

    #[test]
    fn block_code_block() {
        test_block!(
            concat!(
                "````  lang\n",
                "l0\n",
                "```\n",
                " l1\n",
                "````", //
            ),
            Leaf(CodeBlock {
                fence_length: 4,
                c: b'`'
            }),
            "lang",
            5,
        );
        test_block!(
            concat!(
                "```\n", //
                "a\n",   //
                "```\n", //
                "```\n", //
                "bbb\n", //
                "```\n", //
            ),
            Leaf(CodeBlock {
                fence_length: 3,
                c: b'`'
            }),
            "",
            3,
        );
        test_block!(
            concat!(
                "``` no space in lang specifier\n",
                "l0\n",
                "```\n", //
            ),
            Leaf(Paragraph),
            "",
            3,
        );
    }

    #[test]
    fn block_link_definition() {
        test_block!("[tag]: url\n", Leaf(LinkDefinition), "tag", 1);
        test_block!(
            concat!(
                "[tag]: uuu\n",
                " rl\n", //
            ),
            Leaf(LinkDefinition),
            "tag",
            2,
        );
        test_block!(
            concat!(
                "[tag]: url\n",
                "para\n", //
            ),
            Leaf(LinkDefinition),
            "tag",
            1,
        );
    }
}
