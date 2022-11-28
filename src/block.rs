use crate::Span;
use crate::EOF;

use crate::tree;

use Container::*;
use Leaf::*;

pub type Tree = tree::Tree<Block, Atom>;

pub fn parse(src: &str) -> Tree {
    Parser::new(src).parse()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Block {
    Leaf(Leaf),
    Container(Container),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leaf {
    Paragraph,
    Heading { level: u8 },
    Attributes,
    Table,
    LinkDefinition,
    CodeBlock { fence_length: u8 },
    ThematicBreak,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Container {
    Blockquote,
    Div { fence_length: u8 },
    ListItem { indent: u8 },
    Footnote { indent: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    /// Inline content with unparsed inline elements.
    Inline,
    /// A line with no non-whitespace characters.
    Blankline,
    ///// Thematic break.
    //ThematicBreak,
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
            .map(|sp| {
                self.tree.elem(Atom::Blankline, *sp);
            })
            .count();
        let lines = &mut lines[blanklines..];
        Block::parse(lines.iter().map(|sp| sp.of(self.src))).map_or(
            blanklines,
            |(kind, span, len)| {
                let start = lines.get(0).map(|sp| sp.start()).unwrap();
                let span = span.translate(start);
                match &kind {
                    Block::Leaf(l) => {
                        self.tree.enter(kind, span);
                        lines[0] = lines[0].with_start(span.end());
                        let len = match l {
                            CodeBlock { .. } => len - 2,
                            _ => len,
                        };
                        for line in &lines[0..len] {
                            self.tree.elem(Atom::Inline, *line);
                        }
                    }
                    Block::Container(c) => {
                        let (skip_chars, skip_lines_suffix) = match &c {
                            Blockquote => (2, 0),
                            ListItem { indent } | Footnote { indent } => (*indent, 0),
                            Div { .. } => (0, 1),
                        };
                        let line_count_inner = lines.len() - skip_lines_suffix;

                        // update spans, remove indentation / container prefix
                        lines[0] = lines[0].with_start(span.end());
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
                                *sp = sp.trim_start(skip);
                            });

                        self.tree.enter(kind, span);
                        let mut l = 0;
                        while l < line_count_inner {
                            l += self.parse_block(&mut lines[l..line_count_inner]);
                        }
                    }
                }
                self.tree.exit();
                blanklines + len
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
            let line_count = 1
                + lines.take_while(|l| kind.continues(l)).count()
                + usize::from(has_end_delimiter);
            (kind, sp, line_count)
        })
    }

    /// Determine what type of block a line can start.
    fn start(line: &str) -> (Self, Span) {
        let start = line.chars().take_while(|c| c.is_whitespace()).count();
        let line = &line[start..];
        let mut chars = line.chars();
        match chars.next().unwrap_or(EOF) {
            '#' => chars
                .find(|c| *c != '#')
                .map_or(true, char::is_whitespace)
                .then(|| {
                    u8::try_from(line.len() - chars.as_str().len() - 1)
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
                            Span::by_len(start, line.len() - chars.as_str().len() - 1),
                        )
                    })
                } else {
                    Some((
                        Self::Container(Blockquote),
                        Span::by_len(start, line.len() - chars.as_str().len()),
                    ))
                }
            }
            f @ ('`' | ':') => {
                let fence_length = chars.take_while(|c| *c == f).count() + 1;
                (fence_length >= 3)
                    .then(|| {
                        u8::try_from(fence_length).ok().map(|fence_length| {
                            (
                                match f {
                                    '`' => Self::Leaf(CodeBlock { fence_length }),
                                    ':' => Self::Container(Div { fence_length }),
                                    _ => unreachable!(),
                                },
                                Span::by_len(start, fence_length.into()),
                            )
                        })
                    })
                    .flatten()
            }
            _ => {
                let thematic_break = || {
                    let mut without_whitespace = line.chars().filter(|c| !c.is_whitespace());
                    let length = without_whitespace.clone().count();
                    (length >= 3
                        && (without_whitespace.clone().all(|c| c == '-')
                            || without_whitespace.all(|c| c == '*')))
                    .then(|| (Self::Leaf(ThematicBreak), Span::by_len(start, line.len())))
                };

                thematic_break()
            }
        }
        .unwrap_or((Self::Leaf(Paragraph), Span::new(0, 0)))
    }

    /// Determine if this line continues a block of a certain type.
    fn continues(self, line: &str) -> bool {
        //let start = Self::start(line); // TODO allow starting new block without blank line
        match self {
            Self::Leaf(Paragraph | Heading { .. } | Table | LinkDefinition) => {
                !line.trim().is_empty()
            }
            Self::Leaf(Attributes | ThematicBreak) => false,
            Self::Container(Blockquote) => line.trim().starts_with('>'),
            Self::Container(Footnote { indent } | ListItem { indent }) => {
                let spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                !line.trim().is_empty() && spaces >= (indent).into()
            }
            Self::Container(Div { fence_length }) | Self::Leaf(CodeBlock { fence_length }) => {
                let mut c = line.chars();
                !((&mut c).take((fence_length).into()).all(|c| c == ':')
                    && c.next().map_or(false, char::is_whitespace))
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
    use crate::Span;

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
            (Element(Inline), "para\n"),
            (Exit, ""),
        );
    }

    #[test]
    fn parse_para_multiline() {
        test_parse!(
            "para0\npara1\n",
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "para0\n"),
            (Element(Inline), "para1\n"),
            (Exit, ""),
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
            (Element(Inline), " 2\n"),
            (Exit, "#"),
            (Element(Blankline), "\n"),
            (Enter(Leaf(Heading { level: 1 })), "#"),
            (Element(Inline), "   8\n"),
            (Element(Inline), "  12\n"),
            (Element(Inline), "15\n"),
            (Exit, "#"),
        );
    }

    #[test]
    fn parse_blockquote() {
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
            (Element(Inline), " a\n"),
            (Exit, ""),
            (Element(Blankline), "\n"),
            (Enter(Leaf(Heading { level: 2 })), "##"),
            (Element(Inline), " hl\n"),
            (Exit, "##"),
            (Element(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Element(Inline), "  para\n"),
            (Exit, ""),
            (Exit, ">"),
        );
    }

    #[test]
    fn parse_code_block() {
        test_parse!(
            concat!(
                "```\n",
                "l0\n",
                "```", //
            ),
            (Enter(Leaf(CodeBlock { fence_length: 3 })), "```"),
            (Element(Inline), "\n"),
            (Element(Inline), "l0\n"),
            (Exit, "```"),
        );
        test_parse!(
            concat!(
                "````lang\n",
                "l0\n",
                "```\n",
                " l1\n",
                "````", //
            ),
            (Enter(Leaf(CodeBlock { fence_length: 4 })), "````"),
            (Element(Inline), "lang\n"),
            (Element(Inline), "l0\n"),
            (Element(Inline), "```\n"),
            (Element(Inline), " l1\n"),
            (Exit, "````"),
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
            Block::Leaf(Heading { level: 1 }),
            "#",
            2
        );
    }

    #[test]
    fn block_container() {
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
}
