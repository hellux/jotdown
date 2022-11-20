use crate::Span;
use crate::EOF;

use crate::tree;

use Container::*;
use Leaf::*;

pub type Tree = tree::Tree<Block, Atom>;
pub type TreeIter<'t> = tree::Iter<'t, Block, Atom>;

pub fn parse(src: &str) -> Tree {
    Parser::new(src).parse()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
    Leaf(Leaf),
    Container(Container),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Leaf {
    Paragraph,
    Heading {
        level: usize,
    },
    Attributes,
    Table,
    ThematicBreak,
    LinkDefinition,
    CodeBlock {
        fence_char: char,
        fence_length: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Container {
    Blockquote,
    Div { fence_length: usize },
    ListItem { indent: usize },
    Footnote { indent: usize },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Atom {
    /// Inline content with unparsed inline elements.
    Inline,
    /// A line with no non-whitespace characters.
    Blankline,
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
        loop {
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
        Block::parse(lines.iter().map(|sp| (sp.of(self.src), sp.start()))).map_or(
            0,
            |(kind, span, len)| {
                match &kind {
                    Block::Leaf(_) => {
                        self.tree.enter(kind, span);
                        lines[0] = lines[0].with_start(span.end());
                        for line in lines.iter().take(len) {
                            self.tree.elem(Atom::Inline, *line);
                        }
                    }
                    Block::Container(c) => {
                        let (skip_chars, skip_lines_suffix) = match &c {
                            Blockquote => (1, 0),
                            ListItem { indent } | Footnote { indent } => (*indent, 0),
                            Div { .. } => (0, 1),
                        };
                        let line_count = lines.len() - skip_lines_suffix;

                        // update spans, remove indentation / container prefix
                        lines[0] = lines[0].with_start(span.end());
                        lines.iter_mut().skip(1).take(line_count).for_each(|sp| {
                            let skip = (sp
                                .of(self.src)
                                .chars()
                                .take_while(|c| c.is_whitespace())
                                .count()
                                + skip_chars)
                                .min(sp.len());
                            *sp = sp.trim_start(skip);
                        });

                        self.tree.enter(kind, span);
                        let mut l = 0;
                        while l < line_count {
                            l += self.parse_block(&mut lines[l..line_count]);
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
    fn parse<'b, I: Iterator<Item = (&'b str, usize)>>(
        mut lines: I,
    ) -> Option<(Block, Span, usize)> {
        if let Some((l, start)) = lines.next() {
            let (kind, sp) = Block::start(l);
            let line_count = 1 + lines.take_while(|(l, _)| kind.continues(l)).count();
            Some((kind, sp.translate(start), line_count))
        } else {
            None
        }
    }

    /// Determine what type of block a line can start.
    fn start(line: &str) -> (Block, Span) {
        let start = line.chars().take_while(|c| c.is_whitespace()).count();
        let line = &line[start..];
        let mut chars = line.chars();
        match chars.next().unwrap_or(EOF) {
            '#' => chars
                .find(|c| *c != '#')
                .map_or(true, char::is_whitespace)
                .then(|| {
                    let span = Span::by_len(start, line.len() - chars.as_str().len() - 1);
                    (Self::Leaf(Heading { level: span.len() }), span)
                }),
            '>' => chars.next().map_or(true, |c| c == ' ').then(|| {
                (
                    Self::Container(Blockquote),
                    Span::by_len(start, line.len() - chars.as_str().len() - 1),
                )
            }),
            f @ ':' => {
                let fence_length = chars.take_while(|c| *c == f).count() + 1;
                (fence_length >= 3).then(|| {
                    (
                        Self::Container(Div { fence_length }),
                        Span::by_len(start, line.len()),
                    )
                })
            }
            fence_char @ ('`' | '~') => {
                let fence_length = chars.take_while(|c| *c == fence_char).count() + 1;
                (fence_length >= 3).then(|| {
                    (
                        Self::Leaf(CodeBlock {
                            fence_char,
                            fence_length,
                        }),
                        Span::by_len(start, line.len()),
                    )
                })
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
    fn continues(&self, line: &str) -> bool {
        match self {
            Self::Leaf(Paragraph | Heading { .. } | Table | LinkDefinition) => {
                !line.trim().is_empty()
            }
            Self::Leaf(Attributes | ThematicBreak) => false,
            Self::Leaf(CodeBlock {
                fence_char,
                fence_length,
            }) => !line.chars().take(*fence_length).all(|c| c == *fence_char),
            Self::Container(Blockquote) => line.trim().starts_with('>'),
            Self::Container(Footnote { indent } | ListItem { indent }) => {
                let spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                !line.trim().is_empty() && spaces >= *indent
            }
            Self::Container(Div { fence_length }) => {
                line.chars().take(*fence_length).all(|c| c == ':')
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
    use crate::tree::Event;
    use crate::Span;

    use super::Atom::*;
    use super::Block;
    use super::Block::*;
    use super::Container::*;
    use super::Leaf::*;

    #[test]
    fn parse_elem_oneline() {
        let src = "para\n";

        assert_eq!(
            super::Parser::new(src).parse().iter().collect::<Vec<_>>(),
            &[
                Event::Enter(&Leaf(Paragraph), Span::new(0, 0)),
                Event::Element(&Inline, Span::new(0, 5)),
                Event::Exit,
            ],
        );
    }

    #[test]
    fn parse_elem_multiline() {
        let src = "para\npara\n";

        assert_eq!(
            super::Parser::new(src).parse().iter().collect::<Vec<_>>(),
            &[
                Event::Enter(&Leaf(Paragraph), Span::new(0, 0)),
                Event::Element(&Inline, Span::new(0, 5)),
                Event::Element(&Inline, Span::new(5, 10)),
                Event::Exit,
            ],
        );
    }

    #[test]
    fn parse_elem_multi() {
        let src = concat!(
            "# 2\n",
            "\n",
            " # 8\n",
            "  12\n",
            "15\n", //
        );

        assert_eq!(
            super::Parser::new(src).parse().iter().collect::<Vec<_>>(),
            &[
                Event::Enter(&Leaf(Heading { level: 1 }), Span::new(0, 1)),
                Event::Element(&Inline, Span::new(1, 4)),
                Event::Exit,
                Event::Element(&Blankline, Span::new(4, 5)),
                Event::Enter(&Leaf(Heading { level: 1 }), Span::new(6, 7)),
                Event::Element(&Inline, Span::new(7, 10)),
                Event::Element(&Inline, Span::new(10, 15)),
                Event::Element(&Inline, Span::new(15, 18)),
                Event::Exit,
            ],
        );
    }

    #[test]
    fn parse_container() {
        let src = concat!(
            "> a\n",
            ">\n",
            "> ## hl\n",
            ">\n",
            "> para\n", //
        );

        assert_eq!(
            super::Parser::new(src).parse().iter().collect::<Vec<_>>(),
            &[
                Event::Enter(&Container(Blockquote), Span::new(0, 1)),
                Event::Enter(&Leaf(Paragraph), Span::new(1, 1)),
                Event::Element(&Inline, Span::new(1, 4)),
                Event::Exit,
                Event::Element(&Blankline, Span::new(5, 6)),
                Event::Enter(&Leaf(Heading { level: 2 }), Span::new(8, 10)),
                Event::Element(&Inline, Span::new(10, 14)),
                Event::Exit,
                Event::Element(&Blankline, Span::new(15, 16)),
                Event::Enter(&Leaf(Paragraph), Span::new(17, 17)),
                Event::Element(&Inline, Span::new(17, 23)),
                Event::Exit,
                Event::Exit,
            ]
        );
    }

    #[test]
    fn block_multiline() {
        let src = "# heading\n spanning two lines\n";
        let lines = super::lines(src).map(|sp| (sp.of(src), sp.start()));
        let (kind, sp, len) = Block::parse(lines).unwrap();
        assert_eq!(kind, Block::Leaf(Heading { level: 1 }));
        assert_eq!(sp.of(src), "#");
        assert_eq!(len, 2);
    }

    #[test]
    fn block_container() {
        let src = concat!(
        "> a\n",
        ">\n",
        "  >  b\n",
        ">\n",
        "> c\n", //
    );
        let lines = super::lines(src).map(|sp| (sp.of(src), sp.start()));
        let (kind, sp, len) = Block::parse(lines).unwrap();
        assert_eq!(kind, Block::Container(Blockquote));
        assert_eq!(sp.of(src), ">");
        assert_eq!(len, 5);
    }
}
