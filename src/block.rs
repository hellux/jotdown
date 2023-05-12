use crate::Alignment;
use crate::OrderedListNumbering::*;
use crate::OrderedListStyle::*;
use crate::Span;

use crate::attr;
use crate::lex;

use Atom::*;
use Container::*;
use Leaf::*;
use ListType::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Event<'s> {
    pub kind: EventKind<'s>,
    pub span: Span,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum EventKind<'s> {
    Enter(Node<'s>),
    Inline,
    Exit(Node<'s>),
    Atom(Atom),
    Stale,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Node<'s> {
    Container(Container<'s>),
    Leaf(Leaf<'s>),
}

#[must_use]
pub fn parse(src: &str) -> Vec<Event> {
    TreeParser::new(src).parse()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Block<'s> {
    /// An atomic block, containing no children elements.
    Atom(Atom),
    /// A leaf block, containing only inline elements.
    Leaf(Leaf<'s>),
    /// A container block, containing children blocks.
    Container(Container<'s>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    /// A line with no non-whitespace characters.
    Blankline,
    /// A list of attributes.
    Attributes,
    /// A thematic break.
    ThematicBreak,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Leaf<'s> {
    Paragraph,
    Heading {
        level: u16,
        has_section: bool,
        pos: u32,
    },
    DescriptionTerm,
    TableCell(Alignment),
    Caption,
    LinkDefinition {
        label: &'s str,
    },
    CodeBlock {
        language: &'s str,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Container<'s> {
    Blockquote,
    Div { class: &'s str },
    List { kind: ListKind, marker: &'s str },
    ListItem(ListItemKind),
    Footnote { label: &'s str },
    Table,
    TableRow { head: bool },
    Section { pos: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListKind {
    pub ty: ListType,
    pub tight: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListItemKind {
    Task { checked: bool },
    Description,
    List,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListType {
    Unordered(u8),
    Ordered(crate::OrderedListNumbering, crate::OrderedListStyle),
    Task,
    Description,
}

#[derive(Debug)]
struct OpenList {
    /// Type of the list, used to determine whether this list should be continued or a new one
    /// should be created.
    ty: ListType,
    /// Depth in the tree where the direct list items of the list are. Needed to determine when to
    /// close the list.
    depth: u16,
    /// Index to event in tree, required to update tightness.
    event: usize,
}

/// Parser for block-level tree structure of entire document.
struct TreeParser<'s> {
    src: &'s str,
    /// The previous block element was a blank line.
    prev_blankline: bool,
    prev_loose: bool,
    attr_start: Option<usize>,
    /// Stack of currently open lists.
    open_lists: Vec<OpenList>,
    /// Stack of currently open sections.
    open_sections: Vec<usize>,
    /// Alignments for each column in for the current table.
    alignments: Vec<Alignment>,
    /// Current container depth.
    open: Vec<usize>,
    /// Buffer queue for next events. Events are buffered until no modifications due to future
    /// characters are needed.
    events: Vec<Event<'s>>,
}

impl<'s> TreeParser<'s> {
    #[must_use]
    fn new(src: &'s str) -> Self {
        Self {
            src,
            prev_blankline: false,
            prev_loose: false,
            attr_start: None,
            open_lists: Vec::new(),
            alignments: Vec::new(),
            open_sections: Vec::new(),
            open: Vec::new(),
            events: Vec::new(),
        }
    }

    #[must_use]
    fn parse(mut self) -> Vec<Event<'s>> {
        let mut lines = lines(self.src).collect::<Vec<_>>();
        let mut line_pos = 0;
        while line_pos < lines.len() {
            let line_count = self.parse_block(&mut lines[line_pos..], true);
            if line_count == 0 {
                break;
            }
            line_pos += line_count;
        }
        while let Some(l) = self.open_lists.pop() {
            self.close_list(l, self.src.len());
        }

        for _ in std::mem::take(&mut self.open_sections).drain(..) {
            self.exit(Span::empty_at(self.src.len()));
        }
        debug_assert_eq!(self.open, &[]);
        self.events
    }

    fn inline(&mut self, span: Span) {
        self.events.push(Event {
            kind: EventKind::Inline,
            span,
        });
    }

    fn enter(&mut self, node: Node<'s>, span: Span) -> usize {
        let i = self.events.len();
        self.open.push(i);
        self.events.push(Event {
            kind: EventKind::Enter(node),
            span,
        });
        i
    }

    fn exit(&mut self, span: Span) -> usize {
        let i = self.events.len();
        let node = if let EventKind::Enter(node) = self.events[self.open.pop().unwrap()].kind {
            node
        } else {
            panic!();
        };
        self.events.push(Event {
            kind: EventKind::Exit(node),
            span,
        });
        i
    }

    /// Recursively parse a block and all of its children. Return number of lines the block uses.
    fn parse_block(&mut self, lines: &mut [Span], top_level: bool) -> usize {
        if let Some(MeteredBlock {
            kind,
            span: span_start,
            line_count,
        }) = MeteredBlock::new(lines.iter().map(|sp| sp.of(self.src)))
        {
            let lines = &mut lines[..line_count];
            let span_start = span_start.translate(lines[0].start());
            let end_line = lines[lines.len() - 1];
            let span_end = match kind {
                Kind::Fenced {
                    has_closing_fence: true,
                    ..
                } => end_line,
                _ => end_line.empty_after(),
            };

            // part of first inline that is from the outer block
            let outer = Span::new(lines[0].start(), span_start.end());

            // skip outer block part for inner content
            lines[0] = lines[0].skip(outer.len());

            // skip opening and closing fence of code block / div
            let lines = if let Kind::Fenced {
                has_closing_fence, ..
            } = kind
            {
                let l = lines.len() - usize::from(has_closing_fence);
                &mut lines[1..l]
            } else {
                lines
            };

            // close list if a non list item or a list item of new type appeared
            if let Some(OpenList { ty, depth, .. }) = self.open_lists.last() {
                debug_assert!(usize::from(*depth) <= self.open.len());
                if self.open.len() == (*depth).into()
                    && !matches!(kind, Kind::ListItem { ty: ty_new, .. } if *ty == ty_new)
                {
                    let l = self.open_lists.pop().unwrap();
                    self.close_list(l, span_start.start());
                }
            }

            // set list to loose if blankline discovered
            if matches!(kind, Kind::Atom(Atom::Blankline)) {
                self.prev_blankline = true;
            } else {
                self.prev_loose = false;
                if self.prev_blankline {
                    if let Some(OpenList { event, depth, .. }) = self.open_lists.last() {
                        if usize::from(*depth) >= self.open.len()
                            || !matches!(kind, Kind::ListItem { .. })
                        {
                            if let EventKind::Enter(Node::Container(List { kind, .. })) =
                                &mut self.events[*event].kind
                            {
                                if kind.tight {
                                    self.prev_loose = true;
                                    kind.tight = false;
                                }
                            }
                        }
                    }
                }
                self.prev_blankline = false;
            }

            let block = match kind {
                Kind::Atom(a) => Block::Atom(a),
                Kind::Paragraph => Block::Leaf(Paragraph),
                Kind::Heading { level } => Block::Leaf(Heading {
                    level: level.try_into().unwrap(),
                    has_section: top_level,
                    pos: span_start.start() as u32,
                }),
                Kind::Fenced {
                    kind: FenceKind::CodeBlock(..),
                    spec,
                    ..
                } => Block::Leaf(CodeBlock { language: spec }),
                Kind::Fenced {
                    kind: FenceKind::Div,
                    spec,
                    ..
                } => Block::Container(Div { class: spec }),
                Kind::Definition {
                    footnote: false,
                    label,
                    ..
                } => Block::Leaf(LinkDefinition { label }),
                Kind::Definition {
                    footnote: true,
                    label,
                    ..
                } => Block::Container(Footnote { label }),
                Kind::Blockquote => Block::Container(Blockquote),
                Kind::ListItem { ty, .. } => Block::Container(ListItem(match ty {
                    ListType::Task => ListItemKind::Task {
                        checked: span_start.of(self.src).as_bytes()[3] != b' ',
                    },
                    ListType::Description => ListItemKind::Description,
                    _ => ListItemKind::List,
                })),
                Kind::Table { .. } => Block::Container(Table),
            };

            match block {
                Block::Atom(a) => self.events.push(Event {
                    kind: EventKind::Atom(a),
                    span: span_start,
                }),
                Block::Leaf(l) => self.parse_leaf(l, &kind, span_start, span_end, lines),
                Block::Container(Table) => self.parse_table(lines, span_start, span_end),
                Block::Container(c) => {
                    self.parse_container(c, &kind, span_start, span_end, outer, lines);
                }
            }

            if matches!(kind, Kind::Atom(Attributes)) {
                self.attr_start = self.attr_start.or_else(|| Some(self.events.len() - 1));
            } else if !matches!(kind, Kind::Atom(Blankline)) {
                self.attr_start = None;
            }

            line_count
        } else {
            0
        }
    }

    fn parse_leaf(
        &mut self,
        leaf: Leaf<'s>,
        k: &Kind,
        span_start: Span,
        span_end: Span,
        mut lines: &mut [Span],
    ) {
        if let Kind::Fenced { indent, .. } = k {
            for line in lines.iter_mut() {
                let indent_line = line
                    .of(self.src)
                    .chars()
                    .take_while(|c| *c != '\n' && c.is_whitespace())
                    .count();
                *line = line.skip_chars((*indent).min(indent_line), self.src);
            }
        } else {
            // trim starting whitespace of each inline
            for line in lines.iter_mut() {
                *line = line.trim_start(self.src);
            }

            // skip first inline if empty
            if lines.get(0).map_or(false, |l| l.is_empty()) {
                lines = &mut lines[1..];
            };

            if matches!(leaf, LinkDefinition { .. }) {
                // trim ending whitespace of each inline
                for line in lines.iter_mut() {
                    *line = line.trim_end(self.src);
                }
            }

            // trim ending whitespace of block
            let l = lines.len();
            if l > 0 {
                let last = &mut lines[l - 1];
                *last = last.trim_end(self.src);
            }
        }

        if let Kind::Heading { level, .. } = k {
            // open and close sections
            if let Leaf::Heading {
                has_section: true, ..
            } = leaf
            {
                let first_close = self
                    .open_sections
                    .iter()
                    .rposition(|l| l < level)
                    .map_or(0, |i| i + 1);
                let pos = span_start.start() as u32;
                for i in 0..(self.open_sections.len() - first_close) {
                    let node = if let EventKind::Enter(node) =
                        self.events[self.open.pop().unwrap()].kind
                    {
                        node
                    } else {
                        panic!();
                    };
                    let end = self
                        .attr_start
                        .map_or(span_start.start(), |a| self.events[a].span.start());
                    self.events.insert(
                        self.attr_start.map_or(self.events.len(), |a| a + i),
                        Event {
                            kind: EventKind::Exit(node),
                            span: Span::new(end, end),
                        },
                    );
                }
                self.open_sections.drain(first_close..);
                self.open_sections.push(*level);
                self.enter(Node::Container(Section { pos }), span_start.empty_before());
            }

            // trim '#' characters
            for line in lines.iter_mut().skip(1) {
                *line = line.trim_start_matches(self.src, |c| c == '#' || c.is_whitespace());
            }
        }

        self.enter(Node::Leaf(leaf), span_start);
        lines
            .iter()
            .filter(|l| !matches!(k, Kind::Heading { .. }) || !l.is_empty())
            .for_each(|line| self.inline(*line));
        self.exit(span_end);
    }

    fn parse_container(
        &mut self,
        c: Container<'s>,
        k: &Kind,
        mut span_start: Span,
        span_end: Span,
        outer: Span,
        lines: &mut [Span],
    ) {
        // update spans, remove indentation / container prefix
        lines.iter_mut().skip(1).for_each(|sp| {
            let src = sp.of(self.src);
            let src_t = src.trim();
            let spaces = src.chars().take_while(|c| c.is_whitespace()).count();
            let skip = match k {
                Kind::Blockquote => {
                    if src_t == ">" {
                        spaces + 1
                    } else if src_t.starts_with('>')
                        && src_t.chars().nth(1).map_or(false, char::is_whitespace)
                    {
                        spaces + 1 + usize::from(src_t.len() > 1)
                    } else {
                        0
                    }
                }
                Kind::ListItem { .. } | Kind::Definition { .. } => {
                    spaces.min(outer.of(self.src).chars().count())
                }
                Kind::Fenced { indent, .. } => spaces.min(*indent),
                _ => panic!("non-container {:?}", k),
            };
            let count = sp.of(self.src).chars().take_while(|c| *c != '\n').count();
            *sp = sp.skip_chars(skip.min(count), self.src);
        });

        if let Kind::ListItem { ty, .. } = k {
            let same_depth = self
                .open_lists
                .last()
                .map_or(true, |OpenList { depth, .. }| {
                    usize::from(*depth) < self.open.len()
                });
            if same_depth {
                let tight = true;
                let event = self.enter(
                    Node::Container(Container::List {
                        kind: ListKind { ty: *ty, tight },
                        marker: span_start.of(self.src),
                    }),
                    span_start.empty_before(),
                );
                self.open_lists.push(OpenList {
                    ty: *ty,
                    depth: self.open.len().try_into().unwrap(),
                    event,
                });
            }
        }

        let dt = if let ListItem(ListItemKind::Description) = c {
            let dt = self.enter(Node::Leaf(DescriptionTerm), span_start);
            self.exit(span_start.trim_end(self.src).empty_after());
            span_start = lines[0].empty_before();
            Some((dt, self.events.len(), self.open.len()))
        } else {
            None
        };

        self.enter(Node::Container(c), span_start);
        let mut l = 0;
        while l < lines.len() {
            l += self.parse_block(&mut lines[l..], false);
        }

        if let Some((empty_term, enter_detail, open_detail)) = dt {
            let enter_term = enter_detail + 1;
            if let Some(first_child) = self.events.get_mut(enter_term) {
                if let EventKind::Enter(Node::Leaf(l @ Paragraph)) = &mut first_child.kind {
                    // convert paragraph into description term
                    *l = DescriptionTerm;
                    let exit_term = if let Some(i) = self.events[enter_term + 1..]
                        .iter_mut()
                        .position(|e| matches!(e.kind, EventKind::Exit(Node::Leaf(Paragraph))))
                    {
                        enter_term + 1 + i
                    } else {
                        panic!()
                    };
                    if let EventKind::Exit(Node::Leaf(l)) = &mut self.events[exit_term].kind {
                        *l = DescriptionTerm;
                    } else {
                        panic!()
                    }

                    // remove empty description term
                    self.events[empty_term].kind = EventKind::Stale;
                    self.events[empty_term + 1].kind = EventKind::Stale;

                    // move out term before detail
                    self.events[enter_term].span = self.events[empty_term].span;
                    let first_detail = self.events[exit_term + 1..]
                        .iter()
                        .position(|e| !matches!(e.kind, EventKind::Atom(Blankline)))
                        .map(|i| exit_term + 1 + i)
                        .unwrap_or(self.events.len());
                    let detail_pos = self
                        .events
                        .get(first_detail)
                        .map(|e| e.span.start())
                        .unwrap_or_else(|| self.events.last().unwrap().span.end());
                    self.events
                        .copy_within(enter_term..first_detail, enter_detail);
                    self.events[first_detail - 1] = Event {
                        kind: EventKind::Enter(Node::Container(c)),
                        span: Span::empty_at(detail_pos),
                    };
                    self.open[open_detail] = first_detail - 1;
                }
            }
        }

        if let Some(OpenList { depth, .. }) = self.open_lists.last() {
            debug_assert!(usize::from(*depth) <= self.open.len());
            if self.open.len() == (*depth).into() {
                self.prev_blankline = false;
                self.prev_loose = false;
                let l = self.open_lists.pop().unwrap();
                self.close_list(l, span_end.start());
            }
        }

        self.exit(span_end);
    }

    fn parse_table(&mut self, lines: &mut [Span], span_start: Span, span_end: Span) {
        self.alignments.clear();
        self.enter(Node::Container(Table), span_start);

        let caption_line = lines
            .iter()
            .position(|sp| sp.of(self.src).trim_start().starts_with('^'))
            .map_or(lines.len(), |caption_line| {
                self.enter(Node::Leaf(Caption), span_start);
                lines[caption_line] = lines[caption_line]
                    .trim_start(self.src)
                    .skip_chars(2, self.src);
                lines[lines.len() - 1] = lines[lines.len() - 1].trim_end(self.src);
                for line in &lines[caption_line..] {
                    self.inline(*line);
                }
                self.exit(span_end);
                caption_line
            });

        let mut last_row_event = None;
        for row in &lines[..caption_line] {
            let row = row.trim(self.src);
            if row.is_empty() {
                break;
            }
            let row_event_enter =
                self.enter(Node::Container(TableRow { head: false }), row.with_len(1));
            let rem = row.skip(1); // |
            let lex = lex::Lexer::new(rem.of(self.src));
            let mut pos = rem.start();
            let mut cell_start = pos;
            let mut separator_row = true;
            let mut verbatim = None;
            let mut column_index = 0;
            for lex::Token { kind, len } in lex {
                if let Some(l) = verbatim {
                    if matches!(kind, lex::Kind::Seq(lex::Sequence::Backtick)) && len == l {
                        verbatim = None;
                    }
                } else {
                    match kind {
                        lex::Kind::Sym(lex::Symbol::Pipe) => {
                            let span = Span::new(cell_start, pos).trim(self.src);
                            let cell = span.of(self.src);
                            let separator_cell = match cell.len() {
                                0 => false,
                                1 => cell == "-",
                                2 => matches!(cell, ":-" | "--" | "-:"),
                                l => {
                                    matches!(cell.as_bytes()[0], b'-' | b':')
                                        && matches!(cell.as_bytes()[l - 1], b'-' | b':')
                                        && cell.chars().skip(1).take(l - 2).all(|c| c == '-')
                                }
                            };
                            separator_row &= separator_cell;
                            self.enter(
                                Node::Leaf(TableCell(
                                    self.alignments
                                        .get(column_index)
                                        .copied()
                                        .unwrap_or(Alignment::Unspecified),
                                )),
                                Span::empty_at(cell_start),
                            );
                            self.inline(span);
                            self.exit(Span::new(pos, pos + 1));
                            cell_start = pos + len;
                            column_index += 1;
                        }
                        lex::Kind::Seq(lex::Sequence::Backtick) => {
                            verbatim = Some(len);
                        }
                        _ => {}
                    }
                }
                pos += len;
            }

            if separator_row && verbatim.is_none() {
                self.alignments.clear();
                self.alignments.extend(
                    self.events[row_event_enter + 1..]
                        .iter()
                        .filter(|e| matches!(e.kind, EventKind::Inline))
                        .map(|e| {
                            let cell = e.span.of(self.src);
                            let l = cell.as_bytes()[0] == b':';
                            let r = cell.as_bytes()[cell.len() - 1] == b':';
                            match (l, r) {
                                (false, false) => Alignment::Unspecified,
                                (false, true) => Alignment::Right,
                                (true, false) => Alignment::Left,
                                (true, true) => Alignment::Center,
                            }
                        }),
                );
                self.open.pop();
                self.events.drain(row_event_enter..); // remove table row
                if let Some((head_row_enter, head_row_exit)) = last_row_event {
                    self.events[head_row_enter + 1..]
                        .iter_mut()
                        .filter(|e| {
                            matches!(
                                e.kind,
                                EventKind::Enter(Node::Leaf(TableCell(..)))
                                    | EventKind::Exit(Node::Leaf(TableCell(..)))
                            )
                        })
                        .zip(
                            self.alignments
                                .iter()
                                .copied()
                                .chain(std::iter::repeat(Alignment::Unspecified))
                                .flat_map(|a| [a, a].into_iter()),
                        )
                        .for_each(|(e, new_align)| match &mut e.kind {
                            EventKind::Enter(Node::Leaf(TableCell(alignment)))
                            | EventKind::Exit(Node::Leaf(TableCell(alignment))) => {
                                *alignment = new_align;
                            }
                            _ => panic!(),
                        });
                    let event: &mut Event = &mut self.events[head_row_enter];
                    if let EventKind::Enter(Node::Container(TableRow { head })) = &mut event.kind {
                        *head = true;
                    } else {
                        panic!()
                    }
                    let event: &mut Event = &mut self.events[head_row_exit];
                    if let EventKind::Exit(Node::Container(TableRow { head })) = &mut event.kind {
                        *head = true;
                    } else {
                        panic!()
                    }
                }
            } else {
                let row_event_exit = self.exit(Span::empty_at(pos)); // table row
                last_row_event = Some((row_event_enter, row_event_exit));
            }
        }

        self.exit(span_end);
    }

    fn close_list(&mut self, list: OpenList, pos: usize) {
        if self.prev_loose {
            if let EventKind::Enter(Node::Container(List { kind, .. })) =
                &mut self.events[list.event].kind
            {
                // ignore blankline at end
                kind.tight = true;
            } else {
                panic!()
            }
        }

        self.exit(Span::empty_at(pos)); // list
    }
}

/// Parser for a single block.
struct MeteredBlock<'s> {
    kind: Kind<'s>,
    span: Span,
    line_count: usize,
}

impl<'s> MeteredBlock<'s> {
    /// Identify and measure the line length of a single block.
    fn new<I: Iterator<Item = &'s str>>(mut lines: I) -> Option<Self> {
        lines.next().map(|l| {
            let IdentifiedBlock { mut kind, span } = IdentifiedBlock::new(l);
            let line_count = 1 + lines.take_while(|l| kind.continues(l)).count();
            Self {
                kind,
                span,
                line_count,
            }
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FenceKind {
    Div,
    CodeBlock(u8),
}

#[cfg_attr(test, derive(PartialEq, Eq))]
#[derive(Debug)]
enum Kind<'s> {
    Atom(Atom),
    Paragraph,
    Heading {
        level: usize,
    },
    Fenced {
        indent: usize,
        fence_length: usize,
        kind: FenceKind,
        spec: &'s str,
        has_closing_fence: bool,
    },
    Definition {
        indent: usize,
        footnote: bool,
        label: &'s str,
    },
    Blockquote,
    ListItem {
        indent: usize,
        ty: ListType,
        last_blankline: bool,
    },
    Table {
        caption: bool,
    },
}

struct IdentifiedBlock<'s> {
    kind: Kind<'s>,
    span: Span,
}

impl<'s> IdentifiedBlock<'s> {
    fn new(line: &'s str) -> Self {
        let mut chars = line.chars();
        let indent = chars
            .clone()
            .take_while(|c| *c != '\n' && c.is_whitespace())
            .count();
        (&mut chars).take(indent).last();
        let indent_bytes = line.len() - chars.as_str().len();
        let line = chars.as_str();
        let line_t = line.trim_end();
        let l = line.len();
        let lt = line_t.len();

        let first = if let Some(c) = chars.next() {
            c
        } else {
            return Self {
                kind: Kind::Atom(Blankline),
                span: Span::empty_at(indent_bytes),
            };
        };

        match first {
            '\n' => Some((Kind::Atom(Blankline), Span::by_len(indent_bytes, 1))),
            '#' => chars
                .find(|c| *c != '#')
                .map_or(true, char::is_whitespace)
                .then(|| {
                    let level = line.chars().take_while(|c| *c == '#').count();
                    (Kind::Heading { level }, Span::by_len(indent_bytes, level))
                }),
            '>' => {
                if chars.next().map_or(true, char::is_whitespace) {
                    Some((Kind::Blockquote, Span::by_len(indent_bytes, 1)))
                } else {
                    None
                }
            }
            '{' => (attr::valid(line.chars()) == lt)
                .then(|| (Kind::Atom(Attributes), Span::by_len(indent_bytes, l))),
            '|' => {
                if lt >= 2 && line_t.ends_with('|') && !line_t.ends_with("\\|") {
                    Some((Kind::Table { caption: false }, Span::empty_at(indent_bytes)))
                } else {
                    None
                }
            }
            '[' => chars.as_str().find("]:").map(|l| {
                let label = &chars.as_str()[0..l];
                let footnote = label.starts_with('^');
                (
                    Kind::Definition {
                        indent,
                        footnote,
                        label: &label[usize::from(footnote)..],
                    },
                    Span::by_len(0, indent_bytes + 3 + l),
                )
            }),
            '-' | '*' if Self::is_thematic_break(chars.clone()) => {
                Some((Kind::Atom(ThematicBreak), Span::by_len(indent_bytes, lt)))
            }
            b @ ('-' | '*' | '+') => chars.next().map_or(true, |c| c == ' ').then(|| {
                let task_list = chars.next() == Some('[')
                    && matches!(chars.next(), Some('x' | 'X' | ' '))
                    && chars.next() == Some(']')
                    && chars.next().map_or(true, char::is_whitespace);
                if task_list {
                    (
                        Kind::ListItem {
                            indent,
                            ty: Task,
                            last_blankline: false,
                        },
                        Span::by_len(indent_bytes, 5),
                    )
                } else {
                    (
                        Kind::ListItem {
                            indent,
                            ty: Unordered(b as u8),
                            last_blankline: false,
                        },
                        Span::by_len(indent_bytes, 1),
                    )
                }
            }),
            ':' if chars.clone().next().map_or(true, char::is_whitespace) => Some((
                Kind::ListItem {
                    indent,
                    ty: Description,
                    last_blankline: false,
                },
                Span::by_len(indent_bytes, 1),
            )),
            f @ ('`' | ':' | '~') => {
                let fence_length = 1 + (&mut chars).take_while(|c| *c == f).count();
                let spec = &line_t[fence_length..].trim_start();
                let valid_spec = if f == ':' {
                    spec.chars().all(attr::is_name)
                } else {
                    !spec.chars().any(char::is_whitespace) && !spec.chars().any(|c| c == '`')
                };
                (valid_spec && fence_length >= 3).then(|| {
                    (
                        Kind::Fenced {
                            indent,
                            fence_length,
                            kind: match f {
                                ':' => FenceKind::Div,
                                _ => FenceKind::CodeBlock(f as u8),
                            },
                            spec,
                            has_closing_fence: false,
                        },
                        Span::by_len(indent_bytes, line.len()),
                    )
                })
            }
            c => Self::maybe_ordered_list_item(c, chars).map(|(num, style, len)| {
                (
                    Kind::ListItem {
                        indent,
                        ty: Ordered(num, style),
                        last_blankline: false,
                    },
                    Span::by_len(indent_bytes, len),
                )
            }),
        }
        .map(|(kind, span)| Self { kind, span })
        .unwrap_or(Self {
            kind: Kind::Paragraph,
            span: Span::empty_at(indent_bytes),
        })
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

    fn maybe_ordered_list_item(
        mut first: char,
        mut chars: std::str::Chars,
    ) -> Option<(crate::OrderedListNumbering, crate::OrderedListStyle, usize)> {
        fn is_roman_lower_digit(c: char) -> bool {
            matches!(c, 'i' | 'v' | 'x' | 'l' | 'c' | 'd' | 'm')
        }

        fn is_roman_upper_digit(c: char) -> bool {
            matches!(c, 'I' | 'V' | 'X' | 'L' | 'C' | 'D' | 'M')
        }

        let start_paren = first == '(';
        if start_paren {
            first = chars.next()?;
        }

        let numbering = if first.is_ascii_digit() {
            Decimal
        } else if first.is_ascii_lowercase() {
            AlphaLower
        } else if first.is_ascii_uppercase() {
            AlphaUpper
        } else if is_roman_lower_digit(first) {
            RomanLower
        } else if is_roman_upper_digit(first) {
            RomanUpper
        } else {
            return None;
        };

        let max_len = match numbering {
            Decimal => 19,
            AlphaLower | AlphaUpper | RomanLower | RomanUpper => 13,
        };

        let chars_num = chars.clone();
        let len_num = 1 + chars_num
            .clone()
            .take(max_len - 1)
            .take_while(|c| match numbering {
                Decimal => c.is_ascii_digit(),
                AlphaLower => c.is_ascii_lowercase(),
                AlphaUpper => c.is_ascii_uppercase(),
                RomanLower => is_roman_lower_digit(*c),
                RomanUpper => is_roman_upper_digit(*c),
            })
            .count();

        let post_num = chars.nth(len_num - 1)?;
        let style = if start_paren {
            if post_num == ')' {
                ParenParen
            } else {
                return None;
            }
        } else if post_num == ')' {
            Paren
        } else if post_num == '.' {
            Period
        } else {
            return None;
        };
        let len_style = usize::from(start_paren) + 1;

        let chars_num = std::iter::once(first).chain(chars_num.take(len_num - 1));
        let numbering = if matches!(numbering, AlphaLower)
            && chars_num.clone().all(is_roman_lower_digit)
        {
            RomanLower
        } else if matches!(numbering, AlphaUpper) && chars_num.clone().all(is_roman_upper_digit) {
            RomanUpper
        } else {
            numbering
        };

        if chars.next().map_or(true, char::is_whitespace) {
            Some((numbering, style, len_num + len_style))
        } else {
            None
        }
    }
}

impl<'s> Kind<'s> {
    /// Determine if a line continues the block.
    fn continues(&mut self, line: &'s str) -> bool {
        let IdentifiedBlock { kind: next, .. } = IdentifiedBlock::new(line);
        match self {
            Self::Atom(..)
            | Self::Fenced {
                has_closing_fence: true,
                ..
            } => false,
            Self::Blockquote => matches!(next, Self::Blockquote | Self::Paragraph),
            Self::Heading { level } => {
                matches!(next, Self::Paragraph)
                    || matches!(next, Self::Heading { level: l } if l == *level )
            }
            Self::Paragraph | Self::Table { caption: true } => {
                !matches!(next, Self::Atom(Blankline))
            }
            Self::ListItem {
                indent,
                last_blankline,
                ..
            } => {
                let spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                let para = !*last_blankline && matches!(next, Self::Paragraph);
                let blankline = matches!(next, Self::Atom(Blankline));
                *last_blankline = blankline;
                blankline || spaces > *indent || para
            }
            Self::Definition {
                indent, footnote, ..
            } => {
                if *footnote {
                    let spaces = line.chars().take_while(|c| c.is_whitespace()).count();
                    matches!(next, Self::Atom(Blankline)) || spaces > *indent
                } else {
                    line.starts_with(' ') && !matches!(next, Self::Atom(Blankline))
                }
            }
            Self::Fenced {
                fence_length,
                kind,
                has_closing_fence,
                ..
            } => {
                if let Kind::Fenced {
                    kind: k,
                    fence_length: l,
                    spec,
                    ..
                } = next
                {
                    if spec.is_empty() {
                        *has_closing_fence = k == *kind
                            && (l == *fence_length
                                || (matches!(k, FenceKind::Div) && l > *fence_length));
                    }
                }
                true
            }
            Self::Table { caption } => {
                matches!(next, Self::Table { .. } | Self::Atom(Blankline)) || {
                    if line.trim().starts_with("^ ") {
                        *caption = true;
                        true
                    } else {
                        false
                    }
                }
            }
        }
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
    use crate::Alignment;
    use crate::OrderedListNumbering::*;
    use crate::OrderedListStyle::*;

    use super::Atom::*;
    use super::Container::*;
    use super::EventKind::*;
    use super::FenceKind;
    use super::Kind;
    use super::Leaf::*;
    use super::ListItemKind;
    use super::ListKind;
    use super::ListType::*;
    use super::Node::*;

    macro_rules! test_parse {
        ($src:expr $(,$($event:expr),* $(,)?)?) => {
            let t = super::TreeParser::new($src).parse();
            let actual = t.into_iter().map(|ev| (ev.kind, ev.span.of($src))).collect::<Vec<_>>();
            let expected = &[$($($event),*,)?];
            assert_eq!(
                actual,
                expected,
                concat!(
                    "\n",
                    "\x1b[0;1m====================== INPUT =========================\x1b[0m\n",
                    "\x1b[2m{}",
                    "\x1b[0;1m================ ACTUAL vs EXPECTED ==================\x1b[0m\n",
                    "{}",
                    "\x1b[0;1m======================================================\x1b[0m\n",
                ),
                $src,
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
    fn parse_para_oneline() {
        test_parse!(
            "para\n",
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_para_multiline() {
        test_parse!(
            "para0\npara1\n",
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para0\n"),
            (Inline, "para1"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_heading() {
        test_parse!(
            concat!(
                "# a\n",
                "## b\n", //
            ),
            (Enter(Container(Section { pos: 0 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                "#"
            ),
            (Inline, "a"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                ""
            ),
            (Enter(Container(Section { pos: 4 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 4
                })),
                "##"
            ),
            (Inline, "b"),
            (
                Exit(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 4
                })),
                ""
            ),
            (Exit(Container(Section { pos: 4 })), ""),
            (Exit(Container(Section { pos: 0 })), ""),
        );
    }

    #[test]
    fn parse_heading_empty_first_line() {
        test_parse!(
            concat!(
                "#\n",
                "heading\n", //
            ),
            (Enter(Container(Section { pos: 0 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                "#"
            ),
            (Inline, "heading"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                ""
            ),
            (Exit(Container(Section { pos: 0 })), ""),
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
            (Enter(Container(Section { pos: 0 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0,
                })),
                "#"
            ),
            (Inline, "2"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0,
                })),
                ""
            ),
            (Atom(Blankline), "\n"),
            (Exit(Container(Section { pos: 0 })), ""),
            (Enter(Container(Section { pos: 6 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 6,
                })),
                "#"
            ),
            (Inline, "8\n"),
            (Inline, "12\n"),
            (Inline, "15"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 6,
                })),
                ""
            ),
            (Exit(Container(Section { pos: 6 })), ""),
        );
    }

    #[test]
    fn parse_heading_multi_repeat() {
        test_parse!(
            concat!(
                "# a\n",
                "# b\n",
                "c\n", //
            ),
            (Enter(Container(Section { pos: 0 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                "#"
            ),
            (Inline, "a\n"),
            (Inline, "b\n"),
            (Inline, "c"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0
                })),
                "",
            ),
            (Exit(Container(Section { pos: 0 })), ""),
        );
    }

    #[test]
    fn parse_section() {
        test_parse!(
            concat!(
                "# a\n",
                "\n",
                "## aa\n",
                "\n",
                "#### aaaa\n",
                "\n",
                "## ab\n",
                "\n",
                "### aba\n",
                "\n",
                "# b\n",
            ),
            (Enter(Container(Section { pos: 0 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0,
                })),
                "#"
            ),
            (Inline, "a"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 0,
                })),
                "",
            ),
            (Atom(Blankline), "\n"),
            (Enter(Container(Section { pos: 5 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 5,
                })),
                "##"
            ),
            (Inline, "aa"),
            (
                Exit(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 5,
                })),
                "",
            ),
            (Atom(Blankline), "\n"),
            (Enter(Container(Section { pos: 12 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 4,
                    has_section: true,
                    pos: 12,
                })),
                "####"
            ),
            (Inline, "aaaa"),
            (
                Exit(Leaf(Heading {
                    level: 4,
                    has_section: true,
                    pos: 12,
                })),
                "",
            ),
            (Atom(Blankline), "\n"),
            (Exit(Container(Section { pos: 12 })), ""),
            (Exit(Container(Section { pos: 5 })), ""),
            (Enter(Container(Section { pos: 23 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 23,
                })),
                "##"
            ),
            (Inline, "ab"),
            (
                Exit(Leaf(Heading {
                    level: 2,
                    has_section: true,
                    pos: 23,
                })),
                "",
            ),
            (Atom(Blankline), "\n"),
            (Enter(Container(Section { pos: 30 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 3,
                    has_section: true,
                    pos: 30,
                })),
                "###"
            ),
            (Inline, "aba"),
            (
                Exit(Leaf(Heading {
                    level: 3,
                    has_section: true,
                    pos: 30,
                })),
                "",
            ),
            (Atom(Blankline), "\n"),
            (Exit(Container(Section { pos: 30 })), ""),
            (Exit(Container(Section { pos: 23 })), ""),
            (Exit(Container(Section { pos: 0 })), ""),
            (Enter(Container(Section { pos: 39 })), ""),
            (
                Enter(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 39,
                })),
                "#"
            ),
            (Inline, "b"),
            (
                Exit(Leaf(Heading {
                    level: 1,
                    has_section: true,
                    pos: 39,
                })),
                "",
            ),
            (Exit(Container(Section { pos: 39 })), ""),
        );
    }

    #[test]
    fn parse_blockquote() {
        test_parse!(
            "> a\n",
            (Enter(Container(Blockquote)), ">"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Blockquote)), ""),
        );
        test_parse!(
            "> a\nb\nc\n",
            (Enter(Container(Blockquote)), ">"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a\n"),
            (Inline, "b\n"),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Blockquote)), ""),
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
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Leaf(Heading {
                    level: 2,
                    has_section: false,
                    pos: 8,
                })),
                "##"
            ),
            (Inline, "hl"),
            (
                Exit(Leaf(Heading {
                    level: 2,
                    has_section: false,
                    pos: 8,
                })),
                ""
            ),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Blockquote)), ""),
        );
    }

    #[test]
    fn parse_blockquote_empty() {
        test_parse!(
            "> \n",
            (Enter(Container(Blockquote)), ">"),
            (Atom(Blankline), "\n"),
            (Exit(Container(Blockquote)), ""),
        );
        test_parse!(
            ">",
            (Enter(Container(Blockquote)), ">"),
            (Atom(Blankline), ""),
            (Exit(Container(Blockquote)), ""),
        );
    }

    #[test]
    fn parse_code_block() {
        test_parse!(
            concat!(
                "```\n", //
                "l0\n"   //
            ),
            (Enter(Leaf(CodeBlock { language: "" })), "```\n",),
            (Inline, "l0\n"),
            (Exit(Leaf(CodeBlock { language: "" })), "",),
        );
        test_parse!(
            concat!(
                "```\n",
                "l0\n",
                "```\n",
                "\n",
                "para\n", //
            ),
            (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
            (Inline, "l0\n"),
            (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
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
            (Enter(Leaf(CodeBlock { language: "lang" })), "````  lang\n",),
            (Inline, "l0\n"),
            (Inline, "```\n"),
            (Inline, " l1\n"),
            (Exit(Leaf(CodeBlock { language: "lang" })), "````"),
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
            (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
            (Inline, "a\n"),
            (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
            (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
            (Inline, "bbb\n"),
            (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
        );
        test_parse!(
            concat!(
                "~~~\n",
                "code\n",
                "  block\n",
                "~~~\n", //
            ),
            (Enter(Leaf(CodeBlock { language: "" })), "~~~\n"),
            (Inline, "code\n"),
            (Inline, "  block\n"),
            (Exit(Leaf(CodeBlock { language: "" })), "~~~\n"),
        );
        test_parse!(
            "    ```abc\n",
            (Enter(Leaf(CodeBlock { language: "abc" })), "```abc\n"),
            (Exit(Leaf(CodeBlock { language: "abc" })), ""),
        );
    }

    #[test]
    fn parse_link_definition() {
        test_parse!(
            "[tag]: url\n",
            (Enter(Leaf(LinkDefinition { label: "tag" })), "[tag]:"),
            (Inline, "url"),
            (Exit(Leaf(LinkDefinition { label: "tag" })), ""),
        );
    }

    #[test]
    fn parse_footnote() {
        test_parse!(
            "[^tag]: description\n",
            (Enter(Container(Footnote { label: "tag" })), "[^tag]:"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "description"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Footnote { label: "tag" })), ""),
        );
    }

    #[test]
    fn parse_footnote_post() {
        test_parse!(
            concat!(
                "[^a]\n",
                "\n",
                "[^a]: note\n",
                "\n",
                "para\n", //
            ),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "[^a]"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Container(Footnote { label: "a" })), "[^a]:"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "note"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(Footnote { label: "a" })), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_attr() {
        test_parse!(
            "{.some_class}\npara\n",
            (Atom(Attributes), "{.some_class}\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
        test_parse!(
            concat!(
                "{.a}\n", //
                "\n",     //
                "{.b}\n", //
                "\n",     //
                "para\n", //
            ),
            (Atom(Attributes), "{.a}\n"),
            (Atom(Blankline), "\n"),
            (Atom(Attributes), "{.b}\n"),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_list_single_item() {
        test_parse!(
            "- abc",
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "abc"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_list_tight() {
        test_parse!(
            concat!(
                "- a\n", //
                "- b\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_list_loose() {
        test_parse!(
            concat!(
                "- a\n", //
                "- b\n", //
                "\n",    //
                "- c\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: false,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: false,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_list_tight_loose() {
        test_parse!(
            concat!(
                "- a\n",    //
                "- b\n",    //
                "\n",       //
                "   - c\n", //
                "\n",       //
                "     d\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: false,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "d"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: false,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_list_tight_nest() {
        test_parse!(
            concat!(
                "- a\n",    //
                "\n",       //
                "  + aa\n", //
                "  + ab\n", //
                "\n",       //
                "- b\n",    //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true,
                    },
                    marker: "+",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "+"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "aa"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "+"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "ab"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true,
                    },
                    marker: "+",
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
        test_parse!(
            concat!(
                "1. a\n",  //
                "\n",      //
                "  - b\n", //
                "\n",      //
                " c\n",    //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Ordered(Decimal, Period),
                        tight: true,
                    },
                    marker: "1.",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "1."),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                "",
            ),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Ordered(Decimal, Period),
                        tight: true,
                    },
                    marker: "1.",
                })),
                "",
            ),
        );
    }

    #[test]
    fn parse_list_nest() {
        test_parse!(
            concat!(
                "- a\n",     //
                "    \n",    //
                "  + b\n",   //
                "      \n",  //
                "    * c\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true,
                    },
                    marker: "+",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "+"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'*'),
                        tight: true,
                    },
                    marker: "*",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "*"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'*'),
                        tight: true,
                    },
                    marker: "*",
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true,
                    },
                    marker: "+",
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_list_post() {
        test_parse!(
            concat!(
                "- a\n",   //
                "\n",      //
                "  * b\n", //
                "\n",      //
                "cd\n",    //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'*'),
                        tight: true
                    },
                    marker: "*",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "*"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'*'),
                        tight: true
                    },
                    marker: "*",
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "cd"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_list_mixed() {
        test_parse!(
            concat!(
                "- a\n", //
                "+ b\n", //
                "+ c\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                ""
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true
                    },
                    marker: "+",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "+"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "+"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'+'),
                        tight: true
                    },
                    marker: "+",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_description_list() {
        test_parse!(
            concat!(
                ": term\n",         //
                "\n",               //
                "   description\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: true,
                    },
                    marker: ":",
                })),
                ""
            ),
            (Stale, ":"),
            (Stale, ""),
            (Enter(Leaf(DescriptionTerm)), ":"),
            (Inline, "term"),
            (Exit(Leaf(DescriptionTerm)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Container(ListItem(ListItemKind::Description))), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "description"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::Description))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: true,
                    },
                    marker: ":",
                })),
                ""
            ),
        );
        test_parse!(
            concat!(
                ": apple\n",
                "   fruit\n",
                "\n",
                "   Paragraph one\n",
                "\n",
                "   Paragraph two\n",
                "\n",
                "   - sub\n",
                "   - list\n",
                "\n",
                ": orange\n",
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: false
                    },
                    marker: ":",
                })),
                "",
            ),
            (Stale, ":"),
            (Stale, ""),
            (Enter(Leaf(DescriptionTerm)), ":"),
            (Inline, "apple\n"),
            (Inline, "fruit"),
            (Exit(Leaf(DescriptionTerm)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Container(ListItem(ListItemKind::Description))), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "Paragraph one"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "Paragraph two"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                "",
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "sub"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "list"),
            (Exit(Leaf(Paragraph)), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true
                    },
                    marker: "-",
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::Description))), ""),
            (Stale, ":"),
            (Stale, ""),
            (Enter(Leaf(DescriptionTerm)), ":"),
            (Inline, "orange"),
            (Exit(Leaf(DescriptionTerm)), ""),
            (Enter(Container(ListItem(ListItemKind::Description))), ""),
            (Exit(Container(ListItem(ListItemKind::Description))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: false
                    },
                    marker: ":",
                })),
                "",
            ),
        );
    }

    #[test]
    fn parse_description_list_empty() {
        test_parse!(
            ":\n",
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: true,
                    },
                    marker: ":",
                })),
                ""
            ),
            (Enter(Leaf(DescriptionTerm)), ":"),
            (Exit(Leaf(DescriptionTerm)), ""),
            (Enter(Container(ListItem(ListItemKind::Description))), ""),
            (Atom(Blankline), "\n"),
            (Exit(Container(ListItem(ListItemKind::Description))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Description,
                        tight: true,
                    },
                    marker: ":",
                })),
                ""
            ),
        );
    }

    #[test]
    fn parse_table() {
        test_parse!(
            concat!(
                "|a|b|c|\n", //
                "|-|-|-|\n", //
                "|1|2|3|\n", //
            ),
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: true })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "a"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "b"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "c"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: true })), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "1"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "2"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "3"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), "")
        );
    }

    #[test]
    fn parse_table_empty() {
        test_parse!(
            "||",
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, ""),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), ""),
        );
    }

    #[test]
    fn parse_table_escaped() {
        test_parse!(
            "|a\\|\n",
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "|a\\|"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_table_post() {
        test_parse!(
            "|a|\npara",
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "a"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_table_align() {
        test_parse!(
            concat!(
                "|:---|:----:|----:|\n",
                "|left|center|right|\n", //
            ),
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Left))), ""),
            (Inline, "left"),
            (Exit(Leaf(TableCell(Alignment::Left))), "|"),
            (Enter(Leaf(TableCell(Alignment::Center))), ""),
            (Inline, "center"),
            (Exit(Leaf(TableCell(Alignment::Center))), "|"),
            (Enter(Leaf(TableCell(Alignment::Right))), ""),
            (Inline, "right"),
            (Exit(Leaf(TableCell(Alignment::Right))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), "")
        );
        test_parse!(
            concat!(
                "||\n",   //
                "|-:|\n", //
            ),
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: true })), "|"),
            (Enter(Leaf(TableCell(Alignment::Right))), ""),
            (Inline, ""),
            (Exit(Leaf(TableCell(Alignment::Right))), "|"),
            (Exit(Container(TableRow { head: true })), ""),
            (Exit(Container(Table)), ""),
        );
    }

    #[test]
    fn parse_table_caption() {
        test_parse!(
            "|a|\n^ caption",
            (Enter(Container(Table)), ""),
            (Enter(Leaf(Caption)), ""),
            (Inline, "caption"),
            (Exit(Leaf(Caption)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "a"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), ""),
        );
    }

    #[test]
    fn parse_table_caption_multiline() {
        test_parse!(
            concat!(
                "|a|\n",       //
                "\n",          //
                "^ caption\n", //
                "continued\n", //
                "\n",          //
                "para\n",      //
            ),
            (Enter(Container(Table)), ""),
            (Enter(Leaf(Caption)), ""),
            (Inline, "caption\n"),
            (Inline, "continued"),
            (Exit(Leaf(Caption)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "a"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), ""),
            (Atom(Blankline), "\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "para"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_table_caption_empty() {
        test_parse!(
            "|a|\n^ ",
            (Enter(Container(Table)), ""),
            (Enter(Container(TableRow { head: false })), "|"),
            (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
            (Inline, "a"),
            (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
            (Exit(Container(TableRow { head: false })), ""),
            (Exit(Container(Table)), ""),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "^"),
            (Exit(Leaf(Paragraph)), ""),
        );
    }

    #[test]
    fn parse_table_sep_row_only() {
        test_parse!(
            "|-|-|",
            (Enter(Container(Table)), ""),
            (Exit(Container(Table)), "")
        );
    }

    #[test]
    fn parse_div() {
        test_parse!(
            concat!(
                "::: cls\n", //
                "abc\n",     //
                ":::\n",     //
            ),
            (Enter(Container(Div { class: "cls" })), "::: cls\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "abc"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Div { class: "cls" })), ":::\n"),
        );
    }

    #[test]
    fn parse_div_no_class() {
        test_parse!(
            concat!(
                ":::\n", //
                "abc\n", //
                ":::\n", //
            ),
            (Enter(Container(Div { class: "" })), ":::\n"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "abc"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(Div { class: "" })), ":::\n"),
        );
    }

    #[test]
    fn parse_inner_indent() {
        test_parse!(
            concat!(
                "- - a\n", //
                "  - b\n", //
            ),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (
                Enter(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "a"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "b"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    kind: ListKind {
                        ty: Unordered(b'-'),
                        tight: true,
                    },
                    marker: "-",
                })),
                ""
            ),
        );
    }

    macro_rules! test_block {
        ($src:expr, $kind:expr, $str:expr, $len:expr $(,)?) => {
            let lines = super::lines($src).map(|sp| sp.of($src));
            let mb = super::MeteredBlock::new(lines).unwrap();
            assert_eq!(
                (mb.kind, mb.span.of($src), mb.line_count),
                ($kind, $str, $len),
                "\n\n{}\n\n",
                $src
            );
        };
    }

    #[test]
    fn block_blankline() {
        test_block!("\n", Kind::Atom(Blankline), "\n", 1);
        test_block!(" \n", Kind::Atom(Blankline), "\n", 1);
    }

    #[test]
    fn block_multiline() {
        test_block!(
            "# heading\n spanning two lines\n",
            Kind::Heading { level: 1 },
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
            Kind::Blockquote,
            ">",
            5,
        );
    }

    #[test]
    fn block_thematic_break() {
        test_block!("---\n", Kind::Atom(ThematicBreak), "---", 1);
        test_block!(
            concat!(
                "   -*- -*-\n",
                "\n",
                "para", //
            ),
            Kind::Atom(ThematicBreak),
            "-*- -*-",
            1
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
            Kind::Fenced {
                indent: 0,
                kind: FenceKind::CodeBlock(b'`'),
                fence_length: 4,
                spec: "lang",
                has_closing_fence: true,
            },
            "````  lang\n",
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
            Kind::Fenced {
                indent: 0,
                kind: FenceKind::CodeBlock(b'`'),
                fence_length: 3,
                spec: "",
                has_closing_fence: true,
            },
            "```\n",
            3,
        );
        test_block!(
            concat!(
                "``` no space in lang specifier\n",
                "l0\n",
                "```\n", //
            ),
            Kind::Paragraph,
            "",
            3,
        );
    }

    #[test]
    fn block_link_definition() {
        test_block!(
            "[tag]: url\n",
            Kind::Definition {
                indent: 0,
                footnote: false,
                label: "tag",
            },
            "[tag]:",
            1
        );
    }

    #[test]
    fn block_link_definition_multiline() {
        test_block!(
            concat!(
                "[tag]: uuu\n",
                " rl\n", //
            ),
            Kind::Definition {
                indent: 0,
                footnote: false,
                label: "tag",
            },
            "[tag]:",
            2,
        );
        test_block!(
            concat!(
                "[tag]: url\n",
                "para\n", //
            ),
            Kind::Definition {
                indent: 0,
                footnote: false,
                label: "tag",
            },
            "[tag]:",
            1,
        );
    }

    #[test]
    fn block_footnote_empty() {
        test_block!(
            "[^tag]:\n",
            Kind::Definition {
                indent: 0,
                footnote: true,
                label: "tag",
            },
            "[^tag]:",
            1
        );
    }

    #[test]
    fn block_footnote_single() {
        test_block!(
            "[^tag]: a\n",
            Kind::Definition {
                indent: 0,
                footnote: true,
                label: "tag",
            },
            "[^tag]:",
            1
        );
    }

    #[test]
    fn block_footnote_multiline() {
        test_block!(
            concat!(
                "[^tag]: a\n",
                " b\n", //
            ),
            Kind::Definition {
                indent: 0,
                footnote: true,
                label: "tag",
            },
            "[^tag]:",
            2,
        );
    }

    #[test]
    fn block_footnote_multiline_post() {
        test_block!(
            concat!(
                "[^tag]: a\n",
                " b\n",
                "\n",
                "para\n", //
            ),
            Kind::Definition {
                indent: 0,
                footnote: true,
                label: "tag",
            },
            "[^tag]:",
            3,
        );
    }

    #[test]
    fn block_list_bullet() {
        test_block!(
            "- abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Unordered(b'-'),
                last_blankline: false,
            },
            "-",
            1
        );
        test_block!(
            "+ abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Unordered(b'+'),
                last_blankline: false,
            },
            "+",
            1
        );
        test_block!(
            "* abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Unordered(b'*'),
                last_blankline: false,
            },
            "*",
            1
        );
    }

    #[test]
    fn block_list_task() {
        test_block!(
            "- [ ] abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Task,
                last_blankline: false,
            },
            "- [ ]",
            1
        );
        test_block!(
            "+ [x] abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Task,
                last_blankline: false,
            },
            "+ [x]",
            1
        );
        test_block!(
            "* [X] abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Task,
                last_blankline: false,
            },
            "* [X]",
            1
        );
    }

    #[test]
    fn block_list_ordered() {
        test_block!(
            "123. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(Decimal, Period),
                last_blankline: false,
            },
            "123.",
            1
        );
        test_block!(
            "i. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(RomanLower, Period),
                last_blankline: false,
            },
            "i.",
            1
        );
        test_block!(
            "I. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(RomanUpper, Period),
                last_blankline: false,
            },
            "I.",
            1
        );
        test_block!(
            "IJ. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(AlphaUpper, Period),
                last_blankline: false,
            },
            "IJ.",
            1
        );
        test_block!(
            "(a) abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(AlphaLower, ParenParen),
                last_blankline: false,
            },
            "(a)",
            1
        );
        test_block!(
            "a) abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(AlphaLower, Paren),
                last_blankline: false,
            },
            "a)",
            1
        );
    }
}
