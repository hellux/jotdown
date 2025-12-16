use crate::Alignment;
use crate::OrderedListNumbering::*;
use crate::OrderedListStyle::*;

use crate::attr;
use crate::lex;

use Atom::*;
use Container::*;
use Leaf::*;
use ListType::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event<'s> {
    pub kind: EventKind<'s>,
    pub span: std::ops::Range<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
pub fn parse(src: &str) -> Vec<Event<'_>> {
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
    List { ty: ListType, tight: bool },
    ListItem(ListItemKind),
    Footnote { label: &'s str },
    Table,
    TableRow { head: bool },
    Section { pos: u32 },
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
    Ordered(ListNumber, crate::OrderedListStyle),
    Task(u8),
    Description,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListNumber {
    pub numbering: crate::OrderedListNumbering,
    pub value: u64,
}

impl ListNumber {
    /// Return additional value that this number could represent, if any.
    fn ambiguity(self) -> Option<Self> {
        // assume roman if ambiguous (prioritized during parsing)
        match self.numbering {
            RomanLower | RomanUpper => match self.value {
                1 => Some("i"),
                5 => Some("v"),
                10 => Some("x"),
                50 => Some("l"),
                100 => Some("c"),
                500 => Some("d"),
                1000 => Some("m"),
                _ => None,
            }
            .map(|single_digit| ListNumber {
                numbering: if self.numbering == RomanLower {
                    AlphaLower
                } else {
                    AlphaUpper
                },
                value: AlphaLower.parse_number(single_digit),
            }),
            _ => None,
        }
    }
}

impl ListType {
    /// Whether this list item can be continued by the other list item.
    ///
    /// If so, return the two new resolved ListType objects. They only differ from the input in
    /// case of ambiguous types.
    fn continues(&self, other: &Self) -> Option<(Self, Self)> {
        match (self, other) {
            _ if self == other => Some((*self, *other)),
            (
                Ordered(ListNumber { numbering: n0, .. }, s0),
                Ordered(ListNumber { numbering: n1, .. }, s1),
            ) if n0 == n1 && s0 == s1 => Some((*self, *other)),
            (Ordered(n0, s0), Ordered(n1, s1)) if s0 == s1 => {
                if let Some(na0) = n0.ambiguity() {
                    if na0.numbering == n1.numbering && na0.value + 1 == n1.value {
                        Some((ListType::Ordered(na0, *s0), *other))
                    } else {
                        None
                    }
                } else if let Some(na1) = n1.ambiguity() {
                    if n0.numbering == na1.numbering && n0.value + 1 == na1.value {
                        Some((*self, ListType::Ordered(na1, *s1)))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[derive(Debug)]
struct OpenList {
    /// Type of the list, an initial guess is made but may change if ambiguous. Also used to
    /// determine whether this list should be continued or a new one should be created.
    ty_start: ListType,
    /// Type of the previous item, generally the same as ty_start but value may differ in ordered
    /// lists.
    ty_prev: ListType,
    /// Depth in the tree where the direct list items of the list are. Needed to determine when to
    /// close the list.
    depth: u16,
    /// Index to event in tree, required to update list type and tightness.
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
            self.exit(self.src.len()..self.src.len());
        }
        debug_assert_eq!(self.open, &[]);
        self.events
    }

    fn inline(&mut self, span: std::ops::Range<usize>) {
        self.events.push(Event {
            kind: EventKind::Inline,
            span,
        });
    }

    fn enter(&mut self, node: Node<'s>, span: std::ops::Range<usize>) -> usize {
        let i = self.events.len();
        self.open.push(i);
        self.events.push(Event {
            kind: EventKind::Enter(node),
            span,
        });
        i
    }

    fn exit(&mut self, span: std::ops::Range<usize>) -> usize {
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
    fn parse_block(&mut self, lines: &mut [std::ops::Range<usize>], top_level: bool) -> usize {
        if let Some(MeteredBlock {
            kind,
            span: span_start,
            line_count,
        }) = MeteredBlock::new(lines.iter().map(|sp| &self.src[sp.clone()]))
        {
            let lines = &mut lines[..line_count];
            let span_start = (span_start.start + lines[0].start)..(span_start.end + lines[0].start);

            // ignore trailing blanklines after tables if any
            let (lines, line_count) = if matches!(
                kind,
                Kind::Table {
                    caption: false,
                    blankline: true,
                }
            ) {
                let lc = line_count
                    - lines
                        .iter()
                        .rev()
                        .take_while(|l| {
                            self.src[(*l).clone()]
                                .trim_matches(|c: char| c.is_ascii_whitespace())
                                .is_empty()
                        })
                        .count();
                (&mut lines[..lc], lc)
            } else {
                (lines, line_count)
            };

            let end_line = lines[lines.len() - 1].clone();
            let span_end = match kind {
                Kind::Fenced {
                    has_closing_fence: true,
                    ..
                } => end_line,
                _ => end_line.end..end_line.end,
            };

            // part of first inline that is from the outer block
            let outer_len = span_start.end - lines[0].start;

            // skip outer block part for inner content
            lines[0].start += outer_len;
            if matches!(kind, Kind::Blockquote)
                && lines[0].start < lines[0].end
                && matches!(self.src.as_bytes()[lines[0].start], b'\t' | b' ')
            {
                lines[0].start += 1;
            }

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
            if let Some(OpenList {
                ty_start,
                ty_prev,
                depth,
                ..
            }) = self.open_lists.last_mut()
            {
                debug_assert!(usize::from(*depth) <= self.open.len());
                if self.open.len() == (*depth).into() {
                    let continues = if let Kind::ListItem { ty: ty_new, .. } = kind {
                        if let Some((ty_prev_res, ty_new_res)) = ty_prev.continues(&ty_new) {
                            if ty_start == ty_prev {
                                *ty_start = ty_prev_res;
                            }
                            *ty_prev = ty_new_res;
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    };
                    if !continues {
                        let l = self.open_lists.pop().unwrap();
                        self.close_list(l, span_start.start);
                    }
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
                            if let EventKind::Enter(Node::Container(List { tight, .. })) =
                                &mut self.events[*event].kind
                            {
                                if *tight {
                                    self.prev_loose = true;
                                    *tight = false;
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
                    pos: span_start.start as u32,
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
                    ListType::Task(..) => ListItemKind::Task {
                        checked: self.src.as_bytes()[span_start.start + 3] != b' ',
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
                    self.parse_container(c, &kind, span_start, span_end, outer_len, lines);
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
        span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
        mut lines: &mut [std::ops::Range<usize>],
    ) {
        if let Kind::Fenced { indent, spec, .. } = k {
            for line in lines.iter_mut() {
                let indent_line = self.src.as_bytes()[line.clone()]
                    .iter()
                    .take_while(|c| *c != &b'\n' && c.is_ascii_whitespace())
                    .count();
                line.start += (*indent).min(indent_line);
            }

            // trim ending whitespace of raw block
            if spec.starts_with('=') {
                let l = lines.len();
                if l > 0 {
                    lines[l - 1] = self.trim_end(lines[l - 1].clone());
                }
            }
        } else {
            // trim starting whitespace of each inline
            for line in lines.iter_mut() {
                *line = self.trim_start(line.clone());
            }

            // skip first inline if empty
            if lines.first().map_or(false, |l| l.is_empty()) {
                lines = &mut lines[1..];
            };

            if matches!(leaf, LinkDefinition { .. }) {
                // trim ending whitespace of each inline
                for line in lines.iter_mut() {
                    *line = self.trim_end(line.clone());
                }
            }

            // trim ending whitespace of block
            let l = lines.len();
            if l > 0 {
                lines[l - 1] = self.trim_end(lines[l - 1].clone());
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
                let pos = span_start.start as u32;
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
                        .map_or(span_start.start, |a| self.events[a].span.start);
                    self.events.insert(
                        self.attr_start.map_or(self.events.len(), |a| a + i),
                        Event {
                            kind: EventKind::Exit(node),
                            span: end..end,
                        },
                    );
                }
                self.open_sections.drain(first_close..);
                self.open_sections.push(*level);
                self.enter(
                    Node::Container(Section { pos }),
                    span_start.start..span_start.start,
                );
            }

            // trim '#' characters
            for line in lines.iter_mut().skip(1) {
                let start = line.start
                    + self.src.as_bytes()[line.clone()]
                        .iter()
                        .take_while(|c| **c == b'#' || c.is_ascii_whitespace())
                        .count();
                line.start = start;
            }
        }

        self.enter(Node::Leaf(leaf), span_start);
        lines
            .iter()
            .filter(|l| !matches!(k, Kind::Heading { .. }) || !l.is_empty())
            .for_each(|line| self.inline(line.clone()));
        self.exit(span_end);
    }

    fn parse_container(
        &mut self,
        c: Container<'s>,
        k: &Kind,
        mut span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
        outer_len: usize,
        lines: &mut [std::ops::Range<usize>],
    ) {
        // update spans, remove indentation / container prefix
        lines.iter_mut().skip(1).for_each(|sp| {
            let src = &self.src[sp.clone()];
            let src_t = src.trim_matches(|c: char| c.is_ascii_whitespace());
            let whitespace = src_t.as_ptr() as usize - src.as_ptr() as usize;
            let skip = match k {
                Kind::Blockquote => {
                    if src_t == ">" {
                        whitespace + 1
                    } else if src_t.starts_with('>')
                        && src_t[1..].starts_with(|c: char| c.is_ascii_whitespace())
                    {
                        whitespace + 1 + usize::from(src_t.len() > 1)
                    } else {
                        0
                    }
                }
                Kind::ListItem { .. } | Kind::Definition { .. } => whitespace.min(outer_len),
                Kind::Fenced { indent, .. } => whitespace.min(*indent),
                _ => panic!("non-container {:?}", k),
            };
            let len = self.src.as_bytes()[sp.clone()]
                .iter()
                .take_while(|c| **c != b'\n')
                .count();
            sp.start += skip.min(len);
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
                    Node::Container(Container::List { ty: *ty, tight }),
                    span_start.start..span_start.start,
                );
                self.open_lists.push(OpenList {
                    ty_start: *ty,
                    ty_prev: *ty,
                    depth: self.open.len().try_into().unwrap(),
                    event,
                });
            }
        }

        let dt = if let ListItem(ListItemKind::Description) = c {
            let dt = self.enter(Node::Leaf(DescriptionTerm), span_start.clone());
            let start = self.trim_end(span_start.clone()).end;
            self.exit(start..start);
            span_start = lines[0].start..lines[0].start;
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
                    self.events[enter_term].span = self.events[empty_term].span.clone();
                    let first_detail = self.events[exit_term + 1..]
                        .iter()
                        .position(|e| !matches!(e.kind, EventKind::Atom(Blankline)))
                        .map(|i| exit_term + 1 + i)
                        .unwrap_or(self.events.len());
                    let detail_pos = self
                        .events
                        .get(first_detail)
                        .map(|e| e.span.start)
                        .unwrap_or_else(|| self.events.last().unwrap().span.end);
                    for (i, j) in (enter_term..first_detail).enumerate() {
                        self.events[enter_detail + i] = self.events[j].clone();
                    }
                    self.events[first_detail - 1] = Event {
                        kind: EventKind::Enter(Node::Container(c)),
                        span: detail_pos..detail_pos,
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
                self.close_list(l, span_end.start);
            }
        }

        self.exit(span_end);
    }

    fn parse_table(
        &mut self,
        lines: &mut [std::ops::Range<usize>],
        span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
    ) {
        self.alignments.clear();
        self.enter(Node::Container(Table), span_start.clone());

        let caption_line = lines
            .iter()
            .position(|sp| {
                self.src[sp.clone()]
                    .trim_start_matches(|c: char| c.is_ascii_whitespace())
                    .starts_with('^')
            })
            .map_or(lines.len(), |caption_line| {
                self.enter(Node::Leaf(Caption), span_start.clone());
                lines[caption_line] = self.trim_start(lines[caption_line].clone());
                lines[caption_line].start += 2;
                lines[lines.len() - 1] = self.trim_end(lines[lines.len() - 1].clone());
                for line in &lines[caption_line..] {
                    self.inline(line.clone());
                }
                self.exit(span_end.clone());
                caption_line
            });

        let mut last_row_event = None;
        for row in &lines[..caption_line] {
            let row = self.trim(row.clone());
            if row.is_empty() {
                break;
            }
            let row_event_enter = self.enter(
                Node::Container(TableRow { head: false }),
                row.start..(row.start + 1),
            );
            let rem = (row.start + 1)..row.end; // |
            let mut lex = lex::Lexer::new(&self.src.as_bytes()[rem.clone()]);
            let mut pos = rem.start;
            let mut cell_start = pos;
            let mut separator_row = true;
            let mut verbatim = None;
            let mut column_index = 0;
            while let Some(lex::Token { kind, len }) = lex.next() {
                if let Some(l) = verbatim {
                    if matches!(kind, lex::Kind::Seq(lex::Sequence::Backtick)) && len == l {
                        lex.verbatim = false;
                        verbatim = None;
                    }
                } else {
                    match kind {
                        lex::Kind::Sym(lex::Symbol::Pipe) => {
                            let span = self.trim(cell_start..pos);
                            let cell = &self.src[span.clone()];
                            let separator_cell = match cell.len() {
                                0 => false,
                                1 => cell == "-",
                                2 => matches!(cell, ":-" | "--" | "-:"),
                                l => {
                                    matches!(cell.as_bytes()[0], b'-' | b':')
                                        && matches!(cell.as_bytes()[l - 1], b'-' | b':')
                                        && cell.bytes().skip(1).take(l - 2).all(|c| c == b'-')
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
                                cell_start..cell_start,
                            );
                            self.inline(span);
                            self.exit(pos..(pos + 1));
                            cell_start = pos + len;
                            column_index += 1;
                        }
                        lex::Kind::Seq(lex::Sequence::Backtick) => {
                            lex.verbatim = true;
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
                            let cell = &self.src[e.span.clone()];
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
                let row_event_exit = self.exit(pos..pos); // table row
                last_row_event = Some((row_event_enter, row_event_exit));
            }
        }

        self.exit(span_end);
    }

    fn close_list(&mut self, list: OpenList, pos: usize) {
        if let EventKind::Enter(Node::Container(List { ty, tight })) =
            &mut self.events[list.event].kind
        {
            if self.prev_loose {
                // ignore blankline at end
                *tight = true;
            }
            *ty = list.ty_start;
        } else {
            panic!()
        }

        self.exit(pos..pos); // list
    }

    fn trim_start(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        let s = self.src[sp].trim_start_matches(|c: char| c.is_ascii_whitespace());
        (s.as_ptr() as usize - self.src.as_ptr() as usize)
            ..(s.as_ptr() as usize + s.len() - self.src.as_ptr() as usize)
    }

    fn trim_end(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        let s = self.src[sp].trim_end_matches(|c: char| c.is_ascii_whitespace());
        (s.as_ptr() as usize - self.src.as_ptr() as usize)
            ..(s.as_ptr() as usize + s.len() - self.src.as_ptr() as usize)
    }

    fn trim(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        self.trim_end(self.trim_start(sp))
    }
}

/// Parser for a single block.
struct MeteredBlock<'s> {
    kind: Kind<'s>,
    span: std::ops::Range<usize>,
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
        nested_raw: Option<(u8, usize)>,
    },
    Definition {
        indent: usize,
        footnote: bool,
        label: &'s str,
        last_blankline: bool,
    },
    Blockquote,
    ListItem {
        indent: usize,
        ty: ListType,
        last_blankline: bool,
    },
    Table {
        caption: bool,
        blankline: bool,
    },
}

struct IdentifiedBlock<'s> {
    kind: Kind<'s>,
    span: std::ops::Range<usize>,
}

impl<'s> IdentifiedBlock<'s> {
    fn new(line: &'s str) -> Self {
        let l = line.len();

        let line = line.trim_start_matches(|c: char| c.is_ascii_whitespace() && c != '\n');
        let indent = l - line.len();
        let line_t = line.trim_end_matches(|c: char| c.is_ascii_whitespace());

        let l = line.len();
        let lt = line_t.len();
        let mut chars = line.chars();

        let first = if let Some(c) = chars.next() {
            c
        } else {
            return Self {
                kind: Kind::Atom(Blankline),
                span: indent..indent,
            };
        };

        match first {
            '\n' => Some((Kind::Atom(Blankline), indent..(indent + 1))),
            '#' => chars
                .find(|c| *c != '#')
                .map_or(true, |c| c.is_ascii_whitespace())
                .then(|| {
                    let level = line.bytes().take_while(|c| *c == b'#').count();
                    (Kind::Heading { level }, indent..(indent + level))
                }),
            '>' => {
                if chars.next().map_or(true, |c| c.is_ascii_whitespace()) {
                    Some((Kind::Blockquote, indent..(indent + 1)))
                } else {
                    None
                }
            }
            '{' => {
                (attr::valid(line) == lt).then(|| (Kind::Atom(Attributes), indent..(indent + l)))
            }
            '|' => {
                if lt >= 2 && line_t.ends_with('|') && !line_t.ends_with("\\|") {
                    Some((
                        Kind::Table {
                            caption: false,
                            blankline: false,
                        },
                        indent..indent,
                    ))
                } else {
                    None
                }
            }
            '[' => chars.as_str().find("]").and_then(|l| {
                if chars.as_str()[l + 1..].starts_with(':') {
                    let label = &chars.as_str()[0..l];
                    let footnote = label.starts_with('^');
                    Some((
                        Kind::Definition {
                            indent,
                            footnote,
                            label: &label[usize::from(footnote)..],
                            last_blankline: false,
                        },
                        0..(indent + 3 + l),
                    ))
                } else {
                    None
                }
            }),
            '-' | '*' if Self::is_thematic_break(chars.clone()) => {
                Some((Kind::Atom(ThematicBreak), indent..(indent + lt)))
            }
            b @ ('-' | '*' | '+') => chars.next().map_or(true, |c| c == ' ').then(|| {
                let task_list = chars.next() == Some('[')
                    && matches!(chars.next(), Some('x' | 'X' | ' '))
                    && chars.next() == Some(']')
                    && chars.next().map_or(true, |c| c.is_ascii_whitespace());
                if task_list {
                    (
                        Kind::ListItem {
                            indent,
                            ty: Task(b as u8),
                            last_blankline: false,
                        },
                        indent..(indent + 5),
                    )
                } else {
                    (
                        Kind::ListItem {
                            indent,
                            ty: Unordered(b as u8),
                            last_blankline: false,
                        },
                        indent..(indent + 1),
                    )
                }
            }),
            ':' if chars
                .clone()
                .next()
                .map_or(true, |c| c.is_ascii_whitespace()) =>
            {
                Some((
                    Kind::ListItem {
                        indent,
                        ty: Description,
                        last_blankline: false,
                    },
                    indent..(indent + 1),
                ))
            }
            f @ ('`' | ':' | '~') => {
                let fence_length = 1 + (&mut chars).take_while(|c| *c == f).count();
                let spec =
                    &line_t[fence_length..].trim_start_matches(|c: char| c.is_ascii_whitespace());
                let valid_spec = if f == ':' {
                    spec.bytes().all(attr::is_name)
                } else {
                    !spec.bytes().any(|c| c.is_ascii_whitespace())
                        && !spec.bytes().any(|c| c == b'`')
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
                            nested_raw: None,
                        },
                        indent..(indent + line.len()),
                    )
                })
            }
            _ => Self::maybe_ordered_list_item(line).map(|(num, style, len)| {
                (
                    Kind::ListItem {
                        indent,
                        ty: Ordered(num, style),
                        last_blankline: false,
                    },
                    indent..(indent + len),
                )
            }),
        }
        .map(|(kind, span)| Self { kind, span })
        .unwrap_or(Self {
            kind: Kind::Paragraph,
            span: indent..indent,
        })
    }

    fn is_thematic_break(chars: std::str::Chars) -> bool {
        let mut n = 1;
        for c in chars {
            if matches!(c, '-' | '*') {
                n += 1;
            } else if !c.is_ascii_whitespace() {
                return false;
            }
        }
        n >= 3
    }

    fn maybe_ordered_list_item(line: &str) -> Option<(ListNumber, crate::OrderedListStyle, usize)> {
        fn is_roman_lower_digit(c: char) -> bool {
            matches!(c, 'i' | 'v' | 'x' | 'l' | 'c' | 'd' | 'm')
        }

        fn is_roman_upper_digit(c: char) -> bool {
            matches!(c, 'I' | 'V' | 'X' | 'L' | 'C' | 'D' | 'M')
        }

        let mut chars = line.chars();
        let mut first = chars.next().unwrap();

        let start_paren = first == '(';
        if start_paren {
            first = chars.next()?;
        }

        let numbering = if first.is_ascii_digit() {
            Decimal
        } else if is_roman_lower_digit(first) {
            // prioritize roman for now if ambiguous
            RomanLower
        } else if is_roman_upper_digit(first) {
            RomanUpper
        } else if first.is_ascii_lowercase() {
            AlphaLower
        } else if first.is_ascii_uppercase() {
            AlphaUpper
        } else {
            return None;
        };

        let max_len = match numbering {
            AlphaLower | AlphaUpper => 1,
            Decimal => 19,
            RomanLower | RomanUpper => 13,
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

        if chars.next().map_or(true, |c| c.is_ascii_whitespace()) {
            let len = len_num + len_style;
            Some((
                ListNumber {
                    numbering,
                    value: numbering.parse_number(style.number(&line[..len])),
                },
                style,
                len,
            ))
        } else {
            None
        }
    }
}

impl<'s> Kind<'s> {
    /// Determine if a line continues the block.
    fn continues(&mut self, line: &'s str) -> bool {
        match self {
            Self::Atom(..)
            | Self::Fenced {
                has_closing_fence: true,
                ..
            } => false,
            Self::Blockquote => matches!(
                IdentifiedBlock::new(line).kind,
                Self::Blockquote | Self::Paragraph
            ),
            Self::Heading { level } => {
                let next = IdentifiedBlock::new(line).kind;
                matches!(next, Self::Paragraph)
                    || matches!(next, Self::Heading { level: l } if l == *level )
            }
            Self::Paragraph | Self::Table { caption: true, .. } => !line
                .trim_matches(|c: char| c.is_ascii_whitespace())
                .is_empty(),
            Self::ListItem {
                indent,
                last_blankline,
                ..
            } => {
                let line_t = line.trim_start_matches(|c: char| c.is_ascii_whitespace());
                let whitespace = line.len() - line_t.len();
                let next = IdentifiedBlock::new(line).kind;
                let para = !*last_blankline && matches!(next, Self::Paragraph);
                *last_blankline = matches!(next, Self::Atom(Blankline));
                *last_blankline || whitespace > *indent || para
            }
            Self::Definition {
                indent,
                footnote: true,
                last_blankline,
                ..
            } => {
                let next = IdentifiedBlock::new(line).kind;
                let line_t = line.trim_start_matches(|c: char| c.is_ascii_whitespace());
                let whitespace = line.len() - line_t.len();
                let cont_para = !*last_blankline && matches!(next, Self::Paragraph);
                *last_blankline = matches!(next, Self::Atom(Blankline));
                whitespace > *indent || *last_blankline || cont_para
            }
            Self::Definition { .. } => {
                let blankline = line
                    .trim_matches(|c: char| c.is_ascii_whitespace())
                    .is_empty();
                line.starts_with(' ') && !blankline
            }
            Self::Fenced {
                fence_length,
                kind,
                has_closing_fence,
                nested_raw,
                ..
            } => {
                if let Kind::Fenced {
                    kind: k,
                    fence_length: l,
                    spec,
                    ..
                } = IdentifiedBlock::new(line).kind
                {
                    if let Some((c, nested_l)) = nested_raw {
                        if FenceKind::CodeBlock(*c) == k && l >= *nested_l && spec.is_empty() {
                            *nested_raw = None;
                        }
                    } else if k == *kind {
                        *has_closing_fence = l >= *fence_length && spec.is_empty();
                    } else if *kind == FenceKind::Div {
                        if let FenceKind::CodeBlock(c) = k {
                            *nested_raw = Some((c, l));
                        }
                    }
                }
                true
            }
            Self::Table { caption, blankline } => {
                let line_t = line.trim_matches(|c: char| c.is_ascii_whitespace());
                if line_t.is_empty() {
                    *blankline = true;
                    true
                } else if line_t.starts_with("^ ") {
                    *caption = true;
                    true
                } else {
                    !*blankline
                        && (line_t.starts_with('|')
                            && line_t.ends_with('|')
                            && !line_t.ends_with("\\|"))
                }
            }
        }
    }
}

/// Similar to `std::str::split('\n')` but newline is included and spans are used instead of `str`.
fn lines(src: &str) -> impl Iterator<Item = std::ops::Range<usize>> + '_ {
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
                Some(start..end)
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
    use super::ListNumber;
    use super::ListType::*;
    use super::Node::*;

    macro_rules! test_parse {
        ($src:expr $(,$($event:expr),* $(,)?)?) => {
            let t = super::TreeParser::new($src).parse();
            let actual = t.into_iter().map(|ev| (ev.kind, &$src[ev.span])).collect::<Vec<_>>();
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: false,
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
                    ty: Unordered(b'-'),
                    tight: false,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: false,
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
                    ty: Unordered(b'-'),
                    tight: false,
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'+'),
                    tight: true,
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
                    ty: Unordered(b'+'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Ordered(
                        ListNumber {
                            numbering: Decimal,
                            value: 1,
                        },
                        Period,
                    ),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
                })),
                "",
            ),
            (Enter(Leaf(Paragraph)), ""),
            (Inline, "c"),
            (Exit(Leaf(Paragraph)), ""),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Ordered(
                        ListNumber {
                            numbering: Decimal,
                            value: 1,
                        },
                        Period,
                    ),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'+'),
                    tight: true,
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
                    ty: Unordered(b'*'),
                    tight: true,
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
                    ty: Unordered(b'*'),
                    tight: true,
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Unordered(b'+'),
                    tight: true,
                })),
                "",
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'*'),
                    tight: true
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
                    ty: Unordered(b'*'),
                    tight: true
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'-'),
                    tight: true
                })),
                ""
            ),
            (
                Enter(Container(List {
                    ty: Unordered(b'+'),
                    tight: true
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
                    ty: Unordered(b'+'),
                    tight: true
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
                    ty: Description,
                    tight: true,
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
                    ty: Description,
                    tight: true,
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
                    ty: Description,
                    tight: false
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Unordered(b'-'),
                    tight: true
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
                    ty: Description,
                    tight: false
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
                    ty: Description,
                    tight: true,
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
                    ty: Description,
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
                })),
                ""
            ),
            (Enter(Container(ListItem(ListItemKind::List))), "-"),
            (
                Enter(Container(List {
                    ty: Unordered(b'-'),
                    tight: true,
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
                    ty: Unordered(b'-'),
                    tight: true,
                })),
                ""
            ),
            (Exit(Container(ListItem(ListItemKind::List))), ""),
            (
                Exit(Container(List {
                    ty: Unordered(b'-'),
                    tight: true,
                })),
                ""
            ),
        );
    }

    macro_rules! test_block {
        ($src:expr, $kind:expr, $str:expr, $len:expr $(,)?) => {
            let lines = super::lines($src).map(|sp| &$src[sp]);
            let mb = super::MeteredBlock::new(lines).unwrap();
            assert_eq!(
                (mb.kind, &$src[mb.span], mb.line_count),
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
                nested_raw: None,
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
                nested_raw: None,
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
                last_blankline: false,
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
                last_blankline: false,
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
                last_blankline: false,
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
                last_blankline: false,
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
                last_blankline: false,
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
                last_blankline: false,
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
                last_blankline: false,
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
                ty: Task(b'-'),
                last_blankline: false,
            },
            "- [ ]",
            1
        );
        test_block!(
            "+ [x] abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Task(b'+'),
                last_blankline: false,
            },
            "+ [x]",
            1
        );
        test_block!(
            "* [X] abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Task(b'*'),
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
                ty: Ordered(
                    ListNumber {
                        numbering: Decimal,
                        value: 123,
                    },
                    Period,
                ),
                last_blankline: false,
            },
            "123.",
            1
        );
        test_block!(
            "i. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(
                    ListNumber {
                        numbering: RomanLower,
                        value: 1
                    },
                    Period,
                ),
                last_blankline: false,
            },
            "i.",
            1
        );
        test_block!(
            "I. abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(
                    ListNumber {
                        numbering: RomanUpper,
                        value: 1,
                    },
                    Period,
                ),
                last_blankline: false,
            },
            "I.",
            1
        );
        test_block!(
            "(a) abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(
                    ListNumber {
                        numbering: AlphaLower,
                        value: 1,
                    },
                    ParenParen,
                ),
                last_blankline: false,
            },
            "(a)",
            1
        );
        test_block!(
            "a) abc\n",
            Kind::ListItem {
                indent: 0,
                ty: Ordered(
                    ListNumber {
                        numbering: AlphaLower,
                        value: 1,
                    },
                    Paren,
                ),
                last_blankline: false,
            },
            "a)",
            1
        );
    }
}
