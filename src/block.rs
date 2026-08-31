use crate::Alignment;
use crate::OrderedListNumbering::AlphaLower;
use crate::OrderedListNumbering::AlphaUpper;
use crate::OrderedListNumbering::Decimal;
use crate::OrderedListNumbering::RomanLower;
use crate::OrderedListNumbering::RomanUpper;
use crate::OrderedListStyle::Paren;
use crate::OrderedListStyle::ParenParen;
use crate::OrderedListStyle::Period;

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
    Document,
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
                value: AlphaLower.parse_number(single_digit).unwrap(),
            }),
            _ => None,
        }
    }
}

impl ListType {
    fn can_follow(self, start: Self) -> bool {
        start == self
            || if let (Ordered(n0, s0), Ordered(n1, s1)) = (start, self) {
                s0 == s1
                    && (n0.numbering == n1.numbering
                        || n1
                            .ambiguity()
                            .is_some_and(|na1| n0.numbering == na1.numbering))
            } else {
                false
            }
    }
}

#[derive(Debug)]
struct OpenList {
    /// Type of the list, an initial guess is made but may change if ambiguous.
    ty_start: ListType,
    ty_locked: bool,
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
        self.enter(Node::Container(Document), 0..0);

        let mut lines = lines(self.src).collect::<Vec<_>>();
        let mut line_pos = 0;
        while let Some(line_count) = self.parse_block(&mut lines[line_pos..], true) {
            line_pos += line_count;
        }
        while let Some(l) = self.open_lists.pop() {
            self.close_list(&l, self.src.len());
        }

        for _ in std::mem::take(&mut self.open_sections).drain(..) {
            self.exit(self.src.len()..self.src.len());
        }

        self.exit(self.src.len()..self.src.len()); // Document
        debug_assert_eq!(self.open, &[]);

        #[cfg(feature = "log")]
        for e in &self.events {
            log::trace!(
                "emit {:?} {:?} {:?}",
                e.kind,
                &self.src[e.span.clone()],
                e.span
            );
        }

        self.events
    }

    fn inline(&mut self, span: std::ops::Range<usize>) {
        if self.open.last().is_none_or(|i| {
            !matches!(
                self.events[*i].kind,
                EventKind::Enter(Node::Leaf(CodeBlock { .. }))
            )
        }) {
            debug_assert_eq!(
                &self.src[span.clone()],
                &self.src[self.trim_start(span.clone())],
            );
        }
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
        let EventKind::Enter(node) = self.events[self.open.pop().unwrap()].kind else {
            panic!("{:?}", self.events[self.open.pop().unwrap()].kind);
        };
        self.events.push(Event {
            kind: EventKind::Exit(node),
            span,
        });
        i
    }

    /// Recursively parse a block and all of its children. Return number of lines the block uses.
    fn parse_block(&mut self, lines: &mut [Line], top_level: bool) -> Option<usize> {
        let MeteredBlock {
            kind,
            span: span_start,
            line_count,
        } = MeteredBlock::new(
            lines
                .iter()
                .map(|l| (l.current_indent(), &self.src[l.span()])),
        )?;

        #[cfg(feature = "log")]
        log::trace!(
            "parse {kind:?} {line_count} line(s) {:?}",
            &self.src[lines[0].span()]
        );

        let lines = &mut lines[..line_count];
        let span_start = (span_start.start + lines[0].start())..(span_start.end + lines[0].start());

        // ignore trailing blanklines if any
        let (lines, line_count) = if matches!(
            kind,
            Kind::Table {
                caption: false,
                blankline: true,
            } | Kind::Definition {
                last_blankline: true,
                ..
            } | Kind::ListItem {
                last_blankline: true,
                ..
            }
        ) {
            let lc = line_count
                - lines
                    .iter()
                    .rev()
                    .take_while(|l| self.trim((l.span()).clone()).is_empty())
                    .count();
            (&mut lines[..lc], lc)
        } else {
            (lines, line_count)
        };

        let end_line = lines[lines.len() - 1].span();
        let span_end = match kind {
            Kind::Fenced {
                has_closing_fence: true,
                ..
            } => end_line,
            _ => end_line.end..end_line.end,
        };

        // part of first inline that is from the outer block
        let outer_len = span_start.end - lines[0].start();

        // skip outer block part for inner content
        lines[0].indent(outer_len);
        match kind {
            Kind::Blockquote
                if lines[0].start() < lines[0].end()
                    && self.src.as_bytes()[lines[0].start()].is_ascii_whitespace()
                    && self.src.as_bytes()[lines[0].start()] != b'\n' =>
            {
                lines[0].indent(1);
            }
            Kind::Heading { level, .. } => {
                for line in lines.iter_mut().skip(1) {
                    let l = &self.src.as_bytes()[line.span()];
                    let l = &l[l.iter().take_while(|c| c.is_ascii_whitespace()).count()..];
                    let hash = l.iter().take_while(|c| **c == b'#').count();
                    let l = &l[hash..];
                    let post_ws = l.iter().take_while(|c| c.is_ascii_whitespace()).count();
                    let l = &l[post_ws..];
                    if post_ws > 0 {
                        debug_assert_eq!(level, hash);
                        line.indent(line.span().len() - l.len());
                    }
                }
            }
            _ => {}
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
            ty_locked,
            depth,
            ..
        }) = self.open_lists.last_mut()
        {
            debug_assert!(usize::from(*depth) <= self.open.len());
            if self.open.len() == (*depth).into() {
                let continues = if let Kind::ListItem { ty: ty_new, .. } = kind {
                    let num_changed = !*ty_locked && {
                        fn changed_numbering(
                            n0: ListNumber,
                            s0: crate::OrderedListStyle,
                            ty_new: ListType,
                        ) -> Option<ListNumber> {
                            let ListType::Ordered(n1, s1) = ty_new else {
                                return None;
                            };

                            if s0 != s1 {
                                return None;
                            }

                            let na0 = n0.ambiguity()?;
                            (na0.numbering == n1.numbering && na0.value + 1 == n1.value)
                                .then_some(na0)
                        }

                        let ListType::Ordered(n0, s0) = ty_start else {
                            unreachable!("only ordered list set to unlocked")
                        };
                        if let Some(num) = changed_numbering(*n0, *s0, ty_new) {
                            *n0 = num;
                            true
                        } else {
                            false
                        }
                    };
                    *ty_locked = true;

                    num_changed || ty_new.can_follow(*ty_start)
                } else {
                    matches!(kind, Kind::Atom(Blankline))
                };
                if !continues {
                    let l = self.open_lists.pop().unwrap();
                    self.close_list(&l, span_start.start);
                }
            }
        }

        // set list to loose if blankline discovered
        if matches!(kind, Kind::Atom(Atom::Blankline)) {
            self.prev_blankline = !self
                .events
                .iter()
                .rev()
                .find(|e| !matches!(e.kind, EventKind::Exit(Node::Container(ListItem(..)))))
                .is_some_and(|e| matches!(e.kind, EventKind::Exit(Node::Container(List { .. }))));
        } else if !matches!(kind, Kind::Atom(Atom::Attributes)) {
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
                    checked: !self.src.as_bytes()[span_start.start + 3].is_ascii_whitespace(),
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
        } else {
            self.attr_start = None;
        }

        debug_assert_ne!(line_count, 0);

        Some(line_count)
    }

    fn parse_leaf(
        &mut self,
        leaf: Leaf<'s>,
        k: &Kind,
        span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
        mut lines: &mut [Line],
    ) {
        if let Kind::Fenced { indent, .. } = k {
            for l in lines.iter_mut() {
                let indent_line = self.src.as_bytes()[l.span()]
                    .iter()
                    .take_while(|c| *c != &b'\n' && c.is_ascii_whitespace())
                    .count();
                l.indent((*indent).min(indent_line));
            }
        } else {
            // trim starting whitespace of each inline
            for l in lines.iter_mut() {
                l.trim_start(self.src);
            }

            // skip first inline if empty
            if lines.first().is_some_and(|l| l.is_empty()) {
                lines = &mut lines[1..];
            }

            if matches!(leaf, LinkDefinition { .. }) {
                // trim ending whitespace of each inline
                for l in lines.iter_mut() {
                    l.trim_end(self.src);
                }
            }

            if matches!(leaf, Heading { .. }) {
                // strip trailing blank lines
                let lc = lines.len()
                    - lines
                        .iter()
                        .rev()
                        .take_while(|l| self.trim((l.span()).clone()).is_empty())
                        .count();
                lines = &mut lines[..lc];
            }

            // trim ending whitespace of block
            let l = lines.len();
            if l > 0 {
                lines[l - 1].trim_end(self.src);
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
                    let EventKind::Enter(node) = self.events[self.open.pop().unwrap()].kind else {
                        panic!("{:?}", self.events[self.open.pop().unwrap()].kind);
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
        }

        self.enter(Node::Leaf(leaf), span_start);
        lines
            .iter()
            .filter(|l| !l.is_empty())
            .for_each(|l| self.inline(l.span()));
        self.exit(span_end);
    }

    fn parse_container(
        &mut self,
        c: Container<'s>,
        k: &Kind,
        mut span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
        outer_len: usize,
        lines: &mut [Line],
    ) {
        // update spans, remove indentation / container prefix
        lines.iter_mut().skip(1).for_each(|l| {
            let src = &self.src[l.span()];
            let src_t = &self.src[self.trim(l.span())];
            let whitespace = src_t.as_ptr() as usize - src.as_ptr() as usize;
            let skip = match k {
                Kind::Blockquote => {
                    if src_t == ">"
                        || (src_t.starts_with('>')
                            && src_t[1..].starts_with(|c: char| c.is_ascii_whitespace()))
                    {
                        whitespace + 2
                    } else {
                        0
                    }
                }
                Kind::ListItem { .. } | Kind::Definition { .. } => whitespace.min(outer_len),
                Kind::Fenced { indent, .. } => whitespace.min(*indent),
                _ => panic!("non-container {k:?}"),
            };
            let len = self.src.as_bytes()[l.span()]
                .iter()
                .take_while(|c| **c != b'\n')
                .count();
            l.indent(skip.min(len));
        });

        if let Kind::ListItem { ty, .. } = k {
            let same_depth = self
                .open_lists
                .last()
                .is_none_or(|OpenList { depth, .. }| usize::from(*depth) < self.open.len());
            if same_depth {
                let tight = true;
                let event = self.enter(
                    Node::Container(Container::List { ty: *ty, tight }),
                    span_start.start..span_start.start,
                );
                self.open_lists.push(OpenList {
                    ty_start: *ty,
                    ty_locked: !matches!(*ty, ListType::Ordered(..)),
                    depth: self.open.len().try_into().unwrap(),
                    event,
                });
            }
        }

        let dt = if let ListItem(ListItemKind::Description) = c {
            let dt = self.enter(Node::Leaf(DescriptionTerm), span_start.clone());
            let start = self.trim_end(span_start.clone()).end;
            self.exit(start..start);
            span_start = lines[0].start()..lines[0].start();
            Some((dt, self.open.len()))
        } else {
            None
        };

        self.enter(Node::Container(c), span_start);
        let mut l = 0;
        while let Some(line_count) = self.parse_block(&mut lines[l..], false) {
            l += line_count;
        }

        if let Some((empty_term_enter, open_detail)) = dt {
            let (term_enter, term_exit) = if let Some((enter, exit)) = self.events
                [self.open[open_detail] + 1..]
                .iter()
                .take_while(|e| {
                    matches!(
                        e.kind,
                        EventKind::Atom(Blankline) | EventKind::Enter(Node::Leaf(Paragraph))
                    )
                })
                .position(|e| matches!(e.kind, EventKind::Enter(Node::Leaf(Paragraph))))
                .map(|i| self.open[open_detail] + 1 + i)
                .map(|enter| {
                    (
                        enter,
                        enter
                            + 1
                            + self.events[enter + 1..]
                                .iter_mut()
                                .position(|e| {
                                    matches!(e.kind, EventKind::Exit(Node::Leaf(Paragraph)))
                                })
                                .unwrap(),
                    )
                }) {
                // turn empty term + para into a term
                self.events[enter].kind = EventKind::Stale;
                if let EventKind::Exit(Node::Leaf(l)) = &mut self.events[exit].kind {
                    debug_assert_eq!(*l, Paragraph);
                    *l = DescriptionTerm;
                } else {
                    panic!("{:?}", self.events[exit].kind);
                }
                debug_assert_eq!(
                    self.events[empty_term_enter + 1].kind,
                    EventKind::Exit(Node::Leaf(DescriptionTerm)),
                );
                self.events[empty_term_enter + 1].kind = EventKind::Stale;
                (enter, exit)
            } else {
                (empty_term_enter, empty_term_enter + 1)
            };
            let has_term = term_enter + 1 < term_exit;

            let first_detail = {
                let start = term_exit.max(self.open[open_detail]) + 1;
                self.events[start..]
                    .iter()
                    .position(|e| !matches!(e.kind, EventKind::Atom(Blankline)))
                    .map_or(self.events.len(), |i| start + i)
            };

            let has_detail = first_detail != self.events.len();
            if has_term || !has_detail {
                // move out term before detail
                let detail_pos = self
                    .events
                    .get(first_detail)
                    .map_or_else(|| self.events.last().unwrap().span.end, |e| e.span.start);
                debug_assert_eq!(
                    self.events[self.open[open_detail]].kind,
                    EventKind::Enter(Node::Container(c)),
                );
                for (i, j) in (self.open[open_detail] + 1..first_detail).enumerate() {
                    self.events.swap(self.open[open_detail] + i, j);
                }
                self.events[first_detail - 1].span = detail_pos..detail_pos;
                self.open[open_detail] = first_detail - 1;
            }

            // move any blanklines directly after enter detail before enter detail
            let leading_blanklines = self.events[self.open[open_detail] + 1..]
                .iter()
                .take_while(|e| matches!(e.kind, EventKind::Atom(Blankline)))
                .count();
            if leading_blanklines > 0 {
                let pos = self.events[self.open[open_detail] + leading_blanklines]
                    .span
                    .end;
                for (i, j) in (self.open[open_detail] + 1
                    ..=self.open[open_detail] + leading_blanklines)
                    .enumerate()
                {
                    self.events.swap(self.open[open_detail] + i, j);
                }
                self.open[open_detail] += leading_blanklines;
                self.events[self.open[open_detail]].span = pos..pos;
            }

            // move blankline into empty term
            if !has_term && matches!(self.events[term_exit + 1].kind, EventKind::Atom(Blankline)) {
                let pos = self.events[term_exit + 1].span.end;
                self.events.swap(term_exit, term_exit + 1);
                self.events[term_exit + 1].span = pos..pos;
            }
        }

        if let Some(OpenList { depth, .. }) = self.open_lists.last() {
            debug_assert!(usize::from(*depth) <= self.open.len());
            if self.open.len() == (*depth).into() {
                self.prev_blankline = false;
                self.prev_loose = false;
                let l = self.open_lists.pop().unwrap();
                self.close_list(&l, span_end.start);
            }
        }

        self.exit(span_end);
    }

    fn parse_table(
        &mut self,
        lines: &mut [Line],
        span_start: std::ops::Range<usize>,
        span_end: std::ops::Range<usize>,
    ) {
        self.alignments.clear();
        self.enter(Node::Container(Table), span_start.clone());

        let caption_line = lines
            .iter()
            .position(|l| self.src[self.trim_start(l.span())].starts_with('^'))
            .map_or(lines.len(), |caption_line| {
                self.enter(Node::Leaf(Caption), span_start.clone());
                lines[caption_line].trim_start(self.src);
                lines[caption_line].indent(2);
                lines[lines.len() - 1].trim_end(self.src);
                for l in &lines[caption_line..] {
                    self.inline(self.trim_start(l.span()));
                }
                self.exit(span_end.clone());
                caption_line
            });

        let mut last_row_event = None;
        for l in &lines[..caption_line] {
            let row = self.trim(l.span());
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
            let mut last_escape = false;
            let mut last_escaped_nbsp = false;
            while let Some(lex::Token { kind, len }) = lex.next() {
                if let Some(l) = verbatim {
                    if matches!(kind, lex::Kind::Seq(lex::Sequence::Backtick)) && len == l {
                        lex.verbatim = false;
                        verbatim = None;
                    }
                } else {
                    match kind {
                        lex::Kind::Sym(lex::Symbol::Pipe) => {
                            let span = cell_start..pos;
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
                            let span_t = self.trim(span.clone());
                            let span_t = span_t.start..span_t.end + usize::from(last_escaped_nbsp);
                            if last_escaped_nbsp {
                                debug_assert!(self.src[span_t.clone()]
                                    .ends_with(|c: char| c.is_ascii_whitespace()));
                            }
                            self.inline(span_t);
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
                    if !(matches!(kind, lex::Kind::Text) && self.trim(pos..pos + len).is_empty()) {
                        last_escaped_nbsp = last_escape && matches!(kind, lex::Kind::Nbsp);
                        last_escape = matches!(kind, lex::Kind::Escape);
                    }
                }
                pos += len;
            }

            debug_assert!(verbatim.is_none());

            if separator_row {
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
                        panic!("{:?}", event.kind);
                    }
                    let event: &mut Event = &mut self.events[head_row_exit];
                    if let EventKind::Exit(Node::Container(TableRow { head })) = &mut event.kind {
                        *head = true;
                    } else {
                        panic!("{:?}", event.kind);
                    }
                }
            } else {
                let row_event_exit = self.exit(pos..pos); // table row
                last_row_event = Some((row_event_enter, row_event_exit));
            }
        }

        self.exit(span_end);
    }

    fn close_list(&mut self, list: &OpenList, pos: usize) {
        if let EventKind::Enter(Node::Container(List { ty, tight })) =
            &mut self.events[list.event].kind
        {
            if self.prev_loose {
                // ignore blankline at end
                *tight = true;
            }
            *ty = list.ty_start;
        } else {
            panic!("{:?}", self.events[list.event].kind);
        }

        let EventKind::Enter(node) = self.events[self.open.pop().unwrap()].kind else {
            panic!("{:?}", self.events[self.open.pop().unwrap()].kind);
        };

        let trailing_blanklines = self
            .events
            .iter()
            .rev()
            .take_while(|e| matches!(e.kind, EventKind::Atom(Blankline)))
            .count();
        let pos = if trailing_blanklines > 0 {
            self.events[self.events.len() - trailing_blanklines]
                .span
                .start
        } else {
            pos
        };

        self.events.insert(
            self.events.len() - trailing_blanklines,
            Event {
                kind: EventKind::Exit(node),
                span: pos..pos,
            },
        );
    }

    fn trim_start(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        let end = sp.end;
        let s = self.src[sp].trim_start_matches(|c: char| c.is_ascii_whitespace());
        (s.as_ptr() as usize - self.src.as_ptr() as usize)..end
    }

    fn trim_end(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        let start = sp.start;
        let s = self.src[sp].trim_end_matches(|c: char| c.is_ascii_whitespace());
        start..(s.as_ptr() as usize + s.len() - self.src.as_ptr() as usize)
    }

    fn trim(&self, sp: std::ops::Range<usize>) -> std::ops::Range<usize> {
        self.trim_end(self.trim_start(sp))
    }
}

/// Parser for a single block.
#[derive(Debug)]
struct MeteredBlock<'s> {
    kind: Kind<'s>,
    span: std::ops::Range<usize>,
    line_count: usize,
}

impl<'s> MeteredBlock<'s> {
    /// Identify and measure the line length of a single block.
    fn new<I: Iterator<Item = (usize, &'s str)>>(mut lines: I) -> Option<Self> {
        lines.next().map(|(indent, l)| {
            let IdentifiedBlock { mut kind, span } = IdentifiedBlock::new(indent, l);
            let line_count = 1 + lines
                .take_while(|(indent, l)| kind.continues(*indent, l))
                .count();
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
        indent_abs: usize,
        footnote: bool,
        label: &'s str,
        last_blankline: bool,
    },
    Blockquote,
    ListItem {
        indent_abs: usize,
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

fn has_unclosed_verbatim(s: &str) -> bool {
    if !s.contains('`') {
        return false;
    }
    let mut lex = lex::Lexer::new(s.as_bytes());
    let mut verbatim = None;
    while let Some(lex::Token { kind, len }) = lex.next() {
        if let Some(l) = verbatim {
            if matches!(kind, lex::Kind::Seq(lex::Sequence::Backtick)) && len == l {
                lex.verbatim = false;
                verbatim = None;
            }
        } else if let lex::Kind::Seq(lex::Sequence::Backtick) = kind {
            lex.verbatim = true;
            verbatim = Some(len);
        }
    }
    verbatim.is_some()
}

impl<'s> IdentifiedBlock<'s> {
    fn new(line_indent: usize, line: &'s str) -> Self {
        let l = line.len();

        let line = line.trim_start_matches(|c: char| c.is_ascii_whitespace() && c != '\n');
        let indent = l - line.len();
        let indent_abs = line_indent + indent;
        let line_t = line.trim_end_matches(|c: char| c.is_ascii_whitespace());

        let l = line.len();
        let lt = line_t.len();
        let mut chars = line.chars();

        let Some(first) = chars.next() else {
            return Self {
                kind: Kind::Atom(Blankline),
                span: indent..indent,
            };
        };

        match first {
            '\n' => Some((Kind::Atom(Blankline), indent..(indent + 1))),
            '#' => chars
                .find(|c| *c != '#')
                .is_none_or(|c| c.is_ascii_whitespace())
                .then(|| {
                    let level = line.bytes().take_while(|c| *c == b'#').count();
                    (Kind::Heading { level }, indent..(indent + level))
                }),
            '>' => {
                if chars.next().is_none_or(|c| c.is_ascii_whitespace()) {
                    Some((Kind::Blockquote, indent..(indent + 1)))
                } else {
                    None
                }
            }
            '{' => {
                (attr::valid(line) == lt).then(|| (Kind::Atom(Attributes), indent..(indent + l)))
            }
            '|' => {
                if lt >= 2
                    && line_t.ends_with('|')
                    && !line_t.ends_with("\\|")
                    && !has_unclosed_verbatim(line_t)
                {
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
            '[' => chars.as_str().find(']').and_then(|l| {
                if chars.as_str().as_bytes().get(l + 1) == Some(&b':')
                    && chars
                        .as_str()
                        .as_bytes()
                        .get(l + 2)
                        .is_none_or(|c| c.is_ascii_whitespace())
                {
                    let label = &chars.as_str()[0..l];
                    let footnote = label.starts_with('^');
                    let content =
                        &chars.as_str()[l + 2..].trim_matches(|c: char| c.is_ascii_whitespace());
                    (footnote || !content.contains(|c: char| c.is_ascii_whitespace())).then_some((
                        Kind::Definition {
                            indent_abs,
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
            b @ ('-' | '*' | '+') => {
                chars
                    .next()
                    .is_none_or(|c| c.is_ascii_whitespace())
                    .then(|| {
                        let task_list = chars.next() == Some('[')
                            && chars
                                .next()
                                .is_some_and(|c| c.is_ascii_whitespace() || matches!(c, 'x' | 'X'))
                            && chars.next() == Some(']')
                            && chars.next().is_none_or(|c| c.is_ascii_whitespace());
                        if task_list {
                            (
                                Kind::ListItem {
                                    indent_abs,
                                    ty: Task(b as u8),
                                    last_blankline: false,
                                },
                                indent..(indent + 5),
                            )
                        } else {
                            (
                                Kind::ListItem {
                                    indent_abs,
                                    ty: Unordered(b as u8),
                                    last_blankline: false,
                                },
                                indent..(indent + 1),
                            )
                        }
                    })
            }
            ':' if chars.clone().next().is_none_or(|c| c.is_ascii_whitespace()) => Some((
                Kind::ListItem {
                    indent_abs,
                    ty: Description,
                    last_blankline: false,
                },
                indent..(indent + 1),
            )),
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
                        indent_abs,
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

        let chars_num = chars.clone();
        let len_num = 1 + chars_num
            .clone()
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

        if chars.next().is_none_or(|c| c.is_ascii_whitespace()) {
            let len = len_num + len_style;
            Some((
                ListNumber {
                    numbering,
                    value: numbering.parse_number(style.number(&line[..len]))?,
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
    fn continues(&mut self, line_indent: usize, line: &'s str) -> bool {
        match self {
            Self::Atom(..)
            | Self::Fenced {
                has_closing_fence: true,
                ..
            } => false,
            Self::Blockquote => matches!(
                IdentifiedBlock::new(line_indent, line).kind,
                Self::Blockquote | Self::Paragraph
            ),
            Self::Heading { level } => {
                let next = IdentifiedBlock::new(line_indent, line).kind;
                matches!(next, Self::Paragraph)
                    || matches!(next, Self::Heading { level: l } if l == *level )
            }
            Self::Paragraph | Self::Table { caption: true, .. } => !line
                .trim_matches(|c: char| c.is_ascii_whitespace())
                .is_empty(),
            Self::ListItem {
                indent_abs,
                last_blankline,
                ..
            }
            | Self::Definition {
                indent_abs,
                footnote: true,
                last_blankline,
                ..
            } => {
                let line_t = line.trim_start_matches(|c: char| c.is_ascii_whitespace());
                let whitespace = line.len() - line_t.len();
                let next = IdentifiedBlock::new(line_indent, line).kind;
                let para = !*last_blankline && matches!(next, Self::Paragraph);
                let blankline = matches!(next, Self::Atom(Blankline));
                let cont = blankline || (line_indent + whitespace) > *indent_abs || para;
                if cont {
                    *last_blankline = blankline;
                }
                cont
            }
            Self::Definition {
                indent_abs,
                footnote: false,
                ..
            } => {
                let line_t = line.trim_start_matches(|c: char| c.is_ascii_whitespace());
                let whitespace = line.len() - line_t.len();
                let blankline = line
                    .trim_matches(|c: char| c.is_ascii_whitespace())
                    .is_empty();
                let inner_whitespace = line_t
                    .trim_end_matches(|c: char| c.is_ascii_whitespace())
                    .contains(|c: char| c.is_ascii_whitespace());
                (line_indent + whitespace) > *indent_abs && !blankline && !inner_whitespace
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
                } = IdentifiedBlock::new(line_indent, line).kind
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
                        && line_t.starts_with('|')
                        && line_t.len() >= 2
                        && line_t.ends_with('|')
                        && !line_t.ends_with("\\|")
                        && !has_unclosed_verbatim(line_t)
                }
            }
        }
    }
}

mod line {
    pub struct Line {
        indent: usize,
        span: std::ops::Range<usize>,
    }

    impl Line {
        pub fn new(span: std::ops::Range<usize>) -> Self {
            Self { indent: 0, span }
        }

        pub fn current_indent(&self) -> usize {
            self.indent
        }

        pub fn span(&self) -> std::ops::Range<usize> {
            self.span.clone()
        }

        pub fn start(&self) -> usize {
            self.span.start
        }

        pub fn end(&self) -> usize {
            self.span.end
        }

        pub fn len(&self) -> usize {
            self.span.len()
        }

        pub fn is_empty(&self) -> bool {
            self.span.is_empty()
        }

        pub fn indent(&mut self, n: usize) {
            self.indent += n;
            self.span.start += n;
        }

        pub fn trim_start(&mut self, src: &str) {
            self.indent(
                self.span.len()
                    - src[self.span()]
                        .trim_start_matches(|c: char| c.is_ascii_whitespace())
                        .len(),
            );
        }

        pub fn trim_end(&mut self, src: &str) {
            self.span.end -= self.len()
                - src[self.span()]
                    .trim_end_matches(|c: char| c.is_ascii_whitespace())
                    .len();
        }
    }
}

use line::Line;

/// Similar to `std::str::split('\n')` but newline is included and spans are used instead of `str`.
fn lines(src: &str) -> impl Iterator<Item = Line> + '_ {
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
                Some(Line::new(start..end))
            }
        }
    })
}

#[cfg(test)]
#[path = "test_block.rs"]
mod test;
