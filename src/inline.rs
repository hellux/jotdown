use crate::attr;
use crate::lex;
use crate::CowStr;

use lex::Delimiter;
use lex::Sequence;
use lex::Symbol;

use Atom::*;
use Container::*;
use ControlFlow::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom<'s> {
    FootnoteReference { label: &'s str },
    Symbol(&'s str),
    Softbreak,
    Hardbreak,
    Escape,
    Nbsp,
    Ellipsis,
    EnDash,
    EmDash,
    Quote { ty: QuoteType, left: bool },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Container<'s> {
    Span,
    Subscript,
    Superscript,
    Insert,
    Delete,
    Emphasis,
    Strong,
    Mark,
    Verbatim,
    RawFormat { format: &'s str },
    InlineMath,
    DisplayMath,
    ReferenceLink(CowStrIndex),
    ReferenceImage(CowStrIndex),
    InlineLink(CowStrIndex),
    InlineImage(CowStrIndex),
    Autolink(&'s str),
}

type CowStrIndex = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuoteType {
    Single,
    Double,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventKind<'s> {
    Enter(Container<'s>),
    Exit(Container<'s>),
    Atom(Atom<'s>),
    Str,
    Empty, // dummy to hold attributes
    Attributes {
        container: bool,
        attrs: AttributesIndex,
    },
    Placeholder,
}

type AttributesIndex = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event<'s> {
    pub kind: EventKind<'s>,
    pub span: std::ops::Range<usize>,
}

#[derive(Clone)]
struct Input<'s> {
    src: &'s str,
    /// Lexer.
    lexer: lex::Lexer<'s>,
    /// The block is complete, the final line has been provided.
    complete: bool,
    /// Span of current line.
    span_line: std::ops::Range<usize>,
    /// Upcoming lines within the current block.
    ahead: std::collections::VecDeque<std::ops::Range<usize>>,
    /// Span of current event.
    span: std::ops::Range<usize>,
}

impl<'s> Input<'s> {
    fn new(src: &'s str) -> Self {
        Self {
            src,
            lexer: lex::Lexer::new(b""),
            complete: false,
            span_line: 0..0,
            ahead: std::collections::VecDeque::new(),
            span: 0..0,
        }
    }

    fn feed_line(&mut self, line: std::ops::Range<usize>, last: bool) {
        debug_assert!(!self.complete);
        self.complete = last;
        if self.lexer.ahead().is_empty() {
            if let Some(next) = self.ahead.pop_front() {
                self.set_current_line(next);
                self.ahead.push_back(line);
            } else {
                self.set_current_line(line);
            }
        } else {
            self.ahead.push_back(line);
        }
    }

    fn set_current_line(&mut self, line: std::ops::Range<usize>) {
        self.lexer = lex::Lexer::new(&self.src.as_bytes()[line.clone()]);
        self.span = line.start..line.start;
        self.span_line = line;
    }

    fn reset(&mut self) {
        self.lexer = lex::Lexer::new(b"");
        self.complete = false;
        self.ahead.clear();
    }

    fn last(&self) -> bool {
        self.complete && self.ahead.is_empty()
    }

    fn eat(&mut self) -> Option<lex::Token> {
        let tok = self.lexer.next();
        if let Some(t) = &tok {
            self.span.end += t.len;
        }
        tok
    }

    fn peek(&mut self) -> Option<&lex::Token> {
        self.lexer.peek()
    }

    fn reset_span(&mut self) {
        self.span.start = self.span.end;
    }

    fn ahead_raw_format(&mut self) -> Option<std::ops::Range<usize>> {
        if matches!(
            self.lexer.peek().map(|t| &t.kind),
            Some(lex::Kind::Open(Delimiter::BraceEqual))
        ) {
            let mut end = false;
            let len = self
                .lexer
                .ahead()
                .iter()
                .skip(2) // {=
                .take_while(|c| {
                    if **c == b'{' {
                        return false;
                    }
                    if **c == b'}' {
                        end = true;
                    }
                    !end && !c.is_ascii_whitespace()
                })
                .count();
            (len > 0 && end).then(|| {
                let tok = self.eat();
                debug_assert_eq!(
                    tok,
                    Some(lex::Token {
                        kind: lex::Kind::Open(Delimiter::BraceEqual),
                        len: 2,
                    })
                );
                self.lexer.skip_ahead(len + 1);
                self.span.end..(self.span.end + len)
            })
        } else {
            None
        }
    }
}

#[derive(Clone)]
struct VerbatimState {
    event_opener: usize,
    len_opener: u8,
    non_whitespace_encountered: bool,
    non_whitespace_last: Option<(lex::Kind, usize)>,
}

#[derive(Clone)]
struct AttributesState {
    elem_ty: AttributesElementType,
    end_attr: usize,
    valid_lines: usize,
    validator: attr::Validator,
}

#[derive(Clone)]
enum AttributesElementType {
    Container { e_placeholder: usize },
    Word,
}

#[derive(Clone)]
pub struct Parser<'s> {
    input: Input<'s>,
    /// Stack with kind and index of _potential_ openers for containers.
    openers: Vec<(Opener, usize)>,
    /// Buffer queue for next events. Events are buffered until no modifications due to future
    /// characters are needed.
    events: std::collections::VecDeque<Event<'s>>,
    /// State if inside a verbatim container.
    verbatim: Option<VerbatimState>,
    /// State if currently parsing potential attributes.
    attributes: Option<AttributesState>,
    /// Storage of cow strs, used to reduce size of [`Container`].
    pub(crate) store_cowstrs: Vec<CowStr<'s>>,
    /// Storage of attributes, used to reduce size of [`EventKind`].
    pub(crate) store_attributes: Vec<attr::Attributes<'s>>,
}

enum ControlFlow {
    /// At least one event has been emitted, continue parsing the line.
    Continue,
    /// Next line is needed to emit an event.
    Next,
    /// More lines are needed to emit an event. Unlike for the `Next` variant, the internal ahead
    /// buffer has already been examined, and more lines need to retrieved from the block parser.
    More,
    /// Parsing of the line is completed.
    Done,
}

impl<'s> Parser<'s> {
    pub fn new(src: &'s str) -> Self {
        Self {
            input: Input::new(src),
            openers: Vec::new(),
            events: std::collections::VecDeque::new(),
            verbatim: None,
            attributes: None,
            store_cowstrs: Vec::new(),
            store_attributes: Vec::new(),
        }
    }

    pub fn feed_line(&mut self, line: std::ops::Range<usize>, last: bool) {
        self.input.feed_line(line, last);
    }

    pub fn reset(&mut self) {
        debug_assert!(self.events.is_empty());
        self.input.reset();
        self.openers.clear();
        debug_assert!(self.attributes.is_none());
        debug_assert!(self.verbatim.is_none());
        self.store_cowstrs.clear();
        self.store_attributes.clear();
    }

    fn push_sp(&mut self, kind: EventKind<'s>, span: std::ops::Range<usize>) {
        self.events.push_back(Event { kind, span });
    }

    fn push(&mut self, kind: EventKind<'s>) -> ControlFlow {
        self.push_sp(kind, self.input.span.clone());
        Continue
    }

    fn parse_event(&mut self) -> ControlFlow {
        self.input.reset_span();

        if let Some(first) = self.input.eat() {
            self.parse_verbatim(&first)
                .or_else(|| self.parse_attributes(&first))
                .or_else(|| self.parse_autolink(&first))
                .or_else(|| self.parse_symbol(&first))
                .or_else(|| self.parse_footnote_reference(&first))
                .or_else(|| self.parse_container(&first))
                .or_else(|| self.parse_atom(&first))
                .unwrap_or_else(|| self.push(EventKind::Str))
        } else if self.input.last() {
            Done
        } else {
            Next
        }
    }

    fn parse_verbatim(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if let Some(VerbatimState {
            event_opener,
            len_opener,
            non_whitespace_encountered,
            non_whitespace_last,
        }) = &mut self.verbatim
        {
            let event_opener = *event_opener;
            let len_opener = *len_opener;
            if usize::from(len_opener) == first.len
                && matches!(first.kind, lex::Kind::Seq(Sequence::Backtick))
            {
                let raw_format = self.input.ahead_raw_format();
                if let Some(span_format) = raw_format.clone() {
                    self.events[event_opener].kind = EventKind::Enter(RawFormat {
                        format: &self.input.src[span_format.clone()],
                    });
                    self.input.span.end = span_format.end + 1;
                }
                let ty_opener = if let EventKind::Enter(ty) = self.events[event_opener].kind {
                    debug_assert!(matches!(
                        ty,
                        Verbatim | RawFormat { .. } | InlineMath | DisplayMath
                    ));
                    ty
                } else {
                    panic!()
                };
                if let Some((lex::Kind::Seq(Sequence::Backtick), event_skip)) = non_whitespace_last
                {
                    self.events.drain(*event_skip..);
                }
                self.push(EventKind::Exit(ty_opener));
                self.input.lexer.verbatim = false;
                self.verbatim = None;
                if raw_format.is_none()
                    && self.input.peek().map_or(false, |t| {
                        matches!(t.kind, lex::Kind::Open(Delimiter::Brace))
                    })
                {
                    return self
                        .ahead_attributes(
                            AttributesElementType::Container {
                                e_placeholder: event_opener - 1,
                            },
                            false,
                        )
                        .or(Some(Continue));
                }
            } else {
                // continue verbatim
                let is_whitespace = self.input.src.as_bytes()[self.input.span.clone()]
                    .iter()
                    .all(|b| b.is_ascii_whitespace());
                if is_whitespace {
                    if !*non_whitespace_encountered
                        && self.input.peek().map_or(false, |t| {
                            matches!(
                                t.kind,
                                lex::Kind::Seq(Sequence::Backtick) if t.len != len_opener.into(),
                            )
                        })
                    {
                        return Some(Continue); // skip whitespace
                    }
                } else {
                    *non_whitespace_encountered = true;
                    *non_whitespace_last = Some((first.kind, self.events.len() + 1));
                }
                self.push(EventKind::Str);
            }
            Some(Continue)
        } else if matches!(first.kind, lex::Kind::Seq(Sequence::Backtick)) {
            let len_opener = u8::try_from(first.len).ok()?;
            let ty = if let Some(sp) = self
                .events
                .back()
                .and_then(|e| matches!(&e.kind, EventKind::Str).then(|| e.span.clone()))
                .filter(|sp| {
                    sp.end == self.input.span.start
                        && self.input.src.as_bytes()[sp.start + sp.len() - 1] == b'$'
                        && sp
                            .end
                            .checked_sub(2)
                            .map_or(true, |i| self.input.src.as_bytes()[i] != b'\\')
                }) {
                let (ty, num_dollar) = if sp.len() > 1
                    && self.input.src.as_bytes()[sp.start + sp.len() - 2] == b'$'
                    && sp
                        .end
                        .checked_sub(3)
                        .map_or(true, |i| self.input.src.as_bytes()[i] != b'\\')
                {
                    (DisplayMath, 2)
                } else {
                    (InlineMath, 1)
                };
                let border = sp.end - num_dollar;
                self.events.back_mut().unwrap().span = sp.start..border;
                self.input.span = border..self.input.span.end;
                ty
            } else {
                Verbatim
            };
            self.push_sp(
                EventKind::Placeholder,
                self.input.span.start..self.input.span.start,
            );
            self.input.lexer.verbatim = true;
            self.verbatim = Some(VerbatimState {
                event_opener: self.events.len(),
                len_opener,
                non_whitespace_encountered: false,
                non_whitespace_last: None,
            });
            self.attributes = None;
            Some(self.push(EventKind::Enter(ty)))
        } else {
            None
        }
    }

    fn parse_attributes(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Open(Delimiter::Brace) {
            if let Some(state) = self.attributes.take() {
                self.resume_attributes(state, true, false)
            } else {
                self.ahead_attributes(AttributesElementType::Word, true)
            }
        } else {
            debug_assert!(self.attributes.is_none());
            None
        }
    }

    fn ahead_attributes(
        &mut self,
        elem_ty: AttributesElementType,
        opener_eaten: bool,
    ) -> Option<ControlFlow> {
        let state = AttributesState {
            elem_ty,
            end_attr: self.input.span.end - usize::from(opener_eaten),
            valid_lines: 0,
            validator: attr::Validator::new(),
        };
        self.resume_attributes(state, opener_eaten, true)
    }

    fn resume_attributes(
        &mut self,
        mut state: AttributesState,
        opener_eaten: bool,
        first: bool,
    ) -> Option<ControlFlow> {
        let start_attr = self.input.span.end - usize::from(opener_eaten);
        debug_assert!(self.input.src[start_attr..].starts_with('{'));

        let (mut line_next, mut line_start, mut line_end) = if first {
            (0, start_attr, self.input.span_line.end)
        } else {
            let last = self.input.ahead.len() - 1;
            (
                self.input.ahead.len(),
                self.input.ahead[last].start,
                self.input.ahead[last].end,
            )
        };
        {
            let mut res = state.validator.parse(&self.input.src[line_start..line_end]);
            loop {
                if let Some(len) = res.take() {
                    if len == 0 {
                        break;
                    }
                    state.valid_lines = line_next;
                    state.end_attr = line_start + len;
                    if self.input.src[state.end_attr..].starts_with('{') {
                        line_start = state.end_attr;
                        state.validator.restart();
                        res = state
                            .validator
                            .parse(&self.input.src[state.end_attr..line_end]);
                    } else {
                        break;
                    }
                } else if let Some(l) = self.input.ahead.get(line_next) {
                    line_next += 1;
                    line_start = l.start;
                    line_end = l.end;
                    res = state.validator.parse(&self.input.src[l.clone()]);
                } else if self.input.complete {
                    // no need to ask for more input
                    break;
                } else {
                    self.attributes = Some(state);
                    if opener_eaten {
                        self.input.span = start_attr..start_attr;
                        self.input.lexer = lex::Lexer::new(
                            &self.input.src.as_bytes()[start_attr..self.input.span_line.end],
                        );
                    }
                    return Some(More);
                }
            }
        }

        if start_attr == state.end_attr {
            return None;
        }

        // retrieve attributes
        let attrs = {
            let first = start_attr..self.input.span_line.end;
            let mut parser = attr::Parser::new(attr::Attributes::new());
            for line in std::iter::once(first)
                .chain(self.input.ahead.iter().take(state.valid_lines).cloned())
            {
                let line = line.start..usize::min(state.end_attr, line.end);
                parser
                    .parse(&self.input.src[line])
                    .expect("should be valid");
            }
            parser.finish()
        };

        for _ in 0..line_next {
            let l = self.input.ahead.pop_front().unwrap();
            self.input.set_current_line(l);
        }
        self.input.span = start_attr..state.end_attr;
        self.input.lexer = lex::Lexer::new(&self.input.src.as_bytes()[state.end_attr..line_end]);

        if attrs.is_empty() {
            if matches!(state.elem_ty, AttributesElementType::Container { .. }) {
                let last = self.events.len() - 1;
                self.events[last].span.end = self.input.span.end;
            }
        } else {
            let attr_index = self.store_attributes.len() as AttributesIndex;
            self.store_attributes.push(attrs);
            let attr_event = Event {
                kind: EventKind::Attributes {
                    container: matches!(state.elem_ty, AttributesElementType::Container { .. }),
                    attrs: attr_index,
                },
                span: self.input.span.clone(),
            };
            match state.elem_ty {
                AttributesElementType::Container { mut e_placeholder } => {
                    self.events[e_placeholder] = attr_event;
                    let mut last = self.events.len() - 1;
                    if matches!(self.events[e_placeholder + 1].kind, EventKind::Str) {
                        let range = self.events[e_placeholder + 1].span.clone();
                        if &self.input.src[range] == "![" {
                            // Lexed as image link, but actually just a span preceeded by an exclamation mark
                            let start = self.events[e_placeholder + 1].span.start;
                            self.events.insert(
                                e_placeholder,
                                Event {
                                    kind: EventKind::Str,
                                    span: start..start + 1,
                                },
                            );
                            e_placeholder += 1;
                            last += 1;
                            self.events[e_placeholder + 1].span.start += 1;
                        }
                        self.events[e_placeholder + 1].kind = EventKind::Enter(Span);
                        self.events[last].kind = EventKind::Exit(Span);
                    }
                    self.events[last].span.end = self.input.span.end;
                }
                AttributesElementType::Word => {
                    self.events.push_back(attr_event);
                    // push for now, pop later if attrs attached to word
                    self.push(EventKind::Empty);
                }
            }
        }

        Some(Continue)
    }

    fn parse_autolink(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Sym(Symbol::Lt) {
            let mut end = false;
            let mut is_url = false;
            let len = self
                .input
                .lexer
                .ahead()
                .iter()
                .take_while(|c| {
                    if **c == b'<' {
                        return false;
                    }
                    if **c == b'>' {
                        end = true;
                    }
                    if matches!(*c, b':' | b'@') {
                        is_url = true;
                    }
                    !end && !c.is_ascii_whitespace()
                })
                .count();
            if end && is_url {
                self.input.lexer.skip_ahead(len + 1);
                let span_url = self.input.span.end..(self.input.span.end + len);
                let url = &self.input.src[span_url.clone()];
                self.push(EventKind::Enter(Autolink(url)));
                self.input.span = span_url;
                self.push(EventKind::Str);
                self.input.span = self.input.span.end..(self.input.span.end + 1);
                return Some(self.push(EventKind::Exit(Autolink(url))));
            }
        }
        None
    }

    fn parse_symbol(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Sym(Symbol::Colon) {
            let mut end = false;
            let mut valid = true;
            let len = self
                .input
                .lexer
                .ahead()
                .iter()
                .take_while(|c| {
                    if **c == b':' {
                        end = true;
                    } else if !c.is_ascii_alphanumeric() && !matches!(c, b'-' | b'+' | b'_') {
                        valid = false;
                    }
                    !end && !c.is_ascii_whitespace()
                })
                .count();
            if end && valid {
                self.input.lexer.skip_ahead(len + 1);
                let span_symbol = self.input.span.end..(self.input.span.end + len);
                self.input.span.end = span_symbol.end + 1;
                return Some(
                    self.push(EventKind::Atom(Atom::Symbol(&self.input.src[span_symbol]))),
                );
            }
        }
        None
    }

    fn parse_footnote_reference(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Open(Delimiter::Bracket)
            && matches!(
                self.input.peek(),
                Some(lex::Token {
                    kind: lex::Kind::Sym(Symbol::Caret),
                    ..
                })
            )
        {
            let tok = self.input.eat();
            debug_assert_eq!(
                tok,
                Some(lex::Token {
                    kind: lex::Kind::Sym(Symbol::Caret),
                    len: 1,
                })
            );
            let mut end = false;
            let len = self
                .input
                .lexer
                .ahead()
                .iter()
                .take_while(|c| {
                    if **c == b'[' {
                        return false;
                    }
                    if **c == b']' {
                        end = true;
                    }
                    !end && **c != b'\n'
                })
                .count();
            if end {
                self.input.lexer.skip_ahead(len + 1);
                let span_label = self.input.span.end..(self.input.span.end + len);
                let label = &self.input.src[span_label.clone()];
                self.input.span.end = span_label.end + 1;
                return Some(self.push(EventKind::Atom(FootnoteReference { label })));
            }
        }
        None
    }

    fn parse_container(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        self.openers
            .iter()
            .rposition(|(o, _)| o.closed_by(first.kind))
            .and_then(|o| {
                let (opener, e) = self.openers[o];
                let (e_attr, e_opener) = if let Opener::Link { event_span, .. } = opener {
                    (event_span - 1, e)
                } else {
                    (e, e + 1)
                };

                if e_opener == self.events.len() - 1
                    && !matches!(opener, Opener::Link { .. } | Opener::Span { .. })
                {
                    // empty container
                    return None;
                }
                let whitespace_before = self
                    .input
                    .src
                    .as_bytes()
                    .get(self.input.span.start.saturating_sub(1))
                    .map_or(false, u8::is_ascii_whitespace);
                if opener.bidirectional() && whitespace_before {
                    return None;
                }

                self.openers.drain(o..);
                let closed = match DelimEventKind::from(opener) {
                    DelimEventKind::Container(cont) => {
                        self.events[e_opener].kind = EventKind::Enter(cont);
                        Some(self.push(EventKind::Exit(cont)))
                    }
                    DelimEventKind::Quote(ty) => {
                        self.events[e_opener].kind = EventKind::Atom(Quote { ty, left: true });
                        Some(self.push(EventKind::Atom(Quote { ty, left: false })))
                    }
                    DelimEventKind::Span(ty) => {
                        if let Some(lex::Kind::Open(d @ (Delimiter::Bracket | Delimiter::Paren))) =
                            self.input.peek().map(|t| t.kind)
                        {
                            self.push(EventKind::Str); // ]
                            self.openers.push((
                                Opener::Link {
                                    event_span: e_opener,
                                    image: matches!(ty, SpanType::Image),
                                    inline: matches!(d, Delimiter::Paren),
                                },
                                self.events.len(),
                            ));
                            self.input.reset_span();
                            self.input.eat(); // [ or (
                            return Some(self.push(EventKind::Str));
                        } else {
                            Some(self.push(EventKind::Str)) // ]
                        }
                    }
                    DelimEventKind::Link {
                        event_span,
                        inline,
                        image,
                    } => {
                        let span_spec = self.events[e_opener].span.end..self.input.span.start;
                        let multiline_spec =
                            self.events[e_opener].span.start < self.input.span_line.start;

                        let spec: CowStr = if span_spec.is_empty() && !inline {
                            let events_text = self
                                .events
                                .iter()
                                .skip(event_span + 1)
                                .take(e_opener - event_span - 2);

                            let mut spec = String::new();
                            let mut span = 0..0;
                            for ev in events_text.filter(|ev| {
                                matches!(ev.kind, EventKind::Str | EventKind::Atom(..))
                                    && !matches!(ev.kind, EventKind::Atom(Escape))
                            }) {
                                if matches!(ev.kind, EventKind::Atom(Softbreak | Hardbreak)) {
                                    spec.push_str(&self.input.src[span.clone()]);
                                    spec.push(' ');
                                    span = ev.span.end..ev.span.end;
                                } else if span.end == ev.span.start {
                                    span.end = ev.span.end;
                                } else {
                                    spec.push_str(&self.input.src[span.clone()]);
                                    span = ev.span.clone();
                                }
                            }
                            spec.push_str(&self.input.src[span]);
                            spec.into()
                        } else if multiline_spec {
                            let mut spec = String::new();
                            let mut first_part = true;
                            let mut span =
                                self.events[e_opener].span.end..self.events[e_opener].span.end;

                            let mut append = |span: std::ops::Range<usize>| {
                                self.input.src[span].split('\n').for_each(|s| {
                                    if !s.is_empty() {
                                        if !inline && !first_part {
                                            spec.push(' ');
                                        }
                                        spec.push_str(s);
                                        first_part = false;
                                    }
                                });
                            };

                            for ev in self.events.iter().skip(e_opener + 1) {
                                if span.end == ev.span.start {
                                    span.end = ev.span.end;
                                } else {
                                    append(span);
                                    span = ev.span.clone();
                                }
                            }
                            append(span);

                            spec.into()
                        } else {
                            self.input.src[span_spec.clone()].into()
                        };

                        let idx = self.store_cowstrs.len() as CowStrIndex;
                        self.store_cowstrs.push(spec);
                        let container = match (image, inline) {
                            (false, false) => ReferenceLink(idx),
                            (false, true) => InlineLink(idx),
                            (true, false) => ReferenceImage(idx),
                            (true, true) => InlineImage(idx),
                        };
                        self.events[event_span].kind = EventKind::Enter(container);
                        self.events[e_opener - 1] = Event {
                            kind: EventKind::Exit(container),
                            span: (self.events[e_opener - 1].span.start)..(span_spec.end + 1),
                        };
                        self.events.drain(e_opener..);
                        Some(Continue)
                    }
                };

                if self.input.peek().map_or(false, |t| {
                    matches!(t.kind, lex::Kind::Open(Delimiter::Brace))
                }) {
                    let elem_ty = if matches!(opener, Opener::DoubleQuoted | Opener::SingleQuoted) {
                        // quote delimiters will turn into atoms instead of containers, so cannot
                        // place attributes on the container start
                        AttributesElementType::Word
                    } else {
                        AttributesElementType::Container {
                            e_placeholder: e_attr,
                        }
                    };
                    self.ahead_attributes(elem_ty, false).or(Some(Continue))
                } else {
                    closed
                }
            })
            .or_else(|| {
                let opener = Opener::from_token(first.kind)?;
                let whitespace_after = self
                    .input
                    .lexer
                    .ahead()
                    .iter()
                    .next()
                    .map_or(true, |c| c.is_ascii_whitespace());
                if opener.bidirectional() && whitespace_after {
                    return None;
                }
                let whitespace_before = if 0 < self.input.span.start {
                    self.input.src.as_bytes()[self.input.span.start - 1].is_ascii_whitespace()
                } else {
                    false
                };
                if matches!(opener, Opener::SingleQuoted)
                    && self
                        .events
                        .back()
                        .map_or(false, |ev| matches!(ev.kind, EventKind::Str))
                    && !whitespace_before
                {
                    return None;
                }
                self.openers.push((opener, self.events.len()));
                // push dummy event in case attributes are encountered after closing delimiter
                self.push_sp(
                    EventKind::Placeholder,
                    self.input.span.start..self.input.span.start,
                );
                // use non-opener for now, replace if closed later
                Some(self.push(match opener {
                    Opener::SingleQuoted => EventKind::Atom(Quote {
                        ty: QuoteType::Single,
                        left: false,
                    }),
                    Opener::DoubleQuoted => EventKind::Atom(Quote {
                        ty: QuoteType::Double,
                        left: true,
                    }),
                    _ => EventKind::Str,
                }))
            })
    }

    fn parse_atom(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        let atom = match first.kind {
            lex::Kind::Newline => Softbreak,
            lex::Kind::Hardbreak => Hardbreak,
            lex::Kind::Escape => Escape,
            lex::Kind::Nbsp => Nbsp,
            lex::Kind::Seq(Sequence::Period) => {
                while self.input.span.len() >= 3 {
                    let end = self.input.span.start + 3;
                    self.push_sp(EventKind::Atom(Ellipsis), self.input.span.start..end);
                    self.input.span.start = end;
                }
                return None;
            }
            lex::Kind::Seq(Sequence::Hyphen) if first.len >= 2 => {
                let (m, n) = if first.len % 3 == 0 {
                    (first.len / 3, 0)
                } else if first.len % 2 == 0 {
                    (0, first.len / 2)
                } else {
                    let n = (1..).find(|n| (first.len - 2 * n) % 3 == 0).unwrap();
                    ((first.len - 2 * n) / 3, n)
                };
                std::iter::repeat(EmDash)
                    .take(m)
                    .chain(std::iter::repeat(EnDash).take(n))
                    .for_each(|atom| {
                        let end =
                            self.input.span.start + if matches!(atom, EnDash) { 2 } else { 3 };
                        self.push_sp(EventKind::Atom(atom), self.input.span.start..end);
                        self.input.span.start = end;
                    });
                return Some(Continue);
            }
            lex::Kind::Open(Delimiter::BraceQuote1) => Quote {
                ty: QuoteType::Single,
                left: true,
            },
            lex::Kind::Sym(Symbol::Quote1) | lex::Kind::Close(Delimiter::BraceQuote1) => Quote {
                ty: QuoteType::Single,
                left: false,
            },
            lex::Kind::Open(Delimiter::BraceQuote2) => Quote {
                ty: QuoteType::Double,
                left: true,
            },
            lex::Kind::Sym(Symbol::Quote2) | lex::Kind::Close(Delimiter::BraceQuote2) => Quote {
                ty: QuoteType::Double,
                left: false,
            },
            _ => return None,
        };

        Some(self.push(EventKind::Atom(atom)))
    }

    fn merge_str_events(&mut self, span_str: std::ops::Range<usize>) -> Event<'s> {
        let mut span = span_str;
        let should_merge = |e: &Event, span: std::ops::Range<usize>| {
            matches!(e.kind, EventKind::Str | EventKind::Placeholder) && span.end == e.span.start
        };
        while self
            .events
            .front()
            .map_or(false, |e| should_merge(e, span.clone()))
        {
            let ev = self.events.pop_front().unwrap();
            span.end = ev.span.end;
        }

        if matches!(
            self.events.front().map(|ev| &ev.kind),
            Some(EventKind::Attributes {
                container: false,
                ..
            })
        ) {
            self.apply_word_attributes(span)
        } else {
            Event {
                kind: EventKind::Str,
                span,
            }
        }
    }

    fn apply_word_attributes(&mut self, span_str: std::ops::Range<usize>) -> Event<'s> {
        if let Some(i) = self.input.src[span_str.clone()]
            .bytes()
            .rposition(|c| c.is_ascii_whitespace())
        {
            let word_start = span_str.start + i + 1;
            let before = span_str.start..word_start;
            let word = word_start..span_str.end;
            self.events.push_front(Event {
                kind: EventKind::Str,
                span: word,
            });
            Event {
                kind: EventKind::Str,
                span: before,
            }
        } else {
            let attr = self.events.pop_front().unwrap();
            if !span_str.is_empty() {
                let empty = self.events.pop_front();
                debug_assert_eq!(empty.unwrap().kind, EventKind::Empty);
                self.events.push_front(Event {
                    kind: EventKind::Exit(Span),
                    span: attr.span.clone(),
                });
                self.events.push_front(Event {
                    kind: EventKind::Str,
                    span: span_str.clone(),
                });
                self.events.push_front(Event {
                    kind: EventKind::Enter(Span),
                    span: span_str.start..span_str.start,
                });
            }
            attr
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Directionality {
    Uni,
    Bi,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpanType {
    Image,
    General,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Opener {
    Span(SpanType),
    Strong(Directionality),
    Emphasis(Directionality),
    Superscript(Directionality),
    Subscript(Directionality),
    Mark,
    Delete,
    Insert,
    SingleQuoted,
    DoubleQuoted,
    Link {
        event_span: usize,
        image: bool,
        inline: bool,
    },
}

impl Opener {
    fn from_token(kind: lex::Kind) -> Option<Self> {
        use Directionality::{Bi, Uni};
        use Opener::*;
        use SpanType::{General, Image};

        match kind {
            lex::Kind::Sym(Symbol::Asterisk) => Some(Strong(Bi)),
            lex::Kind::Sym(Symbol::Underscore) => Some(Emphasis(Bi)),
            lex::Kind::Sym(Symbol::Caret) => Some(Superscript(Bi)),
            lex::Kind::Sym(Symbol::Tilde) => Some(Subscript(Bi)),
            lex::Kind::Sym(Symbol::Quote1) => Some(SingleQuoted),
            lex::Kind::Sym(Symbol::Quote2) => Some(DoubleQuoted),
            lex::Kind::Sym(Symbol::ExclaimBracket) => Some(Span(Image)),
            lex::Kind::Open(Delimiter::Bracket) => Some(Span(General)),
            lex::Kind::Open(Delimiter::BraceAsterisk) => Some(Strong(Uni)),
            lex::Kind::Open(Delimiter::BraceUnderscore) => Some(Emphasis(Uni)),
            lex::Kind::Open(Delimiter::BraceCaret) => Some(Superscript(Uni)),
            lex::Kind::Open(Delimiter::BraceTilde) => Some(Subscript(Uni)),
            lex::Kind::Open(Delimiter::BraceEqual) => Some(Mark),
            lex::Kind::Open(Delimiter::BraceHyphen) => Some(Delete),
            lex::Kind::Open(Delimiter::BracePlus) => Some(Insert),
            lex::Kind::Open(Delimiter::BraceQuote1) => Some(SingleQuoted),
            lex::Kind::Open(Delimiter::BraceQuote2) => Some(DoubleQuoted),
            _ => None,
        }
    }

    fn closed_by(&self, kind: lex::Kind) -> bool {
        use Directionality::{Bi, Uni};
        use Opener::*;

        match self {
            Span(..) => matches!(kind, lex::Kind::Close(Delimiter::Bracket)),
            Strong(Bi) => matches!(kind, lex::Kind::Sym(Symbol::Asterisk)),
            Strong(Uni) => matches!(kind, lex::Kind::Close(Delimiter::BraceAsterisk)),
            Emphasis(Bi) => matches!(kind, lex::Kind::Sym(Symbol::Underscore)),
            Emphasis(Uni) => matches!(kind, lex::Kind::Close(Delimiter::BraceUnderscore)),
            Superscript(Bi) => matches!(kind, lex::Kind::Sym(Symbol::Caret)),
            Superscript(Uni) => matches!(kind, lex::Kind::Close(Delimiter::BraceCaret)),
            Subscript(Bi) => matches!(kind, lex::Kind::Sym(Symbol::Tilde)),
            Subscript(Uni) => matches!(kind, lex::Kind::Close(Delimiter::BraceTilde)),
            Mark => matches!(kind, lex::Kind::Close(Delimiter::BraceEqual)),
            Delete => matches!(kind, lex::Kind::Close(Delimiter::BraceHyphen)),
            Insert => matches!(kind, lex::Kind::Close(Delimiter::BracePlus)),
            SingleQuoted => matches!(
                kind,
                lex::Kind::Sym(Symbol::Quote1) | lex::Kind::Close(Delimiter::BraceQuote1)
            ),
            DoubleQuoted => matches!(
                kind,
                lex::Kind::Sym(Symbol::Quote2) | lex::Kind::Close(Delimiter::BraceQuote2)
            ),
            Link { inline: false, .. } => matches!(kind, lex::Kind::Close(Delimiter::Bracket)),
            Link { inline: true, .. } => matches!(kind, lex::Kind::Close(Delimiter::Paren)),
        }
    }

    fn bidirectional(&self) -> bool {
        matches!(
            self,
            Opener::Strong(Directionality::Bi)
                | Opener::Emphasis(Directionality::Bi)
                | Opener::Superscript(Directionality::Bi)
                | Opener::Subscript(Directionality::Bi)
                | Opener::SingleQuoted
                | Opener::DoubleQuoted
        )
    }
}

enum DelimEventKind<'s> {
    Container(Container<'s>),
    Span(SpanType),
    Quote(QuoteType),
    Link {
        event_span: usize,
        image: bool,
        inline: bool,
    },
}

impl From<Opener> for DelimEventKind<'_> {
    fn from(d: Opener) -> Self {
        match d {
            Opener::Span(ty) => Self::Span(ty),
            Opener::Strong(..) => Self::Container(Strong),
            Opener::Emphasis(..) => Self::Container(Emphasis),
            Opener::Superscript(..) => Self::Container(Superscript),
            Opener::Subscript(..) => Self::Container(Subscript),
            Opener::Mark => Self::Container(Mark),
            Opener::Delete => Self::Container(Delete),
            Opener::Insert => Self::Container(Insert),
            Opener::SingleQuoted => Self::Quote(QuoteType::Single),
            Opener::DoubleQuoted => Self::Quote(QuoteType::Double),
            Opener::Link {
                event_span,
                image,
                inline,
            } => Self::Link {
                event_span,
                image,
                inline,
            },
        }
    }
}

impl<'s> Iterator for Parser<'s> {
    type Item = Event<'s>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.events.is_empty()
            || !self.openers.is_empty()
            || self.verbatim.is_some()
            || self.attributes.is_some()
            || self // for merge or attributes
                .events
                .back()
                .map_or(false, |ev| matches!(ev.kind, EventKind::Str))
        {
            match self.parse_event() {
                Continue => {}
                Done => break,
                Next => {
                    if let Some(l) = self.input.ahead.pop_front() {
                        self.input.set_current_line(l);
                    } else {
                        return None;
                    }
                }
                More => return None,
            }
        }

        // automatically close unclosed verbatim
        if let Some(VerbatimState { event_opener, .. }) = self.verbatim.take() {
            self.input.lexer.verbatim = false;
            let ty_opener = if let EventKind::Enter(ty) = self.events[event_opener].kind {
                debug_assert!(matches!(
                    ty,
                    Verbatim | RawFormat { .. } | InlineMath | DisplayMath
                ));
                ty
            } else {
                panic!()
            };
            self.push(EventKind::Exit(ty_opener));
        }

        self.events.pop_front().and_then(|e| match e.kind {
            EventKind::Str
                if e.span.is_empty()
                    && !matches!(
                        self.events.front().map(|ev| &ev.kind),
                        Some(EventKind::Attributes {
                            container: false,
                            ..
                        })
                    ) =>
            {
                self.next()
            }
            EventKind::Str => Some(self.merge_str_events(e.span)),
            EventKind::Placeholder => self.next(),
            _ => Some(e),
        })
    }
}

#[cfg(test)]
#[path = "test_inline.rs"]
mod test;
