use crate::attr;
use crate::lex;
use crate::CowStr;
use crate::Span;

use lex::Delimiter;
use lex::Sequence;
use lex::Symbol;

use Atom::*;
use Container::*;
use ControlFlow::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    FootnoteReference,
    Symbol,
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
    RawFormat {
        format: &'s str,
    },
    InlineMath,
    DisplayMath,
    ReferenceLink(CowStrIndex),
    ReferenceImage(CowStrIndex),
    InlineLink(CowStrIndex),
    InlineImage(CowStrIndex),
    /// Open delimiter span is URL, closing is '>'.
    Autolink,
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
    Atom(Atom),
    Str,
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
    pub span: Span,
}

#[derive(Clone)]
struct Input<'s> {
    src: &'s str,
    /// Lexer.
    lexer: lex::Lexer<'s>,
    /// The block is complete, the final line has been provided.
    complete: bool,
    /// Span of current line.
    span_line: Span,
    /// Upcoming lines within the current block.
    ahead: std::collections::VecDeque<Span>,
    /// Span of current event.
    span: Span,
}

impl<'s> Input<'s> {
    fn new(src: &'s str) -> Self {
        Self {
            src,
            lexer: lex::Lexer::new(""),
            complete: false,
            span_line: Span::new(0, 0),
            ahead: std::collections::VecDeque::new(),
            span: Span::empty_at(0),
        }
    }

    fn feed_line(&mut self, line: Span, last: bool) {
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

    fn set_current_line(&mut self, line: Span) {
        self.lexer = lex::Lexer::new(line.of(self.src));
        self.span_line = line;
        self.span = line.empty_before();
    }

    fn reset(&mut self) {
        self.lexer = lex::Lexer::new("");
        self.complete = false;
        self.ahead.clear();
    }

    fn last(&self) -> bool {
        self.complete && self.ahead.is_empty()
    }

    fn eat(&mut self) -> Option<lex::Token> {
        let tok = self.lexer.next();
        if let Some(t) = &tok {
            self.span = self.span.extend(t.len);
        }
        tok
    }

    fn peek(&mut self) -> Option<&lex::Token> {
        self.lexer.peek()
    }

    fn reset_span(&mut self) {
        self.span = self.span.empty_after();
    }

    fn ahead_raw_format(&mut self) -> Option<Span> {
        if matches!(
            self.lexer.peek().map(|t| &t.kind),
            Some(lex::Kind::Open(Delimiter::BraceEqual))
        ) {
            let mut ahead = self.lexer.ahead().chars();
            let mut end = false;
            let len = (&mut ahead)
                .skip(2) // {=
                .take_while(|c| {
                    if *c == '{' {
                        return false;
                    }
                    if *c == '}' {
                        end = true;
                    };
                    !end && !c.is_whitespace()
                })
                .map(char::len_utf8)
                .sum();
            (len > 0 && end).then(|| {
                let tok = self.eat();
                debug_assert_eq!(
                    tok,
                    Some(lex::Token {
                        kind: lex::Kind::Open(Delimiter::BraceEqual),
                        len: 2,
                    })
                );
                self.lexer = lex::Lexer::new(ahead.as_str());
                self.span.after(len)
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

    pub fn feed_line(&mut self, line: Span, last: bool) {
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

    fn push_sp(&mut self, kind: EventKind<'s>, span: Span) -> Option<ControlFlow> {
        self.events.push_back(Event { kind, span });
        Some(Continue)
    }

    fn push(&mut self, kind: EventKind<'s>) -> Option<ControlFlow> {
        self.push_sp(kind, self.input.span)
    }

    fn parse_event(&mut self) -> ControlFlow {
        self.input.reset_span();

        if let Some(first) = self.input.eat() {
            self.parse_attributes(&first)
                .or_else(|| self.parse_verbatim(&first))
                .or_else(|| self.parse_autolink(&first))
                .or_else(|| self.parse_symbol(&first))
                .or_else(|| self.parse_footnote_reference(&first))
                .or_else(|| self.parse_container(&first))
                .or_else(|| self.parse_atom(&first))
                .unwrap_or_else(|| self.push(EventKind::Str).unwrap())
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
                if let Some(span_format) = raw_format {
                    self.events[event_opener].kind = EventKind::Enter(RawFormat {
                        format: span_format.of(self.input.src),
                    });
                    self.input.span = Span::new(self.input.span.start(), span_format.end() + 1);
                };
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
                let is_whitespace = self
                    .input
                    .span
                    .of(self.input.src)
                    .chars()
                    .all(char::is_whitespace);
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
            };
            Some(Continue)
        } else if matches!(first.kind, lex::Kind::Seq(Sequence::Backtick)) {
            let len_opener = u8::try_from(first.len).ok()?;
            let ty = if let Some(sp) = self
                .events
                .back()
                .and_then(|e| matches!(&e.kind, EventKind::Str).then(|| e.span))
                .filter(|sp| {
                    sp.end() == self.input.span.start()
                        && sp.of(self.input.src).as_bytes()[sp.len() - 1] == b'$'
                        && sp
                            .end()
                            .checked_sub(2)
                            .map_or(true, |i| self.input.src.as_bytes()[i] != b'\\')
                }) {
                let (ty, num_dollar) = if sp.len() > 1
                    && sp.of(self.input.src).as_bytes()[sp.len() - 2] == b'$'
                    && sp
                        .end()
                        .checked_sub(3)
                        .map_or(true, |i| self.input.src.as_bytes()[i] != b'\\')
                {
                    (DisplayMath, 2)
                } else {
                    (InlineMath, 1)
                };
                let border = sp.end() - num_dollar;
                self.events.back_mut().unwrap().span = Span::new(sp.start(), border);
                self.input.span = Span::new(border, self.input.span.end());
                ty
            } else {
                Verbatim
            };
            self.push_sp(EventKind::Placeholder, self.input.span.empty_before());
            self.verbatim = Some(VerbatimState {
                event_opener: self.events.len(),
                len_opener,
                non_whitespace_encountered: false,
                non_whitespace_last: None,
            });
            self.attributes = None;
            self.push(EventKind::Enter(ty))
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
            end_attr: self.input.span.end() - usize::from(opener_eaten),
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
        let start_attr = self.input.span.end() - usize::from(opener_eaten);
        debug_assert!(self.input.src[start_attr..].starts_with('{'));

        let (mut line_next, mut line_start, mut line_end) = if first {
            (0, start_attr, self.input.span_line.end())
        } else {
            let last = self.input.ahead.len() - 1;
            (
                self.input.ahead.len(),
                self.input.ahead[last].start(),
                self.input.ahead[last].end(),
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
                    line_start = l.start();
                    line_end = l.end();
                    res = state.validator.parse(l.of(self.input.src));
                } else if self.input.complete {
                    // no need to ask for more input
                    break;
                } else {
                    self.attributes = Some(state);
                    if opener_eaten {
                        self.input.span = Span::empty_at(start_attr);
                        self.input.lexer = lex::Lexer::new(
                            &self.input.src[start_attr..self.input.span_line.end()],
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
            let first = Span::new(start_attr, self.input.span_line.end());
            let mut parser = attr::Parser::new(attr::Attributes::new());
            for line in std::iter::once(first)
                .chain(self.input.ahead.iter().take(state.valid_lines).copied())
            {
                let line = line.start()..usize::min(state.end_attr, line.end());
                parser.parse(&self.input.src[line]);
            }
            parser.finish()
        };

        for _ in 0..line_next {
            let l = self.input.ahead.pop_front().unwrap();
            self.input.set_current_line(l);
        }
        self.input.span = Span::new(start_attr, state.end_attr);
        self.input.lexer = lex::Lexer::new(&self.input.src[state.end_attr..line_end]);

        if !attrs.is_empty() {
            let attr_index = self.store_attributes.len() as AttributesIndex;
            self.store_attributes.push(attrs);
            let attr_event = Event {
                kind: EventKind::Attributes {
                    container: matches!(state.elem_ty, AttributesElementType::Container { .. }),
                    attrs: attr_index,
                },
                span: self.input.span,
            };
            match state.elem_ty {
                AttributesElementType::Container { e_placeholder } => {
                    self.events[e_placeholder] = attr_event;
                    if matches!(self.events[e_placeholder + 1].kind, EventKind::Str) {
                        self.events[e_placeholder + 1].kind = EventKind::Enter(Span);
                        let last = self.events.len() - 1;
                        self.events[last].kind = EventKind::Exit(Span);
                    }
                }
                AttributesElementType::Word => {
                    self.events.push_back(attr_event);
                }
            }
        }

        Some(Continue)
    }

    fn parse_autolink(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Sym(Symbol::Lt) {
            let mut ahead = self.input.lexer.ahead().chars();
            let mut end = false;
            let mut is_url = false;
            let len = (&mut ahead)
                .take_while(|c| {
                    if *c == '<' {
                        return false;
                    }
                    if *c == '>' {
                        end = true;
                    };
                    if matches!(*c, ':' | '@') {
                        is_url = true;
                    }
                    !end && !c.is_whitespace()
                })
                .map(char::len_utf8)
                .sum();
            if end && is_url {
                self.input.lexer = lex::Lexer::new(ahead.as_str());
                self.input.span = self.input.span.after(len);
                self.push(EventKind::Enter(Autolink));
                self.push(EventKind::Str);
                self.push(EventKind::Exit(Autolink));
                self.input.span = self.input.span.after(1);
                return Some(Continue);
            }
        }
        None
    }

    fn parse_symbol(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        if first.kind == lex::Kind::Sym(Symbol::Colon) {
            let mut ahead = self.input.lexer.ahead().chars();
            let mut end = false;
            let mut valid = true;
            let len = (&mut ahead)
                .take_while(|c| {
                    if *c == ':' {
                        end = true;
                    } else if !c.is_ascii_alphanumeric() && !matches!(c, '-' | '+' | '_') {
                        valid = false;
                    }
                    !end && !c.is_whitespace()
                })
                .map(char::len_utf8)
                .sum();
            if end && valid {
                self.input.lexer = lex::Lexer::new(ahead.as_str());
                self.input.span = self.input.span.after(len);
                self.push(EventKind::Atom(Symbol));
                self.input.span = self.input.span.after(1);
                return Some(Continue);
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
            let mut ahead = self.input.lexer.ahead().chars();
            let mut end = false;
            let len = (&mut ahead)
                .take_while(|c| {
                    if *c == '[' {
                        return false;
                    }
                    if *c == ']' {
                        end = true;
                    };
                    !end && *c != '\n'
                })
                .map(char::len_utf8)
                .sum();
            if end {
                self.input.lexer = lex::Lexer::new(ahead.as_str());
                self.input.span = self.input.span.after(len);
                self.push(EventKind::Atom(FootnoteReference));
                self.input.span = self.input.span.after(1);
                return Some(Continue);
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
                let whitespace_before = self.events.back().map_or(false, |ev| {
                    ev.span
                        .of(self.input.src)
                        .chars()
                        .last()
                        .map_or(false, char::is_whitespace)
                });
                if opener.bidirectional() && whitespace_before {
                    return None;
                }

                self.openers.drain(o..);
                let closed = match DelimEventKind::from(opener) {
                    DelimEventKind::Container(cont) => {
                        self.events[e_opener].kind = EventKind::Enter(cont);
                        self.push(EventKind::Exit(cont))
                    }
                    DelimEventKind::Quote(ty) => {
                        self.events[e_opener].kind = EventKind::Atom(Quote { ty, left: true });
                        self.push(EventKind::Atom(Quote { ty, left: false }))
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
                            return self.push(EventKind::Str);
                        } else {
                            self.push(EventKind::Str) // ]
                        }
                    }
                    DelimEventKind::Link {
                        event_span,
                        inline,
                        image,
                    } => {
                        let span_spec = self.events[e_opener].span.between(self.input.span);
                        let multiline =
                            self.events[e_opener].span.start() < self.input.span_line.start();

                        let spec: CowStr = if span_spec.is_empty() && !inline {
                            let span_spec = self.events[event_span]
                                .span
                                .between(self.events[e_opener - 1].span);
                            let events_text = self
                                .events
                                .iter()
                                .skip(event_span + 1)
                                .take(e_opener - event_span - 2);

                            if multiline
                                || events_text.clone().any(|ev| {
                                    !matches!(ev.kind, EventKind::Str | EventKind::Atom(..))
                                })
                            {
                                events_text
                                    .filter(|ev| {
                                        matches!(ev.kind, EventKind::Str | EventKind::Atom(..))
                                    })
                                    .map(|ev| ev.span.of(self.input.src))
                                    .collect::<String>()
                                    .into()
                            } else {
                                span_spec.of(self.input.src).into()
                            }
                        } else if multiline {
                            let mut spec = String::new();
                            let mut first_part = true;
                            let mut span = self.events[e_opener].span.empty_after();

                            let mut append = |span: Span| {
                                span.of(self.input.src).split('\n').for_each(|s| {
                                    if !s.is_empty() {
                                        if !inline && !first_part {
                                            spec.push(' ');
                                        }
                                        spec.push_str(s);
                                        first_part = false;
                                    }
                                })
                            };

                            for ev in self.events.iter().skip(e_opener + 1) {
                                if span.end() == ev.span.start() {
                                    span = Span::new(span.start(), ev.span.end());
                                } else {
                                    append(span);
                                    span = ev.span;
                                }
                            }
                            append(span);

                            spec.into()
                        } else {
                            span_spec.of(self.input.src).into()
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
                            span: Span::new(
                                self.events[e_opener - 1].span.start(),
                                span_spec.end() + 1,
                            ),
                        };
                        self.events.drain(e_opener..);
                        Some(Continue)
                    }
                };

                if self.input.peek().map_or(false, |t| {
                    matches!(t.kind, lex::Kind::Open(Delimiter::Brace))
                }) {
                    self.ahead_attributes(
                        AttributesElementType::Container {
                            e_placeholder: e_attr,
                        },
                        false,
                    )
                    .or(Some(Continue))
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
                    .chars()
                    .next()
                    .map_or(true, char::is_whitespace);
                if opener.bidirectional() && whitespace_after {
                    return None;
                }
                let whitespace_before = self.events.back().map_or(false, |ev| {
                    ev.span
                        .of(self.input.src)
                        .chars()
                        .last()
                        .map_or(false, char::is_whitespace)
                });
                if matches!(opener, Opener::SingleQuoted | Opener::DoubleQuoted)
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
                    Span::empty_at(self.input.span.start()),
                );
                // use non-opener for now, replace if closed later
                self.push(match opener {
                    Opener::SingleQuoted => EventKind::Atom(Quote {
                        ty: QuoteType::Single,
                        left: false,
                    }),
                    Opener::DoubleQuoted => EventKind::Atom(Quote {
                        ty: QuoteType::Double,
                        left: true,
                    }),
                    _ => EventKind::Str,
                })
            })
    }

    fn parse_atom(&mut self, first: &lex::Token) -> Option<ControlFlow> {
        let atom = match first.kind {
            lex::Kind::Newline => Softbreak,
            lex::Kind::Hardbreak => Hardbreak,
            lex::Kind::Escape => Escape,
            lex::Kind::Nbsp => Nbsp,
            lex::Kind::Seq(Sequence::Period) if first.len >= 3 => {
                while self.input.span.len() > 3 {
                    self.push_sp(EventKind::Atom(Ellipsis), self.input.span.with_len(3));
                    self.input.span = self.input.span.skip(3);
                }
                if self.input.span.len() == 3 {
                    Ellipsis
                } else {
                    return self.push(EventKind::Str);
                }
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
                        let l = if matches!(atom, EnDash) { 2 } else { 3 };
                        self.push_sp(EventKind::Atom(atom), self.input.span.with_len(l));
                        self.input.span = self.input.span.skip(l);
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

        self.push(EventKind::Atom(atom))
    }

    fn merge_str_events(&mut self, span_str: Span) -> Event<'s> {
        let mut span = span_str;
        let should_merge = |e: &Event, span: Span| {
            matches!(e.kind, EventKind::Str | EventKind::Placeholder)
                && span.end() == e.span.start()
        };
        while self.events.front().map_or(false, |e| should_merge(e, span)) {
            let ev = self.events.pop_front().unwrap();
            span = span.union(ev.span);
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

    fn apply_word_attributes(&mut self, span_str: Span) -> Event<'s> {
        if let Some(i) = span_str
            .of(self.input.src)
            .bytes()
            .rposition(|c| c.is_ascii_whitespace())
        {
            let before = span_str.with_len(i + 1);
            let word = span_str.skip(i + 1);
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
            self.events.push_front(Event {
                kind: EventKind::Exit(Span),
                span: span_str.empty_after(),
            });
            self.events.push_front(Event {
                kind: EventKind::Str,
                span: span_str,
            });
            self.events.push_front(Event {
                kind: EventKind::Enter(Span),
                span: span_str.empty_before(),
            });
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

impl<'s> From<Opener> for DelimEventKind<'s> {
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
            EventKind::Str if e.span.is_empty() => self.next(),
            EventKind::Str => Some(self.merge_str_events(e.span)),
            EventKind::Placeholder
            | EventKind::Attributes {
                container: false, ..
            } => self.next(),
            _ => Some(e),
        })
    }
}

#[cfg(test)]
mod test {
    use super::Atom::*;
    use super::Container::*;
    use super::EventKind::*;
    use super::QuoteType;
    use super::Verbatim;

    macro_rules! test_parse {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let mut p = super::Parser::new($src);
            p.feed_line(super::Span::by_len(0, $src.len()), true);
            let actual = p.map(|ev| (ev.kind, ev.span.of($src))).collect::<Vec<_>>();
            let expected = &[$($($token),*,)?];
            assert_eq!(actual, expected, "\n\n{}\n\n", $src);
        };
    }

    #[test]
    fn str() {
        test_parse!("abc", (Str, "abc"));
        test_parse!("abc def", (Str, "abc def"));
    }

    #[test]
    fn verbatim() {
        test_parse!(
            "`abc`",
            (Enter(Verbatim), "`"),
            (Str, "abc"),
            (Exit(Verbatim), "`"),
        );
        test_parse!(
            "`abc\ndef`",
            (Enter(Verbatim), "`"),
            (Str, "abc\ndef"),
            (Exit(Verbatim), "`"),
        );
        test_parse!(
            "`abc&def`",
            (Enter(Verbatim), "`"),
            (Str, "abc&def"),
            (Exit(Verbatim), "`"),
        );
        test_parse!(
            "`abc",
            (Enter(Verbatim), "`"),
            (Str, "abc"),
            (Exit(Verbatim), ""),
        );
        test_parse!(
            "``abc``",
            (Enter(Verbatim), "``"),
            (Str, "abc"),
            (Exit(Verbatim), "``"),
        );
        test_parse!(
            "abc `def`",
            (Str, "abc "),
            (Enter(Verbatim), "`"),
            (Str, "def"),
            (Exit(Verbatim), "`"),
        );
        test_parse!(
            "abc`def`",
            (Str, "abc"),
            (Enter(Verbatim), "`"),
            (Str, "def"),
            (Exit(Verbatim), "`"),
        );
    }

    #[test]
    fn verbatim_attr() {
        test_parse!(
            "pre `raw`{#id} post",
            (Str, "pre "),
            (
                Attributes {
                    container: true,
                    attrs: 0,
                },
                "{#id}"
            ),
            (Enter(Verbatim), "`"),
            (Str, "raw"),
            (Exit(Verbatim), "`"),
            (Str, " post"),
        );
    }

    #[test]
    fn verbatim_whitespace() {
        test_parse!(
            "`  `",
            (Enter(Verbatim), "`"),
            (Str, "  "),
            (Exit(Verbatim), "`"),
        );
        test_parse!(
            "` abc `",
            (Enter(Verbatim), "`"),
            (Str, " abc "),
            (Exit(Verbatim), "`"),
        );
    }

    #[test]
    fn verbatim_trim() {
        test_parse!(
            "` ``abc`` `",
            (Enter(Verbatim), "`"),
            (Str, "``abc``"),
            (Exit(Verbatim), "`"),
        );
    }

    #[test]
    fn math() {
        test_parse!(
            "$`abc`",
            (Enter(InlineMath), "$`"),
            (Str, "abc"),
            (Exit(InlineMath), "`"),
        );
        test_parse!(
            "$`abc` str",
            (Enter(InlineMath), "$`"),
            (Str, "abc"),
            (Exit(InlineMath), "`"),
            (Str, " str"),
        );
        test_parse!(
            "$$`abc`",
            (Enter(DisplayMath), "$$`"),
            (Str, "abc"),
            (Exit(DisplayMath), "`"),
        );
        test_parse!(
            "$`abc",
            (Enter(InlineMath), "$`"),
            (Str, "abc"),
            (Exit(InlineMath), ""),
        );
        test_parse!(
            "$```abc```",
            (Enter(InlineMath), "$```"),
            (Str, "abc"),
            (Exit(InlineMath), "```"),
        );
    }

    #[test]
    fn raw_format() {
        test_parse!(
            "`raw`{=format}",
            (Enter(RawFormat { format: "format" }), "`"),
            (Str, "raw"),
            (Exit(RawFormat { format: "format" }), "`{=format}"),
        );
        test_parse!(
            "before `raw`{=format} after",
            (Str, "before "),
            (Enter(RawFormat { format: "format" }), "`"),
            (Str, "raw"),
            (Exit(RawFormat { format: "format" }), "`{=format}"),
            (Str, " after"),
        );
    }

    #[test]
    fn raw_attr() {
        test_parse!(
            "`raw`{=format #id}",
            (Enter(Verbatim), "`"),
            (Str, "raw"),
            (Exit(Verbatim), "`"),
            (Str, "{=format #id}"),
        );
    }

    #[test]
    fn span_tag() {
        test_parse!(
            "[text][tag]",
            (Enter(ReferenceLink(0)), "["),
            (Str, "text"),
            (Exit(ReferenceLink(0)), "][tag]"),
        );
        test_parse!(
            "![text][tag]",
            (Enter(ReferenceImage(0)), "!["),
            (Str, "text"),
            (Exit(ReferenceImage(0)), "][tag]"),
        );
        test_parse!(
            "before [text][tag] after",
            (Str, "before "),
            (Enter(ReferenceLink(0)), "["),
            (Str, "text"),
            (Exit(ReferenceLink(0)), "][tag]"),
            (Str, " after"),
        );
        test_parse!(
            "[[inner][i]][o]",
            (Enter(ReferenceLink(1)), "["),
            (Enter(ReferenceLink(0)), "["),
            (Str, "inner"),
            (Exit(ReferenceLink(0)), "][i]"),
            (Exit(ReferenceLink(1)), "][o]"),
        );
    }

    #[test]
    fn span_tag_empty() {
        test_parse!(
            "[text][]",
            (Enter(ReferenceLink(0)), "["),
            (Str, "text"),
            (Exit(ReferenceLink(0)), "][]"),
        );
        test_parse!(
            "![text][]",
            (Enter(ReferenceImage(0)), "!["),
            (Str, "text"),
            (Exit(ReferenceImage(0)), "][]"),
        );
    }

    #[test]
    fn span_tag_empty_nested() {
        test_parse!(
            "[some _text_][]",
            (Enter(ReferenceLink(0)), "["),
            (Str, "some "),
            (Enter(Emphasis), "_"),
            (Str, "text"),
            (Exit(Emphasis), "_"),
            (Exit(ReferenceLink(0)), "][]"),
        );
    }

    #[test]
    fn span_url() {
        test_parse!(
            "before [text](url) after",
            (Str, "before "),
            (Enter(InlineLink(0)), "["),
            (Str, "text"),
            (Exit(InlineLink(0)), "](url)"),
            (Str, " after"),
        );
        test_parse!(
            "[outer [inner](i)](o)",
            (Enter(InlineLink(1)), "["),
            (Str, "outer "),
            (Enter(InlineLink(0)), "["),
            (Str, "inner"),
            (Exit(InlineLink(0)), "](i)"),
            (Exit(InlineLink(1)), "](o)"),
        );
    }

    #[test]
    fn span_url_attr_unclosed() {
        test_parse!(
            "[text]({.cls}",
            (
                Attributes {
                    container: false,
                    attrs: 0,
                },
                "{.cls}"
            ),
            (Enter(Span), ""),
            (Str, "[text]("),
            (Exit(Span), ""),
        );
    }

    #[test]
    fn span_url_attr_closed() {
        test_parse!(
            "[text]({.cls})",
            (Enter(InlineLink(0)), "["),
            (Str, "text"),
            (Exit(InlineLink(0)), "]({.cls})"),
        );
    }

    #[test]
    fn span_url_empty() {
        test_parse!(
            "before [text]() after",
            (Str, "before "),
            (Enter(InlineLink(0)), "["),
            (Str, "text"),
            (Exit(InlineLink(0)), "]()"),
            (Str, " after"),
        );
    }

    #[test]
    fn span_url_unclosed() {
        test_parse!("[text](url", (Str, "[text](url"));
    }

    #[test]
    fn span() {
        test_parse!("[abc]", (Str, "[abc]"));
    }

    #[test]
    fn span_no_text() {
        test_parse!("[]", (Str, "[]"));
        test_parse!(
            "[](url)",
            (Enter(InlineLink(0)), "["),
            (Exit(InlineLink(0)), "](url)"),
        );
        test_parse!(
            "![](url)",
            (Enter(InlineImage(0)), "!["),
            (Exit(InlineImage(0)), "](url)"),
        );
        test_parse!(
            "[][label]",
            (Enter(ReferenceLink(0)), "["),
            (Exit(ReferenceLink(0)), "][label]"),
        );
        test_parse!(
            "[]{.cls}",
            (
                Attributes {
                    container: true,
                    attrs: 0
                },
                "{.cls}",
            ),
            (Enter(Span), "["),
            (Exit(Span), "]")
        );
    }

    #[test]
    fn span_attr() {
        test_parse!(
            "[abc]{.def}",
            (
                Attributes {
                    container: true,
                    attrs: 0,
                },
                "{.def}"
            ),
            (Enter(Span), "["),
            (Str, "abc"),
            (Exit(Span), "]"),
        );
        test_parse!("not a [span] {#id}.", (Str, "not a [span] "), (Str, "."));
    }

    #[test]
    fn span_attr_cont() {
        test_parse!(
            "[x_y]{.bar_}",
            (
                Attributes {
                    container: true,
                    attrs: 0,
                },
                "{.bar_}"
            ),
            (Enter(Span), "["),
            (Str, "x_y"),
            (Exit(Span), "]"),
        );
    }

    #[test]
    fn autolink() {
        test_parse!(
            "<https://example.com>",
            (Enter(Autolink), "https://example.com"),
            (Str, "https://example.com"),
            (Exit(Autolink), "https://example.com")
        );
        test_parse!(
            "<a@b.c>",
            (Enter(Autolink), "a@b.c"),
            (Str, "a@b.c"),
            (Exit(Autolink), "a@b.c"),
        );
        test_parse!(
            "<http://a.b><http://c.d>",
            (Enter(Autolink), "http://a.b"),
            (Str, "http://a.b"),
            (Exit(Autolink), "http://a.b"),
            (Enter(Autolink), "http://c.d"),
            (Str, "http://c.d"),
            (Exit(Autolink), "http://c.d"),
        );
        test_parse!("<not-a-url>", (Str, "<not-a-url>"));
    }

    #[test]
    fn footnote_reference() {
        test_parse!(
            "text[^footnote]. more text",
            (Str, "text"),
            (Atom(FootnoteReference), "footnote"),
            (Str, ". more text"),
        );
    }

    #[test]
    fn container_basic() {
        test_parse!(
            "_abc_",
            (Enter(Emphasis), "_"),
            (Str, "abc"),
            (Exit(Emphasis), "_"),
        );
        test_parse!(
            "{_abc_}",
            (Enter(Emphasis), "{_"),
            (Str, "abc"),
            (Exit(Emphasis), "_}"),
        );
    }

    #[test]
    fn container_nest() {
        test_parse!(
            "{_{_abc_}_}",
            (Enter(Emphasis), "{_"),
            (Enter(Emphasis), "{_"),
            (Str, "abc"),
            (Exit(Emphasis), "_}"),
            (Exit(Emphasis), "_}"),
        );
        test_parse!(
            "*_abc_*",
            (Enter(Strong), "*"),
            (Enter(Emphasis), "_"),
            (Str, "abc"),
            (Exit(Emphasis), "_"),
            (Exit(Strong), "*"),
        );
    }

    #[test]
    fn container_unclosed_attr() {
        test_parse!(
            "^.^{unclosed",
            (Enter(Superscript), "^"),
            (Str, "."),
            (Exit(Superscript), "^"),
            (Str, "{unclosed"),
        );
    }

    #[test]
    fn verbatim_unclosed_attr() {
        test_parse!(
            "`.`{unclosed",
            (Enter(Verbatim), "`"),
            (Str, "."),
            (Exit(Verbatim), "`"),
            (Str, "{unclosed"),
        );
    }

    #[test]
    fn container_unopened() {
        test_parse!("*}abc", (Str, "*}abc"));
    }

    #[test]
    fn container_close_parent() {
        test_parse!(
            "{*{_abc*}",
            (Enter(Strong), "{*"),
            (Str, "{_abc"),
            (Exit(Strong), "*}"),
        );
    }

    #[test]
    fn container_close_block() {
        test_parse!("{_abc", (Str, "{_abc"));
        test_parse!("{_{*{_abc", (Str, "{_{*{_abc"));
    }

    #[test]
    fn container_attr() {
        test_parse!(
            "_abc def_{.attr}",
            (
                Attributes {
                    container: true,
                    attrs: 0,
                },
                "{.attr}"
            ),
            (Enter(Emphasis), "_"),
            (Str, "abc def"),
            (Exit(Emphasis), "_"),
        );
    }

    #[test]
    fn container_attr_empty() {
        test_parse!(
            "_abc def_{}",
            (Enter(Emphasis), "_"),
            (Str, "abc def"),
            (Exit(Emphasis), "_"),
        );
        test_parse!(
            "_abc def_{ % comment % } ghi",
            (Enter(Emphasis), "_"),
            (Str, "abc def"),
            (Exit(Emphasis), "_"),
            (Str, " ghi"),
        );
    }

    #[test]
    fn container_attr_multiple() {
        test_parse!(
            "_abc def_{.a}{.b}{.c} {.d}",
            (
                Attributes {
                    container: true,
                    attrs: 0,
                },
                "{.a}{.b}{.c}"
            ),
            (Enter(Emphasis), "_"),
            (Str, "abc def"),
            (Exit(Emphasis), "_"),
            (Str, " "),
        );
    }

    #[test]
    fn attr() {
        test_parse!(
            "word{a=b}",
            (
                Attributes {
                    container: false,
                    attrs: 0,
                },
                "{a=b}"
            ),
            (Enter(Span), ""),
            (Str, "word"),
            (Exit(Span), ""),
        );
        test_parse!(
            "some word{.a}{.b} with attrs",
            (Str, "some "),
            (
                Attributes {
                    container: false,
                    attrs: 0,
                },
                "{.a}{.b}"
            ),
            (Enter(Span), ""),
            (Str, "word"),
            (Exit(Span), ""),
            (Str, " with attrs"),
        );
    }

    #[test]
    fn attr_whitespace() {
        test_parse!("word {%comment%}", (Str, "word "));
        test_parse!("word {%comment%} word", (Str, "word "), (Str, " word"));
        test_parse!("word {a=b}", (Str, "word "));
        test_parse!("word {.d}", (Str, "word "));
    }

    #[test]
    fn attr_empty() {
        test_parse!("word{}", (Str, "word"));
        test_parse!("word{ % comment % } trail", (Str, "word"), (Str, " trail"));
    }

    #[test]
    fn quote() {
        test_parse!(
            "'a'",
            (
                Atom(Quote {
                    ty: QuoteType::Single,
                    left: true,
                }),
                "'",
            ),
            (Str, "a"),
            (
                Atom(Quote {
                    ty: QuoteType::Single,
                    left: false,
                }),
                "'",
            ),
        );
        test_parse!(
            " 'a' ",
            (Str, " "),
            (
                Atom(Quote {
                    ty: QuoteType::Single,
                    left: true,
                }),
                "'",
            ),
            (Str, "a"),
            (
                Atom(Quote {
                    ty: QuoteType::Single,
                    left: false,
                }),
                "'",
            ),
            (Str, " "),
        );
    }
}
