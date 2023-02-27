use crate::attr;
use crate::lex;
use crate::Span;

use lex::Delimiter;
use lex::Sequence;
use lex::Symbol;

use Atom::*;
use Container::*;

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
pub enum Container {
    Span,
    Subscript,
    Superscript,
    Insert,
    Delete,
    Emphasis,
    Strong,
    Mark,
    Verbatim,
    /// Span is the format.
    RawFormat,
    InlineMath,
    DisplayMath,
    /// Span is the reference link tag.
    ReferenceLink,
    /// Span is the reference link tag.
    ReferenceImage,
    /// Span is the URL.
    InlineLink,
    /// Span is the URL.
    InlineImage,
    /// Open delimiter span is URL, closing is '>'.
    Autolink,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuoteType {
    Single,
    Double,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EventKind {
    Enter(Container),
    Exit(Container),
    Atom(Atom),
    Str,
    Whitespace,
    Attributes,
    Placeholder,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    pub kind: EventKind,
    pub span: Span,
}

#[derive(Clone)]
struct Input<'s> {
    src: &'s str,
    /// Lexer.
    lexer: lex::Lexer<'s>,
    /// The block is complete, the final line has been provided.
    complete: bool,
    /// Span of current event.
    span: Span,
}

impl<'s> Input<'s> {
    fn new(src: &'s str) -> Self {
        Self {
            src,
            lexer: lex::Lexer::new(""),
            complete: false,
            span: Span::empty_at(0),
        }
    }

    fn feed_line(&mut self, line: Span, last: bool) {
        debug_assert!(!self.complete);
        self.lexer = lex::Lexer::new(line.of(self.src));
        self.complete = last;
        self.span = line.empty_before();
    }

    fn reset(&mut self) {
        *self = Self::new(self.src);
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

    fn ahead_attributes(&mut self) -> Option<(bool, Span)> {
        let mut span = self.span.empty_after();
        let mut ahead = self.lexer.ahead().chars();
        let (mut attr_len, mut has_attr) = attr::valid(&mut ahead);
        if attr_len > 0 {
            while attr_len > 0 {
                span = span.extend(attr_len);
                self.lexer = lex::Lexer::new(ahead.as_str());

                let (l, non_empty) = attr::valid(&mut ahead);
                has_attr |= non_empty;
                attr_len = l;
            }
            Some((has_attr, span))
        } else {
            None
        }
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
pub struct Parser<'s> {
    input: Input<'s>,
    /// Stack with kind and index of _potential_ openers for containers.
    openers: Vec<(Opener, usize)>,
    /// Buffer queue for next events. Events are buffered until no modifications due to future
    /// characters are needed.
    events: std::collections::VecDeque<Event>,
    /// State if inside a verbatim container.
    verbatim: Option<VerbatimState>,
}

impl<'s> Parser<'s> {
    pub fn new(src: &'s str) -> Self {
        Self {
            input: Input::new(src),
            openers: Vec::new(),
            events: std::collections::VecDeque::new(),
            verbatim: None,
        }
    }

    pub fn feed_line(&mut self, line: Span, last: bool) {
        self.input.feed_line(line, last);
    }

    pub fn reset(&mut self) {
        debug_assert!(self.events.is_empty());
        self.input.reset();
        self.openers.clear();
        debug_assert!(self.events.is_empty());
        debug_assert!(self.verbatim.is_none());
    }

    fn push_sp(&mut self, kind: EventKind, span: Span) -> Option<()> {
        self.events.push_back(Event { kind, span });
        Some(())
    }

    fn push(&mut self, kind: EventKind) -> Option<()> {
        self.push_sp(kind, self.input.span)
    }

    fn parse_event(&mut self) -> Option<()> {
        self.input.reset_span();
        self.input.eat().map(|first| {
            self.parse_verbatim(&first)
                .or_else(|| self.parse_attributes(&first))
                .or_else(|| self.parse_autolink(&first))
                .or_else(|| self.parse_symbol(&first))
                .or_else(|| self.parse_footnote_reference(&first))
                .or_else(|| self.parse_container(&first))
                .or_else(|| self.parse_atom(&first))
                .unwrap_or_else(|| {
                    self.push(if matches!(first.kind, lex::Kind::Whitespace) {
                        EventKind::Whitespace
                    } else {
                        EventKind::Str
                    });
                })
        })
    }

    fn parse_verbatim(&mut self, first: &lex::Token) -> Option<()> {
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
                let mut span_closer = self.input.span;
                if let Some(span_format) = raw_format {
                    self.events[event_opener].kind = EventKind::Enter(RawFormat);
                    self.events[event_opener].span = span_format;
                    self.input.span = span_format.translate(1);
                    span_closer = span_format;
                } else if let Some((non_empty, span_attr)) = self.input.ahead_attributes() {
                    if non_empty {
                        let e_attr = event_opener - 1;
                        self.events[e_attr] = Event {
                            kind: EventKind::Attributes,
                            span: span_attr,
                        };
                    }
                    self.input.span = span_attr;
                };
                let ty_opener = if let EventKind::Enter(ty) = self.events[event_opener].kind {
                    debug_assert!(matches!(
                        ty,
                        Verbatim | RawFormat | InlineMath | DisplayMath
                    ));
                    ty
                } else {
                    panic!()
                };
                if let Some((lex::Kind::Seq(Sequence::Backtick), event_skip)) = non_whitespace_last
                {
                    self.events.drain(*event_skip..);
                }
                self.push_sp(EventKind::Exit(ty_opener), span_closer);
                self.verbatim = None;
            } else {
                // continue verbatim
                if matches!(first.kind, lex::Kind::Whitespace) {
                    if !*non_whitespace_encountered
                        && self.input.peek().map_or(false, |t| {
                            matches!(
                                t.kind,
                                lex::Kind::Seq(Sequence::Backtick) if t.len != len_opener.into(),
                            )
                        })
                    {
                        return Some(()); // skip whitespace
                    }
                } else {
                    *non_whitespace_encountered = true;
                    *non_whitespace_last = Some((first.kind, self.events.len() + 1));
                }
                self.push(EventKind::Str);
            };
            Some(())
        } else {
            let (ty, len_opener) = match first.kind {
                lex::Kind::DollarBacktick(l) if first.len - l as usize == 1 => {
                    Some((InlineMath, l))
                }
                lex::Kind::DollarBacktick(l) if first.len - l as usize == 2 => {
                    Some((DisplayMath, l))
                }
                lex::Kind::Seq(Sequence::Backtick) if first.len < 256 => {
                    Some((Verbatim, first.len as u8))
                }
                _ => None,
            }?;
            self.push_sp(EventKind::Placeholder, self.input.span.empty_before());
            self.verbatim = Some(VerbatimState {
                event_opener: self.events.len(),
                len_opener,
                non_whitespace_encountered: false,
                non_whitespace_last: None,
            });
            self.push(EventKind::Enter(ty))
        }
    }

    fn parse_attributes(&mut self, first: &lex::Token) -> Option<()> {
        if first.kind == lex::Kind::Open(Delimiter::Brace) {
            let mut ahead = self.input.lexer.ahead().chars();
            let (mut attr_len, mut has_attr) = attr::valid(std::iter::once('{').chain(&mut ahead));
            attr_len = attr_len.saturating_sub(1); // rm {
            if attr_len > 0 {
                while attr_len > 0 {
                    self.input.span = self.input.span.extend(attr_len);
                    self.input.lexer = lex::Lexer::new(ahead.as_str());

                    let (l, non_empty) = attr::valid(&mut ahead);
                    attr_len = l;
                    has_attr |= non_empty;
                }

                let set_attr = has_attr
                    && self
                        .events
                        .back()
                        .map_or(false, |e| e.kind == EventKind::Str);

                if set_attr {
                    let i = self
                        .events
                        .iter()
                        .rposition(|e| e.kind != EventKind::Str)
                        .map_or(0, |i| i + 1);
                    let span_str = self.events[i]
                        .span
                        .union(self.events[self.events.len() - 1].span);
                    self.events.drain(i..);

                    self.push(EventKind::Attributes);
                    self.push_sp(EventKind::Enter(Span), span_str.empty_before());
                    self.push_sp(EventKind::Str, span_str);
                    self.push_sp(EventKind::Exit(Span), span_str.empty_after());
                } else {
                    self.push_sp(EventKind::Placeholder, self.input.span.empty_before());
                }
                return Some(());
            }
        }

        None
    }

    fn parse_autolink(&mut self, first: &lex::Token) -> Option<()> {
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
                self.input.span = self.input.span.after(1);
                return self.push(EventKind::Exit(Autolink));
            }
        }
        None
    }

    fn parse_symbol(&mut self, first: &lex::Token) -> Option<()> {
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
                return Some(());
            }
        }
        None
    }

    fn parse_footnote_reference(&mut self, first: &lex::Token) -> Option<()> {
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
                return Some(());
            }
        }
        None
    }

    fn parse_container(&mut self, first: &lex::Token) -> Option<()> {
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

                if e_opener == self.events.len() - 1 && !matches!(opener, Opener::Link { .. }) {
                    // empty container
                    return None;
                }
                let whitespace_after = self.events.back().map_or(false, |ev| {
                    matches!(ev.kind, EventKind::Whitespace | EventKind::Atom(Softbreak))
                });
                if opener.bidirectional() && whitespace_after {
                    return None;
                }

                self.openers.drain(o..);
                let mut closed = match DelimEventKind::from(opener) {
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
                        };
                        None
                    }
                    DelimEventKind::Link {
                        event_span,
                        inline,
                        image,
                    } => {
                        let span_spec = self.events[e_opener].span.between(self.input.span);
                        let span_spec = if !inline && span_spec.is_empty() {
                            self.events[event_span]
                                .span
                                .between(self.events[e_opener - 1].span)
                        } else {
                            span_spec
                        };
                        let container = match (image, inline) {
                            (false, false) => ReferenceLink,
                            (false, true) => InlineLink,
                            (true, false) => ReferenceImage,
                            (true, true) => InlineImage,
                        };
                        self.events[event_span] = Event {
                            kind: EventKind::Enter(container),
                            span: span_spec,
                        };
                        self.events[e_opener - 1] = Event {
                            kind: EventKind::Exit(container),
                            span: span_spec,
                        };
                        self.events.drain(e_opener..);
                        Some(())
                    }
                };

                if let Some((non_empty, span)) = self.input.ahead_attributes() {
                    if non_empty {
                        self.events[e_attr] = Event {
                            kind: EventKind::Attributes,
                            span,
                        };
                    }

                    if closed.is_none() {
                        self.events[e_opener].kind = EventKind::Enter(Container::Span);
                        closed = self.push(EventKind::Exit(Container::Span));
                    }

                    self.input.span = span;
                }

                closed
            })
            .or_else(|| {
                let opener = Opener::from_token(first.kind)?;
                if opener.bidirectional()
                    && self
                        .input
                        .peek()
                        .map_or(true, |t| matches!(t.kind, lex::Kind::Whitespace))
                {
                    return None;
                }
                if matches!(opener, Opener::SingleQuoted | Opener::DoubleQuoted)
                    && self
                        .events
                        .back()
                        .map_or(false, |ev| matches!(ev.kind, EventKind::Str))
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

    fn parse_atom(&mut self, first: &lex::Token) -> Option<()> {
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
                return Some(());
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

    fn merge_str_events(&mut self, span_str: Span) -> Event {
        let mut span = span_str;
        let should_merge = |e: &Event, span: Span| {
            matches!(
                e.kind,
                EventKind::Str | EventKind::Whitespace | EventKind::Placeholder
            ) && span.end() == e.span.start()
        };
        while self.events.front().map_or(false, |e| should_merge(e, span)) {
            let ev = self.events.pop_front().unwrap();
            span = span.union(ev.span);
        }
        Event {
            kind: EventKind::Str,
            span,
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

enum DelimEventKind {
    Container(Container),
    Span(SpanType),
    Quote(QuoteType),
    Link {
        event_span: usize,
        image: bool,
        inline: bool,
    },
}

impl From<Opener> for DelimEventKind {
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
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while self.events.is_empty()
            || !self.openers.is_empty()
            || self.verbatim.is_some()
            || self // for merge or attributes
                .events
                .back()
                .map_or(false, |ev| {
                    matches!(ev.kind, EventKind::Str | EventKind::Whitespace)
                })
        {
            if self.parse_event().is_none() {
                if self.input.complete {
                    break;
                } else {
                    return None;
                }
            }
        }

        // automatically close unclosed verbatim
        if let Some(VerbatimState { event_opener, .. }) = self.verbatim.take() {
            let ty_opener = if let EventKind::Enter(ty) = self.events[event_opener].kind {
                debug_assert!(matches!(
                    ty,
                    Verbatim | RawFormat | InlineMath | DisplayMath
                ));
                ty
            } else {
                panic!()
            };
            self.push(EventKind::Exit(ty_opener));
        }

        self.events.pop_front().and_then(|e| match e.kind {
            EventKind::Str if e.span.is_empty() => self.next(),
            EventKind::Str | EventKind::Whitespace => Some(self.merge_str_events(e.span)),
            EventKind::Placeholder => self.next(),
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
            (Attributes, "{#id}"),
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
            (Enter(RawFormat), "format"),
            (Str, "raw"),
            (Exit(RawFormat), "format"),
        );
        test_parse!(
            "before `raw`{=format} after",
            (Str, "before "),
            (Enter(RawFormat), "format"),
            (Str, "raw"),
            (Exit(RawFormat), "format"),
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
            (Enter(ReferenceLink), "tag"),
            (Str, "text"),
            (Exit(ReferenceLink), "tag"),
        );
        test_parse!(
            "![text][tag]",
            (Enter(ReferenceImage), "tag"),
            (Str, "text"),
            (Exit(ReferenceImage), "tag"),
        );
        test_parse!(
            "before [text][tag] after",
            (Str, "before "),
            (Enter(ReferenceLink), "tag"),
            (Str, "text"),
            (Exit(ReferenceLink), "tag"),
            (Str, " after"),
        );
        test_parse!(
            "[[inner][i]][o]",
            (Enter(ReferenceLink), "o"),
            (Enter(ReferenceLink), "i"),
            (Str, "inner"),
            (Exit(ReferenceLink), "i"),
            (Exit(ReferenceLink), "o"),
        );
    }

    #[test]
    fn span_tag_empty() {
        test_parse!(
            "[text][]",
            (Enter(ReferenceLink), "text"),
            (Str, "text"),
            (Exit(ReferenceLink), "text"),
        );
        test_parse!(
            "![text][]",
            (Enter(ReferenceImage), "text"),
            (Str, "text"),
            (Exit(ReferenceImage), "text"),
        );
    }

    #[test]
    fn span_tag_empty_nested() {
        // TODO strip non str from tag?
        test_parse!(
            "[some _text_][]",
            (Enter(ReferenceLink), "some _text_"),
            (Str, "some "),
            (Enter(Emphasis), "_"),
            (Str, "text"),
            (Exit(Emphasis), "_"),
            (Exit(ReferenceLink), "some _text_"),
        );
    }

    #[test]
    fn span_url() {
        test_parse!(
            "before [text](url) after",
            (Str, "before "),
            (Enter(InlineLink), "url"),
            (Str, "text"),
            (Exit(InlineLink), "url"),
            (Str, " after"),
        );
        test_parse!(
            "[outer [inner](i)](o)",
            (Enter(InlineLink), "o"),
            (Str, "outer "),
            (Enter(InlineLink), "i"),
            (Str, "inner"),
            (Exit(InlineLink), "i"),
            (Exit(InlineLink), "o"),
        );
    }

    #[test]
    fn span_url_attr_unclosed() {
        test_parse!(
            "[text]({.cls}",
            (Attributes, "{.cls}"),
            (Enter(Span), ""),
            (Str, "[text]("),
            (Exit(Span), ""),
        );
    }

    #[ignore = "broken"]
    #[test]
    fn span_url_attr_closed() {
        test_parse!(
            "[text]({.cls})",
            (Enter(InlineLink), "{.cls}"),
            (Str, "text"),
            (Exit(InlineLink), "{.cls}"),
        );
    }

    #[test]
    fn span_url_empty() {
        test_parse!(
            "before [text]() after",
            (Str, "before "),
            (Enter(InlineLink), ""),
            (Str, "text"),
            (Exit(InlineLink), ""),
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
    fn span_attr() {
        test_parse!(
            "[abc]{.def}",
            (Attributes, "{.def}"),
            (Enter(Span), "["),
            (Str, "abc"),
            (Exit(Span), "]"),
        );
        test_parse!("not a [span] {#id}.", (Str, "not a [span] "), (Str, "."));
    }

    #[test]
    fn autolink() {
        test_parse!(
            "<https://example.com>",
            (Enter(Autolink), "https://example.com"),
            (Str, "https://example.com"),
            (Exit(Autolink), ">")
        );
        test_parse!(
            "<a@b.c>",
            (Enter(Autolink), "a@b.c"),
            (Str, "a@b.c"),
            (Exit(Autolink), ">"),
        );
        test_parse!(
            "<http://a.b><http://c.d>",
            (Enter(Autolink), "http://a.b"),
            (Str, "http://a.b"),
            (Exit(Autolink), ">"),
            (Enter(Autolink), "http://c.d"),
            (Str, "http://c.d"),
            (Exit(Autolink), ">")
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
            (Attributes, "{.attr}"),
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
            (Attributes, "{.a}{.b}{.c}"),
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
            (Attributes, "{a=b}"),
            (Enter(Span), ""),
            (Str, "word"),
            (Exit(Span), ""),
        );
        test_parse!(
            "some word{.a}{.b} with attrs",
            (Str, "some "),
            (Attributes, "{.a}{.b}"),
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
