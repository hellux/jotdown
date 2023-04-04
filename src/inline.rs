use crate::attr;
use crate::lex;
use crate::Span;

use lex::Delimiter;
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

pub struct Parser<I: Iterator + Clone> {
    /// Lexer, hosting upcoming source.
    lexer: lex::Lexer<I>,
    /// Span of current event.
    span: Span,
    /// Stack with kind and index of _potential_ openers for containers.
    openers: Vec<(Delim, usize)>,
    /// Buffer queue for next events. Events are buffered until no modifications due to future
    /// characters are needed.
    events: std::collections::VecDeque<Event>,
}

impl<I: Iterator<Item = char> + Clone> Parser<I> {
    pub fn new(chars: I) -> Self {
        Self {
            lexer: lex::Lexer::new(chars),
            span: Span::new(0, 0),
            openers: Vec::new(),
            events: std::collections::VecDeque::new(),
        }
    }

    pub fn reset(&mut self, chars: I) {
        self.lexer = lex::Lexer::new(chars);
        self.span = Span::new(0, 0);
        self.openers.clear();
        debug_assert!(self.events.is_empty());
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

    fn push_sp(&mut self, kind: EventKind, span: Span) -> Option<()> {
        self.events.push_back(Event { kind, span });
        Some(())
    }

    fn push(&mut self, kind: EventKind) -> Option<()> {
        self.push_sp(kind, self.span)
    }

    fn parse_event(&mut self) -> Option<()> {
        self.reset_span();
        self.eat().map(|first| {
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
        match first.kind {
            lex::Kind::Seq(lex::Sequence::Dollar) => {
                let math_opt = (first.len <= 2)
                    .then(|| {
                        if let Some(lex::Token {
                            kind: lex::Kind::Seq(lex::Sequence::Backtick),
                            len,
                        }) = self.peek()
                        {
                            Some((
                                if first.len == 2 {
                                    DisplayMath
                                } else {
                                    InlineMath
                                },
                                *len,
                            ))
                        } else {
                            None
                        }
                    })
                    .flatten();
                if math_opt.is_some() {
                    self.eat(); // backticks
                }
                math_opt
            }
            lex::Kind::Seq(lex::Sequence::Backtick) => Some((Verbatim, first.len)),
            _ => None,
        }
        .map(|(mut kind, opener_len)| {
            let e_attr = self.events.len();
            self.push_sp(EventKind::Placeholder, Span::empty_at(self.span.start()));
            let opener_event = self.events.len();
            self.push(EventKind::Enter(kind));

            let mut span_inner = self.span.empty_after();
            let mut span_outer = None;

            let mut non_whitespace_first = None;
            let mut non_whitespace_last = None;

            while let Some(t) = self.eat() {
                if matches!(t.kind, lex::Kind::Seq(lex::Sequence::Backtick)) && t.len == opener_len
                {
                    if matches!(kind, Verbatim)
                        && matches!(
                            self.lexer.peek().map(|t| &t.kind),
                            Some(lex::Kind::Open(Delimiter::BraceEqual))
                        )
                    {
                        let mut ahead = self.lexer.chars();
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
                        if len > 0 && end {
                            let tok = self.eat();
                            debug_assert_eq!(
                                tok,
                                Some(lex::Token {
                                    kind: lex::Kind::Open(Delimiter::BraceEqual),
                                    len: 2,
                                })
                            );
                            self.lexer = lex::Lexer::new(ahead);
                            let span_format = self.span.after(len);
                            kind = RawFormat;
                            self.events[opener_event].kind = EventKind::Enter(kind);
                            self.events[opener_event].span = span_format;
                            self.span = span_format.translate(1); // }
                            span_outer = Some(span_format);
                        }
                    }
                    break;
                }
                if !matches!(t.kind, lex::Kind::Whitespace) {
                    if non_whitespace_first.is_none() {
                        non_whitespace_first = Some((t.kind, span_inner.end()));
                    }
                    non_whitespace_last = Some((t.kind, span_inner.end() + t.len));
                }
                span_inner = span_inner.extend(t.len);
                self.reset_span();
            }

            if let Some((lex::Kind::Seq(lex::Sequence::Backtick), pos)) = non_whitespace_first {
                span_inner = span_inner.with_start(pos);
            }
            if let Some((lex::Kind::Seq(lex::Sequence::Backtick), pos)) = non_whitespace_last {
                span_inner = span_inner.with_end(pos);
            }

            self.push_sp(EventKind::Str, span_inner);
            self.push_sp(EventKind::Exit(kind), span_outer.unwrap_or(self.span));

            if let Some((non_empty, span)) = self.ahead_attributes() {
                self.span = span;
                if non_empty {
                    self.events[e_attr] = Event {
                        kind: EventKind::Attributes,
                        span,
                    };
                }
            }
        })
    }

    fn parse_attributes(&mut self, first: &lex::Token) -> Option<()> {
        if first.kind == lex::Kind::Open(Delimiter::Brace) {
            let mut ahead = self.lexer.chars();
            let (mut attr_len, mut has_attr) = attr::valid(std::iter::once('{').chain(&mut ahead));
            attr_len = attr_len.saturating_sub(1); // rm {
            if attr_len > 0 {
                while attr_len > 0 {
                    self.span = self.span.extend(attr_len);
                    self.lexer = lex::Lexer::new(ahead.clone());

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
                    self.push_sp(EventKind::Enter(Container::Span), span_str.empty_before());
                    self.push_sp(EventKind::Str, span_str);

                    return self.push_sp(EventKind::Exit(Container::Span), span_str.empty_after());
                } else {
                    return self.push_sp(EventKind::Placeholder, self.span.empty_before());
                }
            }
        }

        None
    }

    fn parse_autolink(&mut self, first: &lex::Token) -> Option<()> {
        if first.kind == lex::Kind::Sym(Symbol::Lt) {
            let mut ahead = self.lexer.chars();
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
                self.lexer = lex::Lexer::new(ahead);
                self.span = self.span.after(len);
                self.push(EventKind::Enter(Autolink));
                self.push(EventKind::Str);
                self.span = self.span.after(1);
                return self.push(EventKind::Exit(Autolink));
            }
        }
        None
    }

    fn parse_symbol(&mut self, first: &lex::Token) -> Option<()> {
        if first.kind == lex::Kind::Sym(Symbol::Colon) {
            let mut ahead = self.lexer.chars();
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
                self.lexer = lex::Lexer::new(ahead);
                self.span = self.span.after(len);
                let span = self.span;
                self.span = self.span.after(1);
                return self.push_sp(EventKind::Atom(Symbol), span);
            }
        }
        None
    }

    fn parse_footnote_reference(&mut self, first: &lex::Token) -> Option<()> {
        if first.kind == lex::Kind::Open(Delimiter::Bracket)
            && matches!(
                self.peek(),
                Some(lex::Token {
                    kind: lex::Kind::Sym(Symbol::Caret),
                    ..
                })
            )
        {
            let tok = self.eat();
            debug_assert_eq!(
                tok,
                Some(lex::Token {
                    kind: lex::Kind::Sym(Symbol::Caret),
                    len: 1,
                })
            );
            let mut ahead = self.lexer.chars();
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
                self.lexer = lex::Lexer::new(ahead);
                self.span = self.span.after(len);
                self.push(EventKind::Atom(FootnoteReference));
                self.span = self.span.after(1);
                return Some(());
            }
        }
        None
    }

    fn parse_container(&mut self, first: &lex::Token) -> Option<()> {
        Delim::from_token(first.kind).and_then(|(delim, dir)| {
            self.openers
                .iter()
                .rposition(|(d, _)| {
                    *d == delim || matches!((d, delim), (Delim::Span(..), Delim::Span(..)))
                })
                .and_then(|o| {
                    if matches!(dir, Dir::Open) {
                        return None;
                    }
                    let whitespace_after = self.events.back().map_or(false, |ev| {
                        matches!(ev.kind, EventKind::Whitespace | EventKind::Atom(Softbreak))
                    });
                    if matches!(dir, Dir::Both) && whitespace_after {
                        return None;
                    }

                    let (d, e) = self.openers[o];
                    let e_attr = e;
                    let e_opener = e + 1;
                    if e_opener == self.events.len() - 1 {
                        // empty container
                        return None;
                    }

                    let inner_span = self.events[e_opener].span.between(self.span);
                    let mut closed = match DelimEventKind::from(d) {
                        DelimEventKind::Container(cont) => {
                            self.events[e_opener].kind = EventKind::Enter(cont);
                            self.push(EventKind::Exit(cont))
                        }
                        DelimEventKind::Quote(ty) => {
                            self.events[e_opener].kind =
                                EventKind::Atom(Atom::Quote { ty, left: true });
                            self.push(EventKind::Atom(Atom::Quote { ty, left: false }))
                        }
                        DelimEventKind::Span(ty) => self.post_span(ty, e_opener),
                    };
                    self.openers.drain(o..);

                    if closed.is_some() {
                        let event_closer = &mut self.events.back_mut().unwrap();
                        if event_closer.span.is_empty()
                            && matches!(
                                event_closer.kind,
                                EventKind::Exit(
                                    Container::ReferenceLink | Container::ReferenceImage
                                )
                            )
                        {
                            event_closer.span = inner_span;
                            self.events[e_opener].span = inner_span;
                        }
                    }

                    if let Some((non_empty, span)) = self.ahead_attributes() {
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

                        self.span = span;
                    }

                    closed
                })
                .or_else(|| {
                    if matches!(dir, Dir::Close) {
                        return None;
                    }
                    if matches!(dir, Dir::Both)
                        && self
                            .peek()
                            .map_or(true, |t| matches!(t.kind, lex::Kind::Whitespace))
                    {
                        return None;
                    }
                    if matches!(delim, Delim::SingleQuoted | Delim::DoubleQuoted)
                        && self
                            .events
                            .back()
                            .map_or(false, |ev| matches!(ev.kind, EventKind::Str))
                    {
                        return None;
                    }
                    self.openers.push((delim, self.events.len()));
                    // push dummy event in case attributes are encountered after closing delimiter
                    self.push_sp(EventKind::Placeholder, Span::empty_at(self.span.start()));
                    // use non-opener for now, replace if closed later
                    self.push(match delim {
                        Delim::SingleQuoted => EventKind::Atom(Quote {
                            ty: QuoteType::Single,
                            left: false,
                        }),
                        Delim::DoubleQuoted => EventKind::Atom(Quote {
                            ty: QuoteType::Double,
                            left: true,
                        }),
                        _ => EventKind::Str,
                    })
                })
        })
    }

    fn ahead_attributes(&mut self) -> Option<(bool, Span)> {
        let mut span = self.span.empty_after();
        let mut ahead = self.lexer.chars();
        let (mut attr_len, mut has_attr) = attr::valid(&mut ahead);
        if attr_len > 0 {
            while attr_len > 0 {
                span = span.extend(attr_len);
                self.lexer = lex::Lexer::new(ahead.clone());

                let (l, non_empty) = attr::valid(&mut ahead);
                has_attr |= non_empty;
                attr_len = l;
            }
            Some((has_attr, span))
        } else {
            None
        }
    }

    fn post_span(&mut self, ty: SpanType, opener_event: usize) -> Option<()> {
        let mut ahead = self.lexer.chars();
        match ahead.next() {
            Some(opener @ ('[' | '(')) => {
                let img = ty == SpanType::Image;
                let (closer, kind) = match opener {
                    '[' => (']', if img { ReferenceImage } else { ReferenceLink }),
                    '(' => (')', if img { InlineImage } else { InlineLink }),
                    _ => unreachable!(),
                };
                let mut end = false;
                let len = (&mut ahead)
                    .take_while(|c| {
                        if *c == opener {
                            return false;
                        }
                        if *c == closer {
                            end = true;
                        };
                        !end
                    })
                    .map(char::len_utf8)
                    .sum();
                end.then(|| {
                    let span = self.span.after(len).translate(1);
                    (kind, span)
                })
            }
            _ => None,
        }
        .map(|(kind, span)| {
            self.lexer = lex::Lexer::new(ahead);
            self.events[opener_event].kind = EventKind::Enter(kind);
            self.events[opener_event].span = span;
            self.span = span.translate(1);
            self.push_sp(EventKind::Exit(kind), span);
        })
    }

    fn parse_atom(&mut self, first: &lex::Token) -> Option<()> {
        let atom =
            match first.kind {
                lex::Kind::Newline => Softbreak,
                lex::Kind::Hardbreak => Hardbreak,
                lex::Kind::Escape => Escape,
                lex::Kind::Nbsp => Nbsp,
                lex::Kind::Seq(lex::Sequence::Period) if first.len >= 3 => {
                    while self.span.len() > 3 {
                        self.push_sp(EventKind::Atom(Ellipsis), self.span.with_len(3));
                        self.span = self.span.skip(3);
                    }
                    if self.span.len() == 3 {
                        Ellipsis
                    } else {
                        return self.push(EventKind::Str);
                    }
                }
                lex::Kind::Seq(lex::Sequence::Hyphen) if first.len >= 2 => {
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
                            self.push_sp(EventKind::Atom(atom), self.span.with_len(l));
                            self.span = self.span.skip(l);
                        });
                    return Some(());
                }
                lex::Kind::Open(lex::Delimiter::BraceQuote1) => Quote {
                    ty: QuoteType::Single,
                    left: true,
                },
                lex::Kind::Sym(lex::Symbol::Quote1)
                | lex::Kind::Close(lex::Delimiter::BraceQuote1) => Quote {
                    ty: QuoteType::Single,
                    left: false,
                },
                lex::Kind::Open(lex::Delimiter::BraceQuote2) => Quote {
                    ty: QuoteType::Double,
                    left: true,
                },
                lex::Kind::Sym(lex::Symbol::Quote2)
                | lex::Kind::Close(lex::Delimiter::BraceQuote2) => Quote {
                    ty: QuoteType::Double,
                    left: false,
                },
                _ => return None,
            };

        self.push(EventKind::Atom(atom))
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
enum Delim {
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
}

#[derive(Debug, Clone, Copy)]
enum Dir {
    Open,
    Close,
    Both,
}

impl Delim {
    fn from_token(kind: lex::Kind) -> Option<(Self, Dir)> {
        use Delim::*;
        use Dir::{Both, Close, Open};
        use Directionality::{Bi, Uni};
        use SpanType::{General, Image};

        match kind {
            lex::Kind::Sym(Symbol::Asterisk) => Some((Strong(Bi), Both)),
            lex::Kind::Sym(Symbol::Underscore) => Some((Emphasis(Bi), Both)),
            lex::Kind::Sym(Symbol::Caret) => Some((Superscript(Bi), Both)),
            lex::Kind::Sym(Symbol::Tilde) => Some((Subscript(Bi), Both)),
            lex::Kind::Sym(Symbol::Quote1) => Some((SingleQuoted, Both)),
            lex::Kind::Sym(Symbol::Quote2) => Some((DoubleQuoted, Both)),
            lex::Kind::Sym(Symbol::ExclaimBracket) => Some((Span(Image), Open)),
            lex::Kind::Open(Delimiter::Bracket) => Some((Span(General), Open)),
            lex::Kind::Close(Delimiter::Bracket) => Some((Span(General), Close)),
            lex::Kind::Open(Delimiter::BraceAsterisk) => Some((Strong(Uni), Open)),
            lex::Kind::Close(Delimiter::BraceAsterisk) => Some((Strong(Uni), Close)),
            lex::Kind::Open(Delimiter::BraceUnderscore) => Some((Emphasis(Uni), Open)),
            lex::Kind::Close(Delimiter::BraceUnderscore) => Some((Emphasis(Uni), Close)),
            lex::Kind::Open(Delimiter::BraceCaret) => Some((Superscript(Uni), Open)),
            lex::Kind::Close(Delimiter::BraceCaret) => Some((Superscript(Uni), Close)),
            lex::Kind::Open(Delimiter::BraceTilde) => Some((Subscript(Uni), Open)),
            lex::Kind::Close(Delimiter::BraceTilde) => Some((Subscript(Uni), Close)),
            lex::Kind::Open(Delimiter::BraceEqual) => Some((Mark, Open)),
            lex::Kind::Close(Delimiter::BraceEqual) => Some((Mark, Close)),
            lex::Kind::Open(Delimiter::BraceHyphen) => Some((Delete, Open)),
            lex::Kind::Close(Delimiter::BraceHyphen) => Some((Delete, Close)),
            lex::Kind::Open(Delimiter::BracePlus) => Some((Insert, Open)),
            lex::Kind::Close(Delimiter::BracePlus) => Some((Insert, Close)),
            lex::Kind::Open(Delimiter::BraceQuote1) => Some((SingleQuoted, Open)),
            lex::Kind::Close(Delimiter::BraceQuote1) => Some((SingleQuoted, Close)),
            lex::Kind::Open(Delimiter::BraceQuote2) => Some((DoubleQuoted, Open)),
            lex::Kind::Close(Delimiter::BraceQuote2) => Some((DoubleQuoted, Close)),
            _ => None,
        }
    }
}

enum DelimEventKind {
    Container(Container),
    Span(SpanType),
    Quote(QuoteType),
}

impl From<Delim> for DelimEventKind {
    fn from(d: Delim) -> Self {
        match d {
            Delim::Span(ty) => Self::Span(ty),
            Delim::Strong(..) => Self::Container(Strong),
            Delim::Emphasis(..) => Self::Container(Emphasis),
            Delim::Superscript(..) => Self::Container(Superscript),
            Delim::Subscript(..) => Self::Container(Subscript),
            Delim::Mark => Self::Container(Mark),
            Delim::Delete => Self::Container(Delete),
            Delim::Insert => Self::Container(Insert),
            Delim::SingleQuoted => Self::Quote(QuoteType::Single),
            Delim::DoubleQuoted => Self::Quote(QuoteType::Double),
        }
    }
}

impl<I: Iterator<Item = char> + Clone> Iterator for Parser<I> {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        while self.events.is_empty()
            || !self.openers.is_empty()
            || self // for merge or attributes
                .events
                .back()
                .map_or(false, |ev| {
                    matches!(ev.kind, EventKind::Str | EventKind::Whitespace)
                })
        {
            if self.parse_event().is_none() {
                break;
            }
        }

        self.events.pop_front().and_then(|e| {
            match e.kind {
                EventKind::Str if e.span.is_empty() => self.next(),
                EventKind::Str | EventKind::Whitespace => {
                    // merge str events
                    let mut span = e.span;
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
                    Some(Event {
                        kind: EventKind::Str,
                        span,
                    })
                }
                EventKind::Placeholder => self.next(),
                _ => Some(e),
            }
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
            let mut p = super::Parser::new($src.chars());
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
