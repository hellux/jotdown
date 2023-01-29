use crate::CowStr;

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Span {
    start: u32,
    end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self::by_len(start, end.checked_sub(start).unwrap())
    }

    pub fn by_len(start: usize, len: usize) -> Self {
        Self {
            start: start.try_into().unwrap(),
            end: start.checked_add(len).unwrap().try_into().unwrap(),
        }
    }

    pub fn empty_at(start: usize) -> Self {
        Self::by_len(start, 0)
    }

    pub fn empty_before(self) -> Self {
        Self::empty_at(self.start())
    }

    pub fn empty_after(self) -> Self {
        Self::empty_at(self.end())
    }

    pub fn with_start(self, start: usize) -> Self {
        Self::new(start, self.end())
    }

    pub fn with_end(self, end: usize) -> Self {
        Self::new(self.start(), end)
    }

    pub fn with_len(self, len: usize) -> Self {
        Self::by_len(self.start(), len)
    }

    pub fn after(self, len: usize) -> Self {
        Self::by_len(self.end(), len)
    }

    pub fn union(self, span: Self) -> Self {
        Self::new(self.start(), span.end())
    }

    pub fn between(self, span: Self) -> Self {
        Self::new(self.end(), span.start())
    }

    pub fn skip(self, n: usize) -> Self {
        Self::new(self.start() + n, self.end())
    }

    pub fn extend(self, n: usize) -> Self {
        Self::new(self.start(), self.end() + n)
    }

    pub fn translate(self, n: usize) -> Self {
        Self::new(
            self.start().checked_add(n).unwrap(),
            self.end().checked_add(n).unwrap(),
        )
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub fn start(self) -> usize {
        self.start.try_into().unwrap()
    }

    pub fn end(self) -> usize {
        self.end.try_into().unwrap()
    }

    pub fn len(self) -> usize {
        self.end() - self.start()
    }

    pub fn of(self, s: &str) -> &str {
        &s[self.start()..self.end()]
    }

    pub fn trim_start_matches<P: FnMut(char) -> bool>(self, s: &str, pat: P) -> Self {
        Self::from_slice(s, self.of(s).trim_start_matches(pat))
    }

    pub fn trim_start(self, s: &str) -> Self {
        Self::from_slice(s, self.of(s).trim_start())
    }

    pub fn trim_end(self, s: &str) -> Self {
        Self::from_slice(s, self.of(s).trim_end())
    }

    pub fn trim(self, s: &str) -> Self {
        Self::from_slice(s, self.of(s).trim_start().trim_end())
    }

    fn from_slice(s: &str, slice: &str) -> Self {
        Self::by_len(slice.as_ptr() as usize - s.as_ptr() as usize, slice.len())
    }
}

pub trait DiscontinuousString<'s> {
    type Chars: Iterator<Item = char>;

    fn src(&self, span: Span) -> CowStr<'s>;

    fn chars(&self) -> Self::Chars;
}

impl<'s> DiscontinuousString<'s> for &'s str {
    type Chars = std::str::Chars<'s>;

    fn src(&self, span: Span) -> CowStr<'s> {
        span.of(self).into()
    }

    fn chars(&self) -> Self::Chars {
        str::chars(self)
    }
}

/// Multiple discontinuous [`std::str::Chars`] objects concatenated.
#[derive(Clone)]
pub struct InlineChars<'s, I> {
    src: &'s str,
    inlines: I,
    next: std::str::Chars<'s>,
}

// Implement inlines.flat_map(|sp| sp.of(self.src).chars())
impl<'s, I: Iterator<Item = Span>> InlineChars<'s, I> {
    fn new(src: &'s str, inlines: I) -> Self {
        Self {
            src,
            inlines,
            next: "".chars(),
        }
    }
}

impl<'s, I: Iterator<Item = Span>> Iterator for InlineChars<'s, I> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.as_str().is_empty() {
            self.next = self
                .inlines
                .next()
                .map_or_else(|| "".chars(), |sp| sp.of(self.src).chars());
        }
        self.next.next()
    }
}

pub type InlineCharsIter<'s> = InlineChars<'s, std::iter::Copied<std::slice::Iter<'static, Span>>>;

/// Discontinuous slices of a [`&str`].
#[derive(Default, Debug)]
pub struct InlineSpans<'s> {
    src: &'s str,
    spans: Vec<Span>,
}

impl<'s> InlineSpans<'s> {
    pub fn new(src: &'s str) -> Self {
        Self {
            src,
            spans: Vec::new(),
        }
    }

    pub fn set_spans(&mut self, spans: impl Iterator<Item = Span>) {
        self.spans.clear();
        self.spans.extend(spans);
    }

    pub fn slice<'i>(&'i self, span: Span) -> InlineSpansSlice<'s, 'i> {
        let mut first = 0;
        let mut last = 0;
        let mut first_skip = 0;
        let mut last_len = 0;

        let mut a = 0;
        for (i, sp) in self.spans.iter().enumerate() {
            let b = a + sp.len();
            if span.start() < b {
                if a <= span.start() {
                    first = i;
                    first_skip = span.start() - a;
                    if span.end() <= b {
                        // continuous
                        last = i;
                        last_len = span.len();
                        break;
                    }
                } else {
                    last = i;
                    last_len = sp.len().min(span.end() - a);
                    break;
                };
            }
            a = b;
        }

        assert_ne!(last_len, 0);

        InlineSpansSlice {
            src: self.src,
            first_skip,
            last_len,
            spans: &self.spans[first..=last],
        }
    }

    /// Borrow if continuous, copy if discontiunous.
    fn borrow_or_copy<I: Iterator<Item = Span>>(src: &str, spans: I, span: Span) -> CowStr {
        let mut a = 0;
        let mut s = String::new();
        for sp in spans {
            let b = a + sp.len();
            if span.start() < b {
                let r = if a <= span.start() {
                    if span.end() <= b {
                        // continuous
                        return CowStr::Borrowed(&sp.of(src)[span.start() - a..span.end() - a]);
                    }
                    (span.start() - a)..sp.len()
                } else {
                    0..sp.len().min(span.end() - a)
                };
                s.push_str(&sp.of(src)[r]);
            }
            a = b;
        }
        assert_eq!(span.len(), s.len());
        CowStr::Owned(s)
    }
}

impl<'s> DiscontinuousString<'s> for InlineSpans<'s> {
    type Chars = InlineCharsIter<'s>;

    fn src(&self, span: Span) -> CowStr<'s> {
        Self::borrow_or_copy(self.src, self.spans.iter().copied(), span)
    }

    fn chars(&self) -> Self::Chars {
        // SAFETY: do not call set_spans while chars is in use
        unsafe { std::mem::transmute(InlineChars::new(self.src, self.spans.iter().copied())) }
    }
}

/// A read-only slice of an [`InlineSpans`] object.
pub struct InlineSpansSlice<'s, 'i> {
    src: &'s str,
    first_skip: usize,
    last_len: usize,
    spans: &'i [Span],
}

impl<'s, 'i> InlineSpansSlice<'s, 'i> {
    fn spans(&self) -> InlineSpansSliceIter<'i> {
        let (span_start, r_middle, span_end) = if self.spans.len() == 1 {
            (
                Span::by_len(self.spans[0].start() + self.first_skip, self.last_len),
                0..0,
                Span::by_len(self.spans[self.spans.len() - 1].start(), 0),
            )
        } else {
            (
                Span::new(self.spans[0].start() + self.first_skip, self.spans[0].end()),
                1..self.spans.len().saturating_sub(2),
                Span::by_len(self.spans[self.spans.len() - 1].start(), self.last_len),
            )
        };
        std::iter::once(span_start)
            .chain(self.spans[r_middle].iter().copied())
            .chain(std::iter::once(span_end))
    }
}

impl<'s, 'i> DiscontinuousString<'s> for InlineSpansSlice<'s, 'i> {
    type Chars = InlineChars<'s, InlineSpansSliceIter<'i>>;

    fn src(&self, span: Span) -> CowStr<'s> {
        InlineSpans::borrow_or_copy(self.src, self.spans(), span)
    }

    fn chars(&self) -> Self::Chars {
        InlineChars::new(self.src, self.spans())
    }
}

pub type InlineSpansSliceIter<'i> = std::iter::Chain<
    std::iter::Chain<std::iter::Once<Span>, std::iter::Copied<std::slice::Iter<'i, Span>>>,
    std::iter::Once<Span>,
>;

#[cfg(test)]
mod test {
    use super::Span;

    #[test]
    fn from_slice() {
        let src = "0123456789";
        assert_eq!(Span::from_slice(src, &src[0..0]), Span::new(0, 0));
        assert_eq!(Span::from_slice(src, &src[0..5]), Span::new(0, 5));
        assert_eq!(Span::from_slice(src, &src[5..5]), Span::new(5, 5));
        assert_eq!(Span::from_slice(src, &src[5..8]), Span::new(5, 8));
        assert_eq!(Span::from_slice(src, &src[5..10]), Span::new(5, 10));
        assert_eq!(Span::from_slice(src, &src[5..]), Span::new(5, 10));
    }

    #[test]
    fn trim() {
        let src = "  23456   ";
        assert_eq!(Span::by_len(0, src.len()).trim_start(src), Span::new(2, 10));
        assert_eq!(Span::by_len(0, src.len()).trim_end(src), Span::new(0, 7));
        assert_eq!(Span::by_len(0, src.len()).trim(src), Span::new(2, 7));
        assert_eq!(
            Span::by_len(0, src.len()).trim_start(src).trim_end(src),
            Span::new(2, 7)
        );
    }
}
