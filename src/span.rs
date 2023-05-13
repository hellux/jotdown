#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Span {
    start: u32,
    end: u32,
}

impl From<Span> for std::ops::Range<usize> {
    fn from(span: Span) -> Self {
        span.start()..span.end()
    }
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

    pub fn skip_chars(self, n: usize, s: &str) -> Self {
        let n_bytes: usize = self.of(s).chars().take(n).map(char::len_utf8).sum();
        Self::new(self.start() + n_bytes, self.end())
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
