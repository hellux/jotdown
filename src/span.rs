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

    pub fn with_start(self, start: usize) -> Self {
        Self::new(start, self.end())
    }

    pub fn trim_start(self, n: usize) -> Self {
        Self::new(self.start().checked_add(n).unwrap(), self.end())
    }

    pub fn translate(self, n: usize) -> Self {
        Self::new(
            self.start().checked_add(n).unwrap(),
            self.end().checked_add(n).unwrap(),
        )
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
}
