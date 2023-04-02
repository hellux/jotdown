use std::{borrow::Borrow, fmt::Display, ops::Deref, str::from_utf8};

// Largest CowStr variant is Owned(String). A String uses 3 words of memory, but a fourth word is
// needed to hold the tag (the tag takes a byte, but a full word is used for alignment reasons.)
// This means that the available space we have for an inline string is 4 words - 2 bytes for the
// tag and length.
const MAX_INLINE_STR_LEN: usize = 4 * std::mem::size_of::<usize>() - 2;

/// A clone-on-write string that is inlined if it is small enough.
///
/// Minimizes the number of heap allocations when working with small strings.
#[derive(Debug, Eq)]
pub enum CowStr<'s> {
    Owned(String),
    Borrowed(&'s str),
    Inlined([u8; MAX_INLINE_STR_LEN], u8),
}

impl<'s> CowStr<'s> {
    /// Replaces all occurrences of `from` with `to`.
    ///
    /// Takes ownership of self and returns a new [`CowStr`].
    pub fn replace(self, from: &str, to: &str) -> Self {
        if from.is_empty() {
            return self;
        }

        match self {
            CowStr::Inlined(mut inner, len) => {
                let mut len = len as usize;
                let diff = to.len() as isize - from.len() as isize;

                while let Some(start) = from_utf8(&inner[..len]).unwrap().find(from) {
                    if diff.is_positive() {
                        len += diff as usize;
                        if len > MAX_INLINE_STR_LEN {
                            return CowStr::Owned(self.deref().replace(from, to));
                        }
                        inner[start + from.len()..].rotate_right(diff as usize);
                    } else if diff.is_negative() {
                        len -= (-diff) as usize;
                        inner[start..].rotate_left((-diff) as usize);
                    }

                    inner[start..start + to.len()].copy_from_slice(to.as_bytes());
                }

                CowStr::Inlined(inner, len as u8)
            }
            CowStr::Borrowed(s) if s.contains(from) => {
                let mut inner = [0; MAX_INLINE_STR_LEN];
                let mut len = s.len();
                let diff = to.len() as isize - from.len() as isize;
                inner[..len].copy_from_slice(s.as_bytes());

                while let Some(start) = from_utf8(&inner[..len]).unwrap().find(from) {
                    if diff.is_positive() {
                        len += diff as usize;
                        if len > MAX_INLINE_STR_LEN {
                            return CowStr::Owned(self.deref().replace(from, to));
                        }
                        inner[start + from.len()..].rotate_right(diff as usize);
                    } else if diff.is_negative() {
                        len -= (-diff) as usize;
                        inner[start..].rotate_left((-diff) as usize);
                    }

                    inner[start..start + to.len()].copy_from_slice(to.as_bytes());
                }

                CowStr::Inlined(inner, len as u8)
            }
            CowStr::Owned(s) if s.contains(from) => CowStr::Owned(s.replace(from, to)),
            _ => self,
        }
    }

    /// Pushes a character to the end of the [`CowStr`].
    pub fn push(&mut self, c: char) {
        match self {
            CowStr::Owned(this) => this.push(c),
            CowStr::Inlined(inner, len) => {
                let l = *len as usize + c.len_utf8();
                if l > MAX_INLINE_STR_LEN {
                    let mut s = self.to_string();
                    s.push(c);
                    *self = CowStr::Owned(s);
                } else {
                    c.encode_utf8(&mut inner[*len as usize..l]);
                    *len = l as u8;
                }
            }
            CowStr::Borrowed(this) => {
                let len = this.len() + c.len_utf8();
                if len > MAX_INLINE_STR_LEN {
                    let mut s = self.to_string();
                    s.push(c);
                    *self = CowStr::Owned(s);
                } else {
                    let mut inner = [0; MAX_INLINE_STR_LEN];
                    inner[..this.len()].copy_from_slice(this.as_bytes());
                    c.encode_utf8(&mut inner[this.len()..len]);
                    *self = CowStr::Inlined(inner, len as u8);
                }
            }
        }
    }

    /// Pushes a string slice to the end of the [`CowStr`].
    pub fn push_str(&mut self, s: &str) {
        if s.is_empty() {
            return;
        }

        match self {
            CowStr::Owned(this) => this.push_str(s),
            CowStr::Inlined(inner, len) => {
                let l = *len as usize + s.len();
                if l > MAX_INLINE_STR_LEN {
                    *self = CowStr::Owned(self.to_string() + s);
                } else {
                    inner[*len as usize..l].copy_from_slice(s.as_bytes());
                    *len = l as u8;
                }
            }
            CowStr::Borrowed(this) => {
                let len = this.len() + s.len();
                if len > MAX_INLINE_STR_LEN {
                    *self = CowStr::Owned(this.to_string() + s);
                } else {
                    let mut inner = [0; MAX_INLINE_STR_LEN];
                    inner[..this.len()].copy_from_slice(this.as_bytes());
                    inner[this.len()..len].copy_from_slice(s.as_bytes());
                    *self = CowStr::Inlined(inner, len as u8);
                }
            }
        }
    }
}

impl<'s> Deref for CowStr<'s> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        match *self {
            Self::Owned(ref s) => s.borrow(),
            Self::Borrowed(s) => s,
            // NOTE: Inlined strings can only be constructed from strings or chars, which means they
            // are guaranteed to be valid UTF-8. We could consider unchecked conversion as well, but
            // a benchmark should be done before introducing unsafes.
            Self::Inlined(ref inner, len) => from_utf8(&inner[..len as usize]).unwrap(),
        }
    }
}

impl<'s> AsRef<str> for CowStr<'s> {
    fn as_ref(&self) -> &str {
        self.deref()
    }
}

impl<'s> From<char> for CowStr<'s> {
    fn from(value: char) -> Self {
        let mut inner = [0u8; MAX_INLINE_STR_LEN];
        value.encode_utf8(&mut inner);
        CowStr::Inlined(inner, value.len_utf8() as u8)
    }
}

impl<'s> From<&'s str> for CowStr<'s> {
    fn from(value: &'s str) -> Self {
        CowStr::Borrowed(value)
    }
}

impl<'s> From<String> for CowStr<'s> {
    fn from(value: String) -> Self {
        CowStr::Owned(value)
    }
}

impl<'s> Clone for CowStr<'s> {
    fn clone(&self) -> Self {
        match self {
            CowStr::Owned(s) => {
                let len = s.len();
                if len > MAX_INLINE_STR_LEN {
                    CowStr::Owned(s.clone())
                } else {
                    let mut inner = [0u8; MAX_INLINE_STR_LEN];
                    inner[..len].copy_from_slice(s.as_bytes());
                    CowStr::Inlined(inner, len as u8)
                }
            }
            CowStr::Borrowed(s) => CowStr::Borrowed(s),
            CowStr::Inlined(inner, len) => CowStr::Inlined(*inner, *len),
        }
    }
}

impl<'s> PartialEq for CowStr<'s> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<'s> Display for CowStr<'s> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.deref())
    }
}

impl<'s, 'a> FromIterator<&'a str> for CowStr<'s> {
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        CowStr::Owned(FromIterator::from_iter(iter))
    }
}

#[cfg(test)]
mod tests {
    macro_rules! assert_matches {
        ($expression:expr, $pattern:pat) => {
            match $expression {
                $pattern => (),
                ref e => panic!(
                    "assertion failed: `{:?}` does not match `{}`",
                    e,
                    stringify!($pattern)
                ),
            }
        };
    }

    use super::*;

    #[test]
    fn push_to_borrowed() {
        let mut s = CowStr::Borrowed("hello");
        s.push_str("a".repeat(MAX_INLINE_STR_LEN - 6).as_str());
        assert_matches!(s, CowStr::Inlined(..));
        s.push('a');
        assert_matches!(s, CowStr::Inlined(..));
        s.push('a');
        assert_matches!(s, CowStr::Owned(..));
    }

    #[test]
    fn push_to_inlined() {
        let mut s = CowStr::Inlined([0; MAX_INLINE_STR_LEN], 0);
        s.push_str("a".repeat(MAX_INLINE_STR_LEN - 1).as_str());
        assert_matches!(s, CowStr::Inlined(..));
        s.push('a');
        assert_matches!(s, CowStr::Inlined(..));
        s.push('a');
        assert_matches!(s, CowStr::Owned(..));
    }

    #[test]
    fn push_to_owned() {
        let mut s = CowStr::Owned("hello".to_string());
        s.push_str("a".repeat(MAX_INLINE_STR_LEN - 6).as_str());
        assert_matches!(s, CowStr::Owned(..));
        s.push('a');
        assert_matches!(s, CowStr::Owned(..));
        s.push('a');
        assert_matches!(s, CowStr::Owned(..));
    }

    #[test]
    fn push_empty() {
        let max_min1 = "a".repeat(MAX_INLINE_STR_LEN - 1);
        let mut s = CowStr::Borrowed(&max_min1);
        s.push_str("");
        assert_matches!(s, CowStr::Borrowed(..));

        let max = "a".repeat(MAX_INLINE_STR_LEN);
        let mut s = CowStr::Borrowed(&max);
        s.push_str("");
        assert_matches!(s, CowStr::Borrowed(..));

        let max_plus1 = "a".repeat(MAX_INLINE_STR_LEN + 1);
        let mut s = CowStr::Borrowed(&max_plus1);
        s.push_str("");
        assert_matches!(s, CowStr::Borrowed(..));
    }

    #[test]
    fn replace_borrowed() {
        let string = "a".repeat(MAX_INLINE_STR_LEN - 1) + "b";
        let s = CowStr::Borrowed(&string);
        assert_matches!(s.clone().replace("b", ""), CowStr::Inlined(..));
        assert_matches!(s.clone().replace("b", "c"), CowStr::Inlined(..));
        assert_matches!(s.clone().replace("b", "cd"), CowStr::Owned(..));
    }

    #[test]
    fn replace_inlined() {
        let mut arr = [65; MAX_INLINE_STR_LEN];
        arr[0] = 66;
        let s = CowStr::Inlined(arr, MAX_INLINE_STR_LEN as u8);
        assert_matches!(s.clone().replace("B", ""), CowStr::Inlined(..));
        assert_matches!(s.clone().replace("B", "C"), CowStr::Inlined(..));
        assert_matches!(s.clone().replace("B", "CD"), CowStr::Owned(..));
    }

    #[test]
    fn replace_owned() {
        let string = "a".repeat(MAX_INLINE_STR_LEN - 1) + "b";
        // We need to create a new `s` each time, because we want to make sure the CowStr is of the
        // Owned variant before replacing. Cloning the CowStr would inline it given the chance.
        let s = CowStr::Owned(string.clone());
        assert_matches!(s.replace("b", ""), CowStr::Owned(..));
        let s = CowStr::Owned(string.clone());
        assert_matches!(s.replace("b", "c"), CowStr::Owned(..));
        let s = CowStr::Owned(string);
        assert_matches!(s.replace("b", "cd"), CowStr::Owned(..));
    }

    #[test]
    fn inline_replace() {
        let mut s = CowStr::Borrowed("hello hello");
        s.push_str(" hellohello");
        assert_eq!(
            s.clone().replace("djot", "jotdown").as_ref(),
            "hello hello hellohello"
        );
        assert_eq!(s.clone().replace("hello", "hi").as_ref(), "hi hi hihi");

        let mut s = CowStr::Borrowed("start middle");
        s.push_str(" end");
        assert_eq!(
            s.clone().replace("start", "replaced").as_ref(),
            "replaced middle end"
        );
        assert_eq!(
            s.clone().replace("middle", "replaced").as_ref(),
            "start replaced end"
        );
        assert_eq!(
            s.clone().replace("end", "replaced").as_ref(),
            "start middle replaced"
        );
    }
}
