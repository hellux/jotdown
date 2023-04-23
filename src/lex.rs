use Delimiter::*;
use Kind::*;
use Sequence::*;
use Symbol::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Token {
    pub kind: Kind,
    pub len: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Text,
    #[cfg(feature = "softbreak")]
    Newline,
    Nbsp,
    Hardbreak,
    Escape,
    Open(Delimiter),
    Close(Delimiter),
    Sym(Symbol),
    Seq(Sequence),
    DollarBacktick(u8),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delimiter {
    Brace,
    BraceAsterisk,
    BraceCaret,
    BraceEqual,
    BraceHyphen,
    BracePlus,
    BraceTilde,
    BraceUnderscore,
    Bracket,
    BraceQuote1,
    BraceQuote2,
    Paren,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Symbol {
    Asterisk,
    Caret,
    ExclaimBracket,
    Lt,
    Pipe,
    Quote1,
    Quote2,
    Tilde,
    Underscore,
    Colon,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sequence {
    Backtick,
    Hyphen,
    Period,
}

impl Sequence {
    fn ch(self) -> u8 {
        match self {
            Self::Backtick => b'`',
            Self::Period => b'.',
            Self::Hyphen => b'-',
        }
    }
}

#[derive(Clone)]
pub(crate) struct Lexer<'s> {
    src: &'s str,
    /// Current position within `src`.
    pos: usize,
    /// Next character should be escaped.
    escape: bool,
    /// Token to be peeked or next'ed.
    next: Option<Token>,
}

impl<'s> Lexer<'s> {
    pub fn new(src: &'s str) -> Self {
        Lexer {
            src,
            pos: 0,
            escape: false,
            next: None,
        }
    }

    /// NOTE: Peeked [`Kind::Text`] tokens are only one byte long, they may be longer when
    /// consumed.
    pub fn peek(&mut self) -> Option<&Token> {
        if self.next.is_none() {
            self.next = self.token();
        }
        self.next.as_ref()
    }

    pub fn ahead(&self) -> &'s str {
        &self.src[self.pos - self.next.as_ref().map_or(0, |t| t.len)..]
    }

    fn next_token(&mut self) -> Option<Token> {
        let mut current = self.token();

        // concatenate text tokens
        if let Some(Token { kind: Text, len }) = &mut current {
            self.next = self.token();
            while let Some(Token { kind: Text, len: l }) = self.next {
                *len += l;
                self.next = self.token();
            }
        }

        current
    }

    fn peek_byte_n(&mut self, n: usize) -> Option<u8> {
        self.src.as_bytes().get(self.pos + n).copied()
    }

    fn peek_byte(&mut self) -> Option<u8> {
        self.peek_byte_n(0)
    }

    fn eat_byte(&mut self) -> Option<u8> {
        if self.pos < self.src.len() {
            let c = self.src.as_bytes()[self.pos];
            self.pos += 1;
            Some(c)
        } else {
            None
        }
    }

    fn eat_while(&mut self, mut predicate: impl FnMut(u8) -> bool) {
        while let Some(c) = self.peek_byte() {
            if predicate(c) {
                self.eat_byte();
            } else {
                break;
            }
        }
    }

    fn token(&mut self) -> Option<Token> {
        let start = self.pos;

        let kind = if self.escape {
            self.escape = false;
            match self.eat_byte()? {
                b'\n' => Hardbreak,
                b'\t' | b' '
                    if self.src[self.pos..]
                        .bytes()
                        .find(|c| !matches!(c, b' ' | b'\t'))
                        == Some(b'\n') =>
                {
                    while self.eat_byte() != Some(b'\n') {}
                    Hardbreak
                }
                b' ' => Nbsp,
                _ => Text,
            }
        } else {
            self.eat_while(|c| !is_special(c));
            if start < self.pos {
                Text
            } else {
                match self.eat_byte()? {
                    #[cfg(feature = "softbreak")]
                    b'\n' => Newline,

                    b'\\' => {
                        if self.peek_byte().map_or(false, |c| {
                            c.is_ascii_whitespace() || c.is_ascii_punctuation()
                        }) {
                            self.escape = true;
                            Escape
                        } else {
                            Text
                        }
                    }

                    b'[' => Open(Bracket),
                    b']' => Close(Bracket),
                    b'(' => Open(Paren),
                    b')' => Close(Paren),
                    b'{' => {
                        let explicit = match self.peek_byte() {
                            Some(b'*') => Some(Open(BraceAsterisk)),
                            Some(b'^') => Some(Open(BraceCaret)),
                            Some(b'=') => Some(Open(BraceEqual)),
                            Some(b'-') => Some(Open(BraceHyphen)),
                            Some(b'+') => Some(Open(BracePlus)),
                            Some(b'~') => Some(Open(BraceTilde)),
                            Some(b'_') => Some(Open(BraceUnderscore)),
                            Some(b'\'') => Some(Open(BraceQuote1)),
                            Some(b'"') => Some(Open(BraceQuote2)),
                            _ => None,
                        };
                        if let Some(exp) = explicit {
                            self.eat_byte();
                            exp
                        } else {
                            Open(Brace)
                        }
                    }
                    b'}' => Close(Brace),
                    b'*' => self.maybe_eat_close_brace(Sym(Asterisk), BraceAsterisk),
                    b'^' => self.maybe_eat_close_brace(Sym(Caret), BraceCaret),
                    b'=' => self.maybe_eat_close_brace(Text, BraceEqual),
                    b'+' => self.maybe_eat_close_brace(Text, BracePlus),
                    b'~' => self.maybe_eat_close_brace(Sym(Tilde), BraceTilde),
                    b'_' => self.maybe_eat_close_brace(Sym(Underscore), BraceUnderscore),
                    b'\'' => self.maybe_eat_close_brace(Sym(Quote1), BraceQuote1),
                    b'"' => self.maybe_eat_close_brace(Sym(Quote2), BraceQuote2),
                    b'-' => {
                        if self.peek_byte() == Some(b'}') {
                            self.eat_byte();
                            Close(BraceHyphen)
                        } else {
                            while self.peek_byte() == Some(b'-')
                                && self.peek_byte_n(1) != Some(b'}')
                            {
                                self.eat_byte();
                            }
                            Seq(Hyphen)
                        }
                    }

                    b'!' => {
                        if self.peek_byte() == Some(b'[') {
                            self.eat_byte();
                            Sym(ExclaimBracket)
                        } else {
                            Text
                        }
                    }
                    b'<' => Sym(Lt),
                    b'|' => Sym(Pipe),
                    b':' => Sym(Colon),

                    b'`' => self.eat_seq(Backtick),
                    b'.' => self.eat_seq(Period),
                    b'$' => {
                        self.eat_while(|c| c == b'$');
                        let mut n_ticks: u8 = 0;
                        self.eat_while(|c| {
                            if c == b'`' {
                                if let Some(l) = n_ticks.checked_add(1) {
                                    n_ticks = l;
                                    return true;
                                }
                            }
                            false
                        });
                        DollarBacktick(n_ticks)
                    }

                    _ => Text,
                }
            }
        };

        Some(Token {
            kind,
            len: self.pos - start,
        })
    }

    fn eat_seq(&mut self, s: Sequence) -> Kind {
        self.eat_while(|c| c == s.ch());
        Seq(s)
    }

    fn maybe_eat_close_brace(&mut self, kind: Kind, d: Delimiter) -> Kind {
        if self.peek_byte() == Some(b'}') {
            self.eat_byte();
            Close(d)
        } else {
            kind
        }
    }
}

impl<'s> Iterator for Lexer<'s> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().or_else(|| self.next_token())
    }
}

fn is_special(c: u8) -> bool {
    #[allow(unused_mut)]
    let mut special = matches!(
        c,
        b'\\'
            | b'['
            | b']'
            | b'('
            | b')'
            | b'{'
            | b'}'
            | b'*'
            | b'^'
            | b'='
            | b'+'
            | b'~'
            | b'_'
            | b'\''
            | b'"'
            | b'-'
            | b'!'
            | b'<'
            | b'|'
            | b':'
            | b'`'
            | b'.'
            | b'$'
    );
    #[cfg(feature = "softbreak")]
    {
        // this has a significant impact on performance in paragraphs with linebreaks
        special |= c == b'\n';
    }
    special
}

#[cfg(test)]
mod test {
    use super::Delimiter::*;
    use super::Kind::*;
    use super::Sequence::*;
    use super::Symbol::*;

    macro_rules! test_lex {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let actual = super::Lexer::new($src).collect::<Vec<_>>();
            let expected = vec![$($($token),*,)?];
            assert_eq!(actual, expected, "{}", $src);
        };
    }

    impl super::Kind {
        fn l(self, len: usize) -> super::Token {
            super::Token { kind: self, len }
        }
    }

    #[test]
    fn empty() {
        test_lex!("");
    }

    #[test]
    fn basic() {
        test_lex!("abc", Text.l(3));
        test_lex!(
            "para w/ some _emphasis_ and *strong*.",
            Text.l(13),
            Sym(Underscore).l(1),
            Text.l(8),
            Sym(Underscore).l(1),
            Text.l(5),
            Sym(Asterisk).l(1),
            Text.l(6),
            Sym(Asterisk).l(1),
            Seq(Period).l(1),
        );
    }

    #[test]
    fn escape() {
        test_lex!(r#"\a"#, Text.l(2));
        test_lex!(r#"\\a"#, Escape.l(1), Text.l(2));
        test_lex!(r#"\."#, Escape.l(1), Text.l(1));
        test_lex!(r#"\ "#, Escape.l(1), Nbsp.l(1));
        test_lex!(r#"\{-"#, Escape.l(1), Text.l(1), Seq(Hyphen).l(1));
    }

    #[test]
    fn hardbreak() {
        test_lex!("a\\\n", Text.l(1), Escape.l(1), Hardbreak.l(1));
        test_lex!("a\\   \n", Text.l(1), Escape.l(1), Hardbreak.l(4));
        test_lex!("a\\\t \t \n", Text.l(1), Escape.l(1), Hardbreak.l(5));
    }

    #[test]
    fn delim() {
        test_lex!("{-", Open(BraceHyphen).l(2));
        test_lex!("-}", Close(BraceHyphen).l(2));
        test_lex!("{++}", Open(BracePlus).l(2), Close(BracePlus).l(2));
    }

    #[test]
    fn sym() {
        test_lex!(
            r#"'*^![<|"~_"#,
            Sym(Quote1).l(1),
            Sym(Asterisk).l(1),
            Sym(Caret).l(1),
            Sym(ExclaimBracket).l(2),
            Sym(Lt).l(1),
            Sym(Pipe).l(1),
            Sym(Quote2).l(1),
            Sym(Tilde).l(1),
            Sym(Underscore).l(1),
        );
        test_lex!(
            "''''",
            Sym(Quote1).l(1),
            Sym(Quote1).l(1),
            Sym(Quote1).l(1),
            Sym(Quote1).l(1),
        );
    }

    #[test]
    fn seq() {
        test_lex!("`", Seq(Backtick).l(1));
        test_lex!("```", Seq(Backtick).l(3));
        test_lex!(
            "`-.",
            Seq(Backtick).l(1),
            Seq(Hyphen).l(1),
            Seq(Period).l(1),
        );
    }

    #[test]
    fn dollar_backtick() {
        test_lex!("$`", DollarBacktick(1).l(2));
        test_lex!("$$$`", DollarBacktick(1).l(4));
        test_lex!("$$````", DollarBacktick(4).l(6));
    }
}
