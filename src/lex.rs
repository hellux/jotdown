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
    fn ch(self) -> char {
        match self {
            Self::Backtick => '`',
            Self::Period => '.',
            Self::Hyphen => '-',
        }
    }
}

#[derive(Clone)]
pub(crate) struct Lexer<'s> {
    src: &'s str,
    chars: std::str::Chars<'s>,
    /// Next character should be escaped.
    escape: bool,
    /// Token to be peeked or next'ed.
    next: Option<Token>,
    /// Length of current token.
    len: usize,
}

impl<'s> Lexer<'s> {
    pub fn new(src: &'s str) -> Self {
        Lexer {
            src,
            chars: src.chars(),
            escape: false,
            next: None,
            len: 0,
        }
    }

    /// NOTE: Peeked [`Kind::Text`] tokens are only one char long, they may be longer when
    /// consumed.
    pub fn peek(&mut self) -> Option<&Token> {
        if self.next.is_none() {
            self.next = self.token();
        }
        self.next.as_ref()
    }

    pub fn ahead(&self) -> &'s str {
        let pos =
            self.src.len() - self.chars.as_str().len() - self.next.as_ref().map_or(0, |t| t.len);
        &self.src[pos..]
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

    fn peek_char_n(&mut self, n: usize) -> Option<char> {
        self.chars.clone().nth(n)
    }

    fn peek_char(&mut self) -> Option<char> {
        self.peek_char_n(0)
    }

    fn eat_char(&mut self) -> Option<char> {
        let c = self.chars.next();
        self.len += c.map_or(0, char::len_utf8);
        c
    }

    fn eat_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        while let Some(c) = self.peek_char() {
            if predicate(c) {
                self.eat_char();
            } else {
                break;
            }
        }
    }

    fn token(&mut self) -> Option<Token> {
        self.len = 0;

        let first = self.eat_char()?;

        let escape = self.escape;

        let kind = match first {
            _ if escape && first == '\n' => Hardbreak,
            _ if escape
                && matches!(first, '\t' | ' ')
                && self.chars.clone().find(|c| !matches!(c, ' ' | '\t')) == Some('\n') =>
            {
                while self.eat_char() != Some('\n') {}
                Hardbreak
            }
            _ if escape && first == ' ' => Nbsp,
            _ if escape => Text,

            '\n' => Newline,

            '\\' => {
                if self
                    .peek_char()
                    .map_or(false, |c| c.is_whitespace() || c.is_ascii_punctuation())
                {
                    self.escape = true;
                    Escape
                } else {
                    Text
                }
            }

            '[' => Open(Bracket),
            ']' => Close(Bracket),
            '(' => Open(Paren),
            ')' => Close(Paren),
            '{' => {
                let explicit = match self.peek_char() {
                    Some('*') => Some(Open(BraceAsterisk)),
                    Some('^') => Some(Open(BraceCaret)),
                    Some('=') => Some(Open(BraceEqual)),
                    Some('-') => Some(Open(BraceHyphen)),
                    Some('+') => Some(Open(BracePlus)),
                    Some('~') => Some(Open(BraceTilde)),
                    Some('_') => Some(Open(BraceUnderscore)),
                    Some('\'') => Some(Open(BraceQuote1)),
                    Some('"') => Some(Open(BraceQuote2)),
                    _ => None,
                };
                if let Some(exp) = explicit {
                    self.eat_char();
                    exp
                } else {
                    Open(Brace)
                }
            }
            '}' => Close(Brace),
            '*' => self.maybe_eat_close_brace(Sym(Asterisk), BraceAsterisk),
            '^' => self.maybe_eat_close_brace(Sym(Caret), BraceCaret),
            '=' => self.maybe_eat_close_brace(Text, BraceEqual),
            '+' => self.maybe_eat_close_brace(Text, BracePlus),
            '~' => self.maybe_eat_close_brace(Sym(Tilde), BraceTilde),
            '_' => self.maybe_eat_close_brace(Sym(Underscore), BraceUnderscore),
            '\'' => self.maybe_eat_close_brace(Sym(Quote1), BraceQuote1),
            '"' => self.maybe_eat_close_brace(Sym(Quote2), BraceQuote2),
            '-' => {
                if self.peek_char() == Some('}') {
                    self.eat_char();
                    Close(BraceHyphen)
                } else {
                    while self.peek_char() == Some('-') && self.peek_char_n(1) != Some('}') {
                        self.eat_char();
                    }
                    Seq(Hyphen)
                }
            }

            '!' if self.peek_char() == Some('[') => {
                self.eat_char();
                Sym(ExclaimBracket)
            }
            '<' => Sym(Lt),
            '|' => Sym(Pipe),
            ':' => Sym(Colon),

            '`' => self.eat_seq(Backtick),
            '.' => self.eat_seq(Period),
            '$' => {
                self.eat_while(|c| c == '$');
                let mut n_ticks: u8 = 0;
                self.eat_while(|c| {
                    if c == '`' {
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
        };

        if escape {
            self.escape = false;
        }

        Some(Token {
            kind,
            len: self.len,
        })
    }

    fn eat_seq(&mut self, s: Sequence) -> Kind {
        self.eat_while(|c| c == s.ch());
        Seq(s)
    }

    fn maybe_eat_close_brace(&mut self, kind: Kind, d: Delimiter) -> Kind {
        if self.peek_char() == Some('}') {
            self.eat_char();
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
