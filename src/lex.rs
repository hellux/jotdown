use crate::EOF;

use Delimiter::*;
use Kind::*;
use Sequence::*;
use Symbol::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Token {
    pub kind: Kind,
    pub len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Text,
    Newline,
    Whitespace,
    Nbsp,
    Hardbreak,
    Escape,
    Integer,
    Open(Delimiter),
    Close(Delimiter),
    Sym(Symbol),
    Seq(Sequence),
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
    Paren,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Symbol {
    Ampersand,
    Asterisk,
    Caret,
    Equal,
    Exclaim,
    Gt,
    Lt,
    Percentage,
    Pipe,
    Plus,
    Quote1,
    Quote2,
    Tilde,
    Underscore,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sequence {
    Backtick,
    Colon,
    Dollar,
    Hash,
    Hyphen,
    Period,
}

impl Sequence {
    fn ch(self) -> char {
        match self {
            Self::Backtick => '`',
            Self::Colon => ':',
            Self::Dollar => '$',
            Self::Hash => '#',
            Self::Period => '.',
            Self::Hyphen => '-',
        }
    }
}

#[derive(Clone)]
pub(crate) struct Lexer<'s> {
    pub src: &'s str,
    chars: std::str::Chars<'s>,
    /// Next character should be escaped.
    escape: bool,
    /// Token to be peeked or next'ed.
    next: Option<Token>,
    /// Length of current token.
    len: usize,
}

impl<'s> Lexer<'s> {
    pub fn new(src: &'s str) -> Lexer<'s> {
        Lexer {
            src,
            chars: src.chars(),
            escape: false,
            next: None,
            len: 0,
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        if self.next.is_none() {
            self.next = self.next_token();
        }
        self.next.as_ref()
    }

    pub fn pos(&self) -> usize {
        self.src.len()
            - self.chars.as_str().len()
            - self.next.as_ref().map(|t| t.len).unwrap_or_default()
    }

    pub fn peek_ahead(&mut self) -> &'s str {
        &self.src[self.pos()..]
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

    fn peek_char(&mut self) -> char {
        self.chars.clone().next().unwrap_or(EOF)
    }

    fn eat_char(&mut self) -> Option<char> {
        let c = self.chars.next();
        self.len += c.map_or(0, char::len_utf8);
        c
    }

    fn eat_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        while predicate(self.peek_char()) {
            self.eat_char();
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

            '\\' => {
                let next = self.peek_char();
                if next.is_whitespace() || next.is_ascii_punctuation() {
                    self.escape = true;
                    Escape
                } else {
                    Text
                }
            }

            '\n' => Newline,
            _ if first.is_whitespace() => {
                self.eat_while(char::is_whitespace);
                Whitespace
            }

            '(' => Open(Paren),
            ')' => Close(Paren),
            '[' => Open(Bracket),
            ']' => Close(Bracket),
            '{' => {
                let explicit = match self.peek_char() {
                    '*' => Some(Open(BraceAsterisk)),
                    '^' => Some(Open(BraceCaret)),
                    '=' => Some(Open(BraceEqual)),
                    '-' => Some(Open(BraceHyphen)),
                    '+' => Some(Open(BracePlus)),
                    '~' => Some(Open(BraceTilde)),
                    '_' => Some(Open(BraceUnderscore)),
                    _ => None,
                };
                if let Some(exp) = explicit {
                    self.eat_char();
                    exp
                } else {
                    Open(Brace)
                }
            }
            '&' => self.maybe_eat_close_brace(Ampersand, BraceAsterisk),
            '*' => self.maybe_eat_close_brace(Asterisk, BraceAsterisk),
            '^' => self.maybe_eat_close_brace(Caret, BraceCaret),
            '=' => self.maybe_eat_close_brace(Equal, BraceEqual),
            '+' => self.maybe_eat_close_brace(Plus, BracePlus),
            '~' => self.maybe_eat_close_brace(Tilde, BraceTilde),
            '_' => self.maybe_eat_close_brace(Underscore, BraceUnderscore),
            '-' => {
                if self.peek_char() == '}' {
                    self.eat_char();
                    Close(BraceHyphen)
                } else {
                    self.eat_seq(Hyphen)
                }
            }

            '!' => Sym(Exclaim),
            '%' => Sym(Percentage),
            '<' => Sym(Lt),
            '>' => Sym(Gt),
            '|' => Sym(Pipe),
            '\'' => Sym(Quote1),
            '"' => Sym(Quote2),

            '`' => self.eat_seq(Backtick),
            ':' => self.eat_seq(Colon),
            '$' => self.eat_seq(Dollar),
            '#' => self.eat_seq(Hash),
            '.' => self.eat_seq(Period),

            '0'..='9' => {
                self.eat_while(|c| c.is_ascii_digit());
                Integer
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

    fn maybe_eat_close_brace(&mut self, s: Symbol, d: Delimiter) -> Kind {
        if self.peek_char() == '}' {
            self.eat_char();
            Close(d)
        } else {
            Sym(s)
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
            Text.l(4),
            Whitespace.l(1),
            Text.l(2),
            Whitespace.l(1),
            Text.l(4),
            Whitespace.l(1),
            Sym(Underscore).l(1),
            Text.l(8),
            Sym(Underscore).l(1),
            Whitespace.l(1),
            Text.l(3),
            Whitespace.l(1),
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
            r#"'*^=!><%|+"~_"#,
            Sym(Quote1).l(1),
            Sym(Asterisk).l(1),
            Sym(Caret).l(1),
            Sym(Equal).l(1),
            Sym(Exclaim).l(1),
            Sym(Gt).l(1),
            Sym(Lt).l(1),
            Sym(Percentage).l(1),
            Sym(Pipe).l(1),
            Sym(Plus).l(1),
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
            "`:$#-.",
            Seq(Backtick).l(1),
            Seq(Colon).l(1),
            Seq(Dollar).l(1),
            Seq(Hash).l(1),
            Seq(Hyphen).l(1),
            Seq(Period).l(1),
        );
    }

    #[test]
    fn int() {
        test_lex!("1", Integer.l(1));
        test_lex!("123", Integer.l(3));
        test_lex!("1234567890", Integer.l(10));
        test_lex!("000", Integer.l(3));
    }
}
