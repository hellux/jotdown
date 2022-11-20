use crate::EOF;

use Delimiter::*;
use Sequence::*;
use Symbol::*;
use TokenKind::*;

#[derive(Debug)]
pub(crate) struct Token {
    pub kind: TokenKind,
    pub len: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    Text,
    Whitespace,
    Nbsp,
    Escape,
    Integer,
    Open(Delimiter),
    Close(Delimiter),
    Sym(Symbol),
    Seq(Sequence),
}

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, PartialEq, Eq)]
pub enum Symbol {
    Asterisk,
    Caret,
    Dollar1,
    Dollar2,
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
    Hash,
    Hyphen,
    Period,
}

impl Sequence {
    fn ch(self) -> char {
        match self {
            Self::Backtick => '`',
            Self::Colon => ':',
            Self::Hash => '#',
            Self::Period => '.',
            Self::Hyphen => '-',
        }
    }
}

pub(crate) struct Lexer<I: Iterator<Item = char>> {
    chars: std::iter::Peekable<I>,
    escape: bool,
    next: Option<Token>,
    len: usize,
}

impl<I: Iterator<Item = char>> Lexer<I> {
    pub fn new(chars: I) -> Lexer<I> {
        Lexer {
            chars: chars.peekable(),
            escape: false,
            next: None,
            len: 0,
        }
    }

    fn peek(&mut self) -> char {
        self.chars.peek().copied().unwrap_or(EOF)
    }

    fn eat(&mut self) -> Option<char> {
        let c = self.chars.next();
        self.len += c.map_or(0, char::len_utf8);
        c
    }

    fn len(&self) -> usize {
        self.len
    }

    fn eat_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        while predicate(self.peek()) {
            self.eat();
        }
    }

    fn token(&mut self) -> Option<Token> {
        let first = self.eat()?;

        let escape = self.escape;

        let kind = match first {
            _ if escape && first == ' ' => Nbsp,
            _ if escape => Text,

            '\\' => {
                let next = self.peek();
                if next == ' ' || next.is_ascii_punctuation() {
                    self.escape = true;
                    Escape
                } else {
                    Text
                }
            }

            _ if first.is_whitespace() => {
                self.eat_while(char::is_whitespace);
                Whitespace
            }

            '(' => Open(Paren),
            ')' => Close(Paren),
            '[' => Open(Bracket),
            ']' => Close(Bracket),
            '{' => {
                let explicit = match self.peek() {
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
                    self.eat();
                    exp
                } else {
                    Open(Brace)
                }
            }
            '*' => self.maybe_eat_close_brace(Asterisk, BraceAsterisk),
            '^' => self.maybe_eat_close_brace(Caret, BraceCaret),
            '=' => self.maybe_eat_close_brace(Equal, BraceEqual),
            '+' => self.maybe_eat_close_brace(Plus, BracePlus),
            '~' => self.maybe_eat_close_brace(Tilde, BraceTilde),
            '_' => self.maybe_eat_close_brace(Underscore, BraceUnderscore),
            '-' => {
                if self.peek() == '}' {
                    self.eat();
                    Close(BraceHyphen)
                } else {
                    self.eat_seq(Hyphen)
                }
            }

            '$' => {
                if self.peek() == '$' {
                    self.eat();
                    Sym(Dollar2)
                } else {
                    Sym(Dollar1)
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

        let len = self.len();

        Some(Token { kind, len })
    }

    fn eat_seq(&mut self, s: Sequence) -> TokenKind {
        self.eat_while(|c| c == s.ch());
        Seq(s)
    }

    fn maybe_eat_close_brace(&mut self, s: Symbol, d: Delimiter) -> TokenKind {
        if self.peek() == '}' {
            self.eat();
            Close(d)
        } else {
            Sym(s)
        }
    }
}

impl<I: Iterator<Item = char>> Iterator for Lexer<I> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(token) = self.next.take() {
            Some(token)
        } else {
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
    }
}

#[cfg(test)]
mod test {
    use super::Delimiter::*;
    use super::Sequence::*;
    use super::Symbol::*;
    use super::TokenKind::*;

    macro_rules! test_lex {
        ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
            #[allow(unused)]
            let actual = super::Lexer::new($src.chars()).map(|t| t.kind).collect::<Vec<_>>();
            let expected = vec![$($($token),*,)?];
            assert_eq!(actual, expected, "{}", $src);
        };
    }

    #[test]
    fn empty() {
        test_lex!("");
    }

    #[test]
    fn basic() {
        test_lex!("abc", Text);
        test_lex!(
            "para w/ some _emphasis_ and *strong*.",
            Text,
            Whitespace,
            Text,
            Whitespace,
            Text,
            Whitespace,
            Sym(Underscore),
            Text,
            Sym(Underscore),
            Whitespace,
            Text,
            Whitespace,
            Sym(Asterisk),
            Text,
            Sym(Asterisk),
            Seq(Period)
        );
    }

    #[test]
    fn escape() {
        test_lex!(r#"\a"#, Text);
        test_lex!(r#"\\a"#, Escape, Text);
        test_lex!(r#"\."#, Escape, Text);
        test_lex!(r#"\ "#, Escape, Nbsp);
        test_lex!(r#"\{-"#, Escape, Text, Seq(Hyphen));
    }

    #[test]
    fn delim() {
        test_lex!("{-", Open(BraceHyphen));
        test_lex!("-}", Close(BraceHyphen));
        test_lex!("{++}", Open(BracePlus), Close(BracePlus));
    }

    #[test]
    fn sym() {
        test_lex!(
            r#"'*^=!><%|+"~_"#,
            Sym(Quote1),
            Sym(Asterisk),
            Sym(Caret),
            Sym(Equal),
            Sym(Exclaim),
            Sym(Gt),
            Sym(Lt),
            Sym(Percentage),
            Sym(Pipe),
            Sym(Plus),
            Sym(Quote2),
            Sym(Tilde),
            Sym(Underscore),
        );
        test_lex!("''''", Sym(Quote1), Sym(Quote1), Sym(Quote1), Sym(Quote1),);
    }

    #[test]
    fn seq() {
        test_lex!("`", Seq(Backtick));
        test_lex!("```", Seq(Backtick));
        test_lex!(
            "`:#-.",
            Seq(Backtick),
            Seq(Colon),
            Seq(Hash),
            Seq(Hyphen),
            Seq(Period),
        );
    }

    #[test]
    fn int() {
        test_lex!("1", Integer);
        test_lex!("123", Integer);
        test_lex!("1234567890", Integer);
        test_lex!("000", Integer);
    }
}
