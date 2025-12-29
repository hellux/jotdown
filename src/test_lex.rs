use super::Delimiter::*;
use super::Kind::*;
use super::Sequence::*;
use super::Symbol::*;

macro_rules! test_lex {
    ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
        #[allow(unused)]
        let actual = super::Lexer::new($src.as_bytes()).collect::<Vec<_>>();
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
