use super::Atom::*;
use super::Container::*;
use super::EventKind::*;
use super::QuoteType;
use super::Verbatim;

macro_rules! test_parse {
    ($($st:ident,)? $src:expr $(,$($token:expr),* $(,)?)?) => {
        #[allow(unused)]
        let mut p = super::Parser::new($src);
        p.feed_line(0..$src.len(), true);
        let actual = p.map(|ev| (ev.kind, &$src[ev.span])).collect::<Vec<_>>();
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
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{#id}"
        ),
        (Enter(Verbatim), "`"),
        (Str, "raw"),
        (Exit(Verbatim), "`{#id}"),
        (Str, " post"),
    );
}

#[test]
fn verbatim_attr_inside() {
    test_parse!(
        "`a{i=0}`",
        (Enter(Verbatim), "`"),
        (Str, "a{i=0}"),
        (Exit(Verbatim), "`"),
    );
    test_parse!(
        r"$`\sum_{i=0}^n 2^i`",
        (Enter(InlineMath), "$`"),
        (Str, r"\sum_{i=0}^n 2^i"),
        (Exit(InlineMath), "`"),
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
        (Enter(RawFormat { format: "format" }), "`"),
        (Str, "raw"),
        (Exit(RawFormat { format: "format" }), "`{=format}"),
    );
    test_parse!(
        "before `raw`{=format} after",
        (Str, "before "),
        (Enter(RawFormat { format: "format" }), "`"),
        (Str, "raw"),
        (Exit(RawFormat { format: "format" }), "`{=format}"),
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
        (Enter(ReferenceLink(0)), "["),
        (Str, "text"),
        (Exit(ReferenceLink(0)), "][tag]"),
    );
    test_parse!(
        "![text][tag]",
        (Enter(ReferenceImage(0)), "!["),
        (Str, "text"),
        (Exit(ReferenceImage(0)), "][tag]"),
    );
    test_parse!(
        "before [text][tag] after",
        (Str, "before "),
        (Enter(ReferenceLink(0)), "["),
        (Str, "text"),
        (Exit(ReferenceLink(0)), "][tag]"),
        (Str, " after"),
    );
    test_parse!(
        "[[inner][i]][o]",
        (Enter(ReferenceLink(1)), "["),
        (Enter(ReferenceLink(0)), "["),
        (Str, "inner"),
        (Exit(ReferenceLink(0)), "][i]"),
        (Exit(ReferenceLink(1)), "][o]"),
    );
}

#[test]
fn span_tag_empty() {
    test_parse!(
        "[text][]",
        (Enter(ReferenceLink(0)), "["),
        (Str, "text"),
        (Exit(ReferenceLink(0)), "][]"),
    );
    test_parse!(
        "![text][]",
        (Enter(ReferenceImage(0)), "!["),
        (Str, "text"),
        (Exit(ReferenceImage(0)), "][]"),
    );
}

#[test]
fn span_tag_empty_nested() {
    test_parse!(
        "[some _text_][]",
        (Enter(ReferenceLink(0)), "["),
        (Str, "some "),
        (Enter(Emphasis), "_"),
        (Str, "text"),
        (Exit(Emphasis), "_"),
        (Exit(ReferenceLink(0)), "][]"),
    );
}

#[test]
fn span_url() {
    test_parse!(
        "before [text](url) after",
        (Str, "before "),
        (Enter(InlineLink(0)), "["),
        (Str, "text"),
        (Exit(InlineLink(0)), "](url)"),
        (Str, " after"),
    );
    test_parse!(
        "[outer [inner](i)](o)",
        (Enter(InlineLink(1)), "["),
        (Str, "outer "),
        (Enter(InlineLink(0)), "["),
        (Str, "inner"),
        (Exit(InlineLink(0)), "](i)"),
        (Exit(InlineLink(1)), "](o)"),
    );
}

#[test]
fn span_url_attr_unclosed() {
    test_parse!(
        "[text]({.cls}",
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{.cls}"
        ),
        (Enter(Span), ""),
        (Str, "[text]("),
        (Exit(Span), "{.cls}"),
    );
}

#[test]
fn span_url_attr_closed() {
    test_parse!(
        "[text]({.cls})",
        (Enter(InlineLink(0)), "["),
        (Str, "text"),
        (Exit(InlineLink(0)), "]({.cls})"),
    );
}

#[test]
fn span_url_empty() {
    test_parse!(
        "before [text]() after",
        (Str, "before "),
        (Enter(InlineLink(0)), "["),
        (Str, "text"),
        (Exit(InlineLink(0)), "]()"),
        (Str, " after"),
    );
}

#[test]
fn span_url_unclosed() {
    test_parse!("[text](url", (Str, "[text](url"));
}

#[test]
fn span() {
    test_parse!("[abc]", (Str, "[abc]"));
}

#[test]
fn span_no_text() {
    test_parse!("[]", (Str, "[]"));
    test_parse!(
        "[](url)",
        (Enter(InlineLink(0)), "["),
        (Exit(InlineLink(0)), "](url)"),
    );
    test_parse!(
        "![](url)",
        (Enter(InlineImage(0)), "!["),
        (Exit(InlineImage(0)), "](url)"),
    );
    test_parse!(
        "[][label]",
        (Enter(ReferenceLink(0)), "["),
        (Exit(ReferenceLink(0)), "][label]"),
    );
    test_parse!(
        "[]{.cls}",
        (
            Attributes {
                container: true,
                attrs: 0
            },
            "{.cls}",
        ),
        (Enter(Span), "["),
        (Exit(Span), "]{.cls}")
    );
}

#[test]
fn span_attr() {
    test_parse!(
        "[abc]{.def}",
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{.def}"
        ),
        (Enter(Span), "["),
        (Str, "abc"),
        (Exit(Span), "]{.def}"),
    );
    test_parse!(
        "not a [span] {#id}.",
        (Str, "not a [span] "),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{#id}",
        ),
        (Empty, "{#id}"),
        (Str, "."),
    );
}

#[test]
fn span_attr_cont() {
    test_parse!(
        "[x_y]{.bar_}",
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{.bar_}"
        ),
        (Enter(Span), "["),
        (Str, "x_y"),
        (Exit(Span), "]{.bar_}"),
    );
}

#[test]
fn span_attr_exclamation_mark() {
    test_parse!(
        "![abc]{.def}",
        (Str, "!"),
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{.def}"
        ),
        (Enter(Span), "["),
        (Str, "abc"),
        (Exit(Span), "]{.def}"),
    );
}

#[test]
fn autolink() {
    test_parse!(
        "<https://example.com>",
        (Enter(Autolink("https://example.com",)), "<"),
        (Str, "https://example.com"),
        (Exit(Autolink("https://example.com",)), ">")
    );
    test_parse!(
        "<a@b.c>",
        (Enter(Autolink("a@b.c")), "<"),
        (Str, "a@b.c"),
        (Exit(Autolink("a@b.c")), ">"),
    );
    test_parse!(
        "<http://a.b><http://c.d>",
        (Enter(Autolink("http://a.b")), "<"),
        (Str, "http://a.b"),
        (Exit(Autolink("http://a.b")), ">"),
        (Enter(Autolink("http://c.d")), "<"),
        (Str, "http://c.d"),
        (Exit(Autolink("http://c.d")), ">"),
    );
    test_parse!("<not-a-url>", (Str, "<not-a-url>"));
}

#[test]
fn footnote_reference() {
    test_parse!(
        "text[^footnote]. more text",
        (Str, "text"),
        (Atom(FootnoteReference { label: "footnote" }), "[^footnote]"),
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
fn container_unclosed_attr() {
    test_parse!(
        "^.^{unclosed",
        (Enter(Superscript), "^"),
        (Str, "."),
        (Exit(Superscript), "^"),
        (Str, "{unclosed"),
    );
}

#[test]
fn verbatim_unclosed_attr() {
    test_parse!(
        "`.`{unclosed",
        (Enter(Verbatim), "`"),
        (Str, "."),
        (Exit(Verbatim), "`"),
        (Str, "{unclosed"),
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
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{.attr}"
        ),
        (Enter(Emphasis), "_"),
        (Str, "abc def"),
        (Exit(Emphasis), "_{.attr}"),
    );
}

#[test]
fn container_attr_empty() {
    test_parse!(
        "_abc def_{}",
        (Enter(Emphasis), "_"),
        (Str, "abc def"),
        (Exit(Emphasis), "_{}"),
    );
    test_parse!(
        "_abc def_{ % comment % } ghi",
        (
            Attributes {
                container: true,
                attrs: 0
            },
            "{ % comment % }"
        ),
        (Enter(Emphasis), "_"),
        (Str, "abc def"),
        (Exit(Emphasis), "_{ % comment % }"),
        (Str, " ghi"),
    );
}

#[test]
fn container_attr_multiple() {
    test_parse!(
        "_abc def_{.a}{.b}{.c} {.d}",
        (
            Attributes {
                container: true,
                attrs: 0,
            },
            "{.a}{.b}{.c}"
        ),
        (Enter(Emphasis), "_"),
        (Str, "abc def"),
        (Exit(Emphasis), "_{.a}{.b}{.c}"),
        (Str, " "),
        (
            Attributes {
                container: false,
                attrs: 1,
            },
            "{.d}",
        ),
        (Empty, "{.d}"),
    );
}

#[test]
fn attr() {
    test_parse!(
        "word{a=b}",
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{a=b}"
        ),
        (Enter(Span), ""),
        (Str, "word"),
        (Exit(Span), "{a=b}"),
    );
    test_parse!(
        "some word{.a}{.b} with attrs",
        (Str, "some "),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{.a}{.b}"
        ),
        (Enter(Span), ""),
        (Str, "word"),
        (Exit(Span), "{.a}{.b}"),
        (Str, " with attrs"),
    );
}

#[test]
fn attr_quoted() {
    test_parse!(
        r#"word{a="`verb`"}"#,
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            r#"{a="`verb`"}"#,
        ),
        (Enter(Span), ""),
        (Str, "word"),
        (Exit(Span), r#"{a="`verb`"}"#),
    );
}

#[test]
fn attr_whitespace() {
    test_parse!(
        "word {%comment%}",
        (Str, "word "),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{%comment%}",
        ),
        (Empty, "{%comment%}"),
    );
    test_parse!(
        "word {%comment%} word",
        (Str, "word "),
        (
            Attributes {
                container: false,
                attrs: 0
            },
            "{%comment%}",
        ),
        (Empty, "{%comment%}"),
        (Str, " word"),
    );
    test_parse!(
        "word {a=b}",
        (Str, "word "),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{a=b}",
        ),
        (Empty, "{a=b}"),
    );
    test_parse!(
        " {a=b}",
        (Str, " "),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{a=b}",
        ),
        (Empty, "{a=b}"),
    );
}

#[test]
fn attr_start() {
    test_parse!(
        "{a=b} word",
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{a=b}",
        ),
        (Empty, "{a=b}"),
        (Str, " word"),
    );
}

#[test]
fn attr_empty() {
    test_parse!("word{}", (Str, "word"));
    test_parse!(
        "word{ % comment % } trail",
        (
            Attributes {
                container: false,
                attrs: 0
            },
            "{ % comment % }"
        ),
        (Enter(Span), ""),
        (Str, "word"),
        (Exit(Span), "{ % comment % }"),
        (Str, " trail")
    );
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

#[test]
fn quote_attr() {
    test_parse!(
        "'a'{.b}",
        (
            Atom(Quote {
                ty: QuoteType::Single,
                left: true
            }),
            "'"
        ),
        (Str, "a"),
        (
            Atom(Quote {
                ty: QuoteType::Single,
                left: false
            }),
            "'"
        ),
        (
            Attributes {
                container: false,
                attrs: 0,
            },
            "{.b}",
        ),
        (Empty, "{.b}"),
    );
}
