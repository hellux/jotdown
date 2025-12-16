use jotdown::Alignment;
use jotdown::AttributeKind;
use jotdown::Attributes;
use jotdown::Container::*;
use jotdown::Event::*;
use jotdown::LinkType;
use jotdown::ListBulletType::*;
use jotdown::ListKind;
use jotdown::OrderedListNumbering::*;
use jotdown::OrderedListStyle::*;
use jotdown::SpanLinkType;

macro_rules! attrs {
    ($(($kind:expr, $val:expr)),* $(,)?) => {
        [$(($kind, $val.into())),*].into_iter().collect::<jotdown::Attributes>()
    };
}

macro_rules! test_parse {
    ($src:expr $(,$($token:expr),* $(,)?)?) => {
        #[allow(unused)]
        let actual = jotdown::Parser::new($src)
            .into_offset_iter()
            .map(|(e, r)| (e, &$src[r]))
            .collect::<Vec<_>>();
        let expected = &[$($($token),*,)?];
        assert_eq!(
            actual,
            expected,
            concat!(
                "\n",
                "\x1b[0;1m====================== INPUT =========================\x1b[0m\n",
                "\x1b[2m{}{}",
                "\x1b[0;1m================ ACTUAL vs EXPECTED ==================\x1b[0m\n",
                "{}",
                "\x1b[0;1m======================================================\x1b[0m\n",
            ),
            $src,
            if $src.ends_with('\n') {
                ""
            } else {
                "\n"
            },
            {
                let a = actual.iter().map(|n| format!("{:?}", n)).collect::<Vec<_>>();
                let b = expected.iter().map(|n| format!("{:?}", n)).collect::<Vec<_>>();
                let max = a.len().max(b.len());
                let a_width = a.iter().map(|a| a.len()).max().unwrap_or(0);
                a.iter()
                    .map(AsRef::as_ref)
                    .chain(std::iter::repeat(""))
                    .zip(b.iter().map(AsRef::as_ref).chain(std::iter::repeat("")))
                    .take(max)
                    .map(|(a, b)|
                        format!(
                            "\x1b[{}m{:a_width$}\x1b[0m    {}=    \x1b[{}m{}\x1b[0m\n",
                            if a == b { "2" } else { "31" },
                            a,
                            if a == b { '=' } else { '!' },
                            if a == b { "2" } else { "32" },
                            b,
                            a_width = a_width,
                        )
                    )
                    .collect::<String>()
            },
        );
    };
}

#[test]
fn empty() {
    test_parse!("");
}

#[test]
fn heading() {
    test_parse!(
        "#\n",
        (Start(Section { id: "s-1".into() }, Attributes::new()), ""),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "s-1".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "s-1".into(),
            }),
            "",
        ),
        (End(Section { id: "s-1".into() }), ""),
    );
    test_parse!(
        "# abc\ndef\n",
        (
            Start(
                Section {
                    id: "abc-def".into(),
                },
                Attributes::new(),
            ),
            "",
        ),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "abc-def".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("abc".into()), "abc"),
        (Softbreak, "\n"),
        (Str("def".into()), "def"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "abc-def".into(),
            }),
            "",
        ),
        (
            End(Section {
                id: "abc-def".into(),
            }),
            "",
        ),
    );
}

#[test]
fn heading_attr() {
    test_parse!(
        concat!(
                "# abc\n",
                "{a=b}\n",
                "# def\n", //
            ),
        (Start(Section { id: "abc".into() }, Attributes::new()), ""),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "abc".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("abc".into()), "abc"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "abc".into(),
            }),
            "",
        ),
        (End(Section { id: "abc".into() }), ""),
        (
            Start(
                Section { id: "def".into() },
                attrs![(AttributeKind::Pair { key: "a".into() }, "b")],
            ),
            "{a=b}\n",
        ),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "def".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("def".into()), "def"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "def".into(),
            }),
            "",
        ),
        (End(Section { id: "def".into() }), ""),
    );
}

#[test]
fn heading_ref() {
    test_parse!(
        concat!(
            "A [link][Some Section] to another section.\n", //
            "\n",                                           //
            "# Some Section",                               //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("A ".into()), "A "),
        (
            Start(
                Link(
                    "#Some-Section".into(),
                    LinkType::Span(SpanLinkType::Reference),
                ),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("link".into()), "link"),
        (
            End(Link(
                "#Some-Section".into(),
                LinkType::Span(SpanLinkType::Reference),
            )),
            "][Some Section]",
        ),
        (Str(" to another section.".into()), " to another section."),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                Section {
                    id: "Some-Section".into(),
                },
                Attributes::new(),
            ),
            "",
        ),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "Some-Section".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("Some Section".into()), "Some Section"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "Some-Section".into(),
            }),
            "",
        ),
        (
            End(Section {
                id: "Some-Section".into(),
            }),
            "",
        ),
    );
    test_parse!(
        concat!(
            "[a][]\n", //
            "[b][]\n", //
            "\n",      //
            "# b\n",   //
            "\n",      //
            "# a\n",   //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("#a".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("a".into()), "a"),
        (
            End(Link("#a".into(), LinkType::Span(SpanLinkType::Reference))),
            "][]",
        ),
        (Softbreak, "\n"),
        (
            Start(
                Link("#b".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("b".into()), "b"),
        (
            End(Link("#b".into(), LinkType::Span(SpanLinkType::Reference))),
            "][]",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (Start(Section { id: "b".into() }, Attributes::new()), ""),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "b".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("b".into()), "b"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "b".into(),
            }),
            "",
        ),
        (Blankline, "\n"),
        (End(Section { id: "b".into() }), ""),
        (Start(Section { id: "a".into() }, Attributes::new()), ""),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "a".into(),
                },
                Attributes::new(),
            ),
            "#",
        ),
        (Str("a".into()), "a"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "a".into(),
            }),
            "",
        ),
        (End(Section { id: "a".into() }), ""),
    );
}

#[test]
fn blockquote() {
    test_parse!(
        ">\n",
        (Start(Blockquote, Attributes::new()), ">"),
        (Blankline, "\n"),
        (End(Blockquote), ""),
    );
}

#[test]
fn para() {
    test_parse!(
        "para",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "pa     ra",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("pa     ra".into()), "pa     ra"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "para0\n\npara1",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para0".into()), "para0"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para1".into()), "para1"),
        (End(Paragraph), ""),
    );
}

#[test]
fn verbatim() {
    test_parse!(
        "`abc\ndef",
        (Start(Paragraph, Attributes::new()), ""),
        (Start(Verbatim, Attributes::new()), "`"),
        (Str("abc\ndef".into()), "abc\ndef"),
        (End(Verbatim), ""),
        (End(Paragraph), ""),
    );
    test_parse!(
        concat!(
                "> `abc\n",
                "> def\n", //
            ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (Start(Verbatim, Attributes::new()), "`"),
        (Str("abc\n".into()), "abc\n"),
        (Str("def".into()), "def"),
        (End(Verbatim), ""),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
}

#[test]
fn raw_inline() {
    test_parse!(
        "``raw\nraw``{=format}",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                RawInline {
                    format: "format".into()
                },
                Attributes::new()
            ),
            "``",
        ),
        (Str("raw\nraw".into()), "raw\nraw"),
        (
            End(RawInline {
                format: "format".into()
            }),
            "``{=format}"
        ),
        (End(Paragraph), ""),
    );
}

#[test]
fn raw_block() {
    test_parse!(
        "``` =html\n<table>\n```",
        (
            Start(
                RawBlock {
                    format: "html".into()
                },
                Attributes::new()
            ),
            "``` =html\n",
        ),
        (Str("<table>".into()), "<table>"),
        (
            End(RawBlock {
                format: "html".into()
            }),
            "```"
        ),
    );
}

#[test]
fn raw_block_whitespace() {
    test_parse!(
        concat!(
            "```=html\n",  //
            "<tag1>\n",    //
            "<tag2>\n",    //
            "```\n",       //
            "\n",          //
            "paragraph\n", //
            "\n",          //
            "```=html\n",  //
            "</tag2>\n",   //
            "</tag1>\n",   //
            "```\n",       //
        ),
        (
            Start(
                RawBlock {
                    format: "html".into()
                },
                Attributes::new()
            ),
            "```=html\n",
        ),
        (Str("<tag1>\n".into()), "<tag1>\n"),
        (Str("<tag2>".into()), "<tag2>"),
        (
            End(RawBlock {
                format: "html".into()
            }),
            "```\n"
        ),
        (Blankline, "\n"),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("paragraph".into()), "paragraph"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                RawBlock {
                    format: "html".into()
                },
                Attributes::new()
            ),
            "```=html\n",
        ),
        (Str("</tag2>\n".into()), "</tag2>\n"),
        (Str("</tag1>".into()), "</tag1>"),
        (
            End(RawBlock {
                format: "html".into()
            }),
            "```\n"
        ),
    );
}

#[test]
fn symbol() {
    test_parse!(
        "abc :+1: def",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("abc ".into()), "abc "),
        (Symbol("+1".into()), ":+1:"),
        (Str(" def".into()), " def"),
        (End(Paragraph), ""),
    );
}

#[test]
fn link_inline() {
    test_parse!(
        "[text](url)",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Inline)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Inline))),
            "](url)",
        ),
        (End(Paragraph), ""),
    );
}

#[test]
fn link_inline_multi_line() {
    test_parse!(
        concat!(
            "> [text](url\n",
            "> url)\n", //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("urlurl".into(), LinkType::Span(SpanLinkType::Inline))),
            "](url\n> url)",
        ),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
    test_parse!(
        concat!(
            "> [text](a\n", //
            "> bc\n",       //
            "> def)\n",     //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("abcdef".into(), LinkType::Span(SpanLinkType::Inline)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("abcdef".into(), LinkType::Span(SpanLinkType::Inline))),
            "](a\n> bc\n> def)",
        ),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
}

#[test]
fn link_reference() {
    test_parse!(
        concat!(
            "[text][tag]\n",
            "\n",
            "[tag]: url\n" //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][tag]",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                Attributes::new()
            ),
            "[tag]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
    );
    test_parse!(
        concat!(
            "![text][tag]\n",
            "\n",
            "[tag]: url\n" //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Image("url".into(), SpanLinkType::Reference),
                Attributes::new(),
            ),
            "![",
        ),
        (Str("text".into()), "text"),
        (End(Image("url".into(), SpanLinkType::Reference)), "][tag]"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                Attributes::new()
            ),
            "[tag]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
    );
}

#[test]
fn link_reference_unresolved() {
    test_parse!(
        "[text][tag]",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("tag".into(), LinkType::Span(SpanLinkType::Unresolved))),
            "][tag]",
        ),
        (End(Paragraph), ""),
    );
    test_parse!(
        "![text][tag]",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Image("tag".into(), SpanLinkType::Unresolved),
                Attributes::new(),
            ),
            "![",
        ),
        (Str("text".into()), "text"),
        (End(Image("tag".into(), SpanLinkType::Unresolved)), "][tag]"),
        (End(Paragraph), ""),
    );
}

#[test]
fn link_reference_multiline() {
    test_parse!(
        concat!(
            "> [text][a\n", //
            "> b]\n",       //
            "\n",           //
            "[a b]: url\n", //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][a\n> b]",
        ),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "a b".into()
                },
                Attributes::new()
            ),
            "[a b]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "a b".into()
            }),
            ""
        ),
    );
}

#[test]
fn link_reference_multiline_empty() {
    test_parse!(
        concat!(
            "> [a\n",       //
            "> b][]\n",     //
            "> [a\\\n",     //
            "> b][]\n",     //
            "\n",           //
            "[a b]: url\n", //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("a".into()), "a"),
        (Softbreak, "\n"),
        (Str("b".into()), "b"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][]",
        ),
        (Softbreak, "\n"),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("a".into()), "a"),
        (Escape, "\\"),
        (Hardbreak, "\n"),
        (Str("b".into()), "b"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][]",
        ),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "a b".into()
                },
                Attributes::new()
            ),
            "[a b]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "a b".into()
            }),
            ""
        ),
    );
}

#[test]
fn link_definition_multiline() {
    test_parse!(
        concat!(
            "[text][tag]\n",
            "\n",
            "[tag]: u\n",
            " rl\n", //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][tag]",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                Attributes::new()
            ),
            "[tag]:",
        ),
        (Str("u".into()), "u"),
        (Str("rl".into()), "rl"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
    );
    test_parse!(
        concat!(
            "[text][tag]\n",
            "\n",
            "[tag]:\n",
            " url\n",  //
            " cont\n", //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("urlcont".into(), LinkType::Span(SpanLinkType::Reference)),
                Attributes::new(),
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link(
                "urlcont".into(),
                LinkType::Span(SpanLinkType::Reference),
            )),
            "][tag]",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                Attributes::new()
            ),
            "[tag]:",
        ),
        (Str("url".into()), "url"),
        (Str("cont".into()), "cont"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
    );
}

#[test]
fn link_reference_attrs() {
    test_parse!(
        concat!(
            "[text][tag]{b=c}\n",
            "\n",
            "{a=b}\n",
            "[tag]: url\n",
            "para\n",
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                attrs![
                    (AttributeKind::Pair { key: "a".into() }, "b"),
                    (AttributeKind::Pair { key: "b".into() }, "c"),
                ],
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][tag]{b=c}",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                attrs![(AttributeKind::Pair { key: "a".into() }, "b")],
            ),
            "{a=b}\n[tag]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
}

#[test]
fn link_reference_attrs_class() {
    test_parse!(
        concat!(
            "[text][tag]{.link}\n",
            "\n",
            "{.def}\n",
            "[tag]: url\n",
            "para\n",
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("url".into(), LinkType::Span(SpanLinkType::Reference)),
                attrs![
                    (AttributeKind::Class, "def"),
                    (AttributeKind::Class, "link"),
                ],
            ),
            "[",
        ),
        (Str("text".into()), "text"),
        (
            End(Link("url".into(), LinkType::Span(SpanLinkType::Reference))),
            "][tag]{.link}",
        ),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(
                LinkDefinition {
                    label: "tag".into()
                },
                attrs![(AttributeKind::Class, "def")],
            ),
            "{.def}\n[tag]:",
        ),
        (Str("url".into()), "url"),
        (
            End(LinkDefinition {
                label: "tag".into()
            }),
            ""
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
}

#[test]
fn autolink() {
    test_parse!(
        "<proto:url>\n",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("proto:url".into(), LinkType::AutoLink),
                Attributes::new(),
            ),
            "<",
        ),
        (Str("proto:url".into()), "proto:url"),
        (End(Link("proto:url".into(), LinkType::AutoLink)), ">"),
        (End(Paragraph), ""),
    );
}

#[test]
fn email() {
    test_parse!(
        "<name@domain>\n",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Link("name@domain".into(), LinkType::Email),
                Attributes::new(),
            ),
            "<",
        ),
        (Str("name@domain".into()), "name@domain"),
        (End(Link("name@domain".into(), LinkType::Email)), ">"),
        (End(Paragraph), ""),
    );
}

#[test]
fn footnote_references() {
    test_parse!(
        "[^a][^b][^c]",
        (Start(Paragraph, Attributes::new()), ""),
        (FootnoteReference("a".into()), "[^a]"),
        (FootnoteReference("b".into()), "[^b]"),
        (FootnoteReference("c".into()), "[^c]"),
        (End(Paragraph), ""),
    );
}

#[test]
fn footnote() {
    test_parse!(
        "[^a]\n\n[^a]: a\n",
        (Start(Paragraph, Attributes::new()), ""),
        (FootnoteReference("a".into()), "[^a]"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(Footnote { label: "a".into() }, Attributes::new()),
            "[^a]:"
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a".into()), "a"),
        (End(Paragraph), ""),
        (End(Footnote { label: "a".into() }), ""),
    );
}

#[test]
fn footnote_multiblock() {
    test_parse!(
        concat!(
            "[^a]\n",
            "\n",
            "[^a]: abc\n",
            "\n",
            " def", //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (FootnoteReference("a".into()), "[^a]"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(Footnote { label: "a".into() }, Attributes::new()),
            "[^a]:"
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("abc".into()), "abc"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("def".into()), "def"),
        (End(Paragraph), ""),
        (End(Footnote { label: "a".into() }), ""),
    );
}

#[test]
fn footnote_post() {
    test_parse!(
        concat!(
            "[^a]\n",
            "\n",
            "[^a]: note\n",
            "cont\n",
            "\n",
            "para\n", //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (FootnoteReference("a".into()), "[^a]"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(Footnote { label: "a".into() }, Attributes::new()),
            "[^a]:"
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("note".into()), "note"),
        (Softbreak, "\n"),
        (Str("cont".into()), "cont"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (End(Footnote { label: "a".into() }), ""),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
    test_parse!(
        concat!(
            "[^a]\n",       //
            "\n",           //
            "[^a]: note\n", //
            ":::\n",        //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (FootnoteReference("a".into()), "[^a]"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (
            Start(Footnote { label: "a".into() }, Attributes::new()),
            "[^a]:"
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("note".into()), "note"),
        (End(Paragraph), ""),
        (End(Footnote { label: "a".into() }), ""),
        (Start(Div { class: "".into() }, Attributes::new()), ":::\n"),
        (End(Div { class: "".into() }), ""),
    );
}

#[test]
fn attr_block() {
    test_parse!(
        "{.some_class}\npara\n",
        (
            Start(Paragraph, attrs![(AttributeKind::Class, "some_class")]),
            "{.some_class}\n",
        ),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
    test_parse!(
        concat!(
                "{.a}\n",
                "{#b}\n",
                "para\n", //
            ),
        (
            Start(
                Paragraph,
                attrs![(AttributeKind::Class, "a"), (AttributeKind::Id, "b")],
            ),
            "{.a}\n{#b}\n",
        ),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_block_dangling() {
    test_parse!(
        "{.a}",
        (Attributes(attrs![(AttributeKind::Class, "a")]), "{.a}"),
    );
    test_parse!(
        "para\n\n{.a}",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
        (Blankline, "\n"),
        (Attributes(attrs![(AttributeKind::Class, "a")]), "{.a}"),
    );
    test_parse!(
        "{.a}\n{.b}\n",
        (
            Attributes(attrs![
                (AttributeKind::Class, "a"),
                (AttributeKind::Class, "b")
            ]),
            "{.a}\n{.b}\n",
        ),
    );
}

#[test]
fn attr_block_dangling_end_of_block() {
    test_parse!(
        concat!(
            "# h\n",  //
            "\n",     //
            "{%cmt}", //
        ),
        (Start(Section { id: "h".into() }, Attributes::new()), ""),
        (
            Start(
                Heading {
                    level: 1,
                    has_section: true,
                    id: "h".into(),
                },
                Attributes::new(),
            ),
            "#"
        ),
        (Str("h".into()), "h"),
        (
            End(Heading {
                level: 1,
                has_section: true,
                id: "h".into(),
            }),
            ""
        ),
        (Blankline, "\n"),
        (
            Attributes(attrs![(AttributeKind::Comment, "cmt")]),
            "{%cmt}",
        ),
        (End(Section { id: "h".into() }), ""),
    );
    test_parse!(
        concat!(
            ":::\n",    //
            "{%cmt}\n", //
            ":::\n",    //
        ),
        (Start(Div { class: "".into() }, Attributes::new()), ":::\n"),
        (
            Attributes(attrs![(AttributeKind::Comment, "cmt")]),
            "{%cmt}\n"
        ),
        (End(Div { class: "".into() }), ":::\n"),
    );
}

#[test]
fn attr_block_blankline() {
    test_parse!(
        "{.a}\n\n{.b}\n\n{.c}\npara",
        (Attributes(attrs![(AttributeKind::Class, "a")]), "{.a}\n"),
        (Blankline, "\n"),
        (Attributes(attrs![(AttributeKind::Class, "b")]), "{.b}\n"),
        (Blankline, "\n"),
        (
            Start(Paragraph, attrs![(AttributeKind::Class, "c")]),
            "{.c}\n",
        ),
        (Str("para".into()), "para"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline() {
    test_parse!(
        "abc _def_{.ghi}",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("abc ".into()), "abc "),
        (Start(Emphasis, attrs![(AttributeKind::Class, "ghi")],), "_"),
        (Str("def".into()), "def"),
        (End(Emphasis), "_{.ghi}"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_consecutive() {
    test_parse!(
        "_abc def_{.a}{.b #i}",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Class, "a"),
                    (AttributeKind::Class, "b"),
                    (AttributeKind::Id, "i"),
                ],
            ),
            "_",
        ),
        (Str("abc def".into()), "abc def"),
        (End(Emphasis), "_{.a}{.b #i}"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "_abc def_{.a}{%%}{.b #i}",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Class, "a"),
                    (AttributeKind::Comment, ""),
                    (AttributeKind::Class, "b"),
                    (AttributeKind::Id, "i"),
                ],
            ),
            "_",
        ),
        (Str("abc def".into()), "abc def"),
        (End(Emphasis), "_{.a}{%%}{.b #i}"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_consecutive_invalid() {
    test_parse!(
        "_abc def_{.a}{.b #i}{.c invalid}",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Class, "a"),
                    (AttributeKind::Class, "b"),
                    (AttributeKind::Id, "i"),
                ],
            ),
            "_",
        ),
        (Str("abc def".into()), "abc def"),
        (End(Emphasis), "_{.a}{.b #i}"),
        (Str("{.c invalid}".into()), "{.c invalid}"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "_abc def_{.a}{.b #i}{%%}{.c invalid}",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Class, "a"),
                    (AttributeKind::Class, "b"),
                    (AttributeKind::Id, "i"),
                    (AttributeKind::Comment, ""),
                ],
            ),
            "_",
        ),
        (Str("abc def".into()), "abc def"),
        (End(Emphasis), "_{.a}{.b #i}{%%}"),
        (Str("{.c invalid}".into()), "{.c invalid}"),
        (End(Paragraph), ""),
    );
    test_parse!(
        concat!("_abc def_{.a}{.b #i}{%%}{.c\n", "invalid}\n"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Class, "a"),
                    (AttributeKind::Class, "b"),
                    (AttributeKind::Id, "i"),
                    (AttributeKind::Comment, ""),
                ],
            ),
            "_",
        ),
        (Str("abc def".into()), "abc def"),
        (End(Emphasis), "_{.a}{.b #i}{%%}"),
        (Str("{.c".into()), "{.c"),
        (Softbreak, "\n"),
        (Str("invalid}".into()), "invalid}"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_multiline() {
    test_parse!(
        concat!(
            "> _abc_{a=b\n", //
            "> c=d}\n",      //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Emphasis,
                attrs![
                    (AttributeKind::Pair { key: "a".into() }, "b"),
                    (AttributeKind::Pair { key: "c".into() }, "d"),
                ],
            ),
            "_",
        ),
        (Str("abc".into()), "abc"),
        (End(Emphasis), "_{a=b\n> c=d}"),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
    test_parse!(
        concat!(
            "> a{\n",   //
            "> %%\n",   //
            "> a=a}\n", //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Span,
                attrs![
                    (AttributeKind::Comment, ""),
                    (AttributeKind::Pair { key: "a".into() }, "a"),
                ],
            ),
            "",
        ),
        (Str("a".into()), "a"),
        (End(Span), "{\n> %%\n> a=a}"),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
    test_parse!(
        concat!(
            "> a{a=\"a\n", //
            "> b\n",       //
            "> c\"}\n",    //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(
                Span,
                attrs![(AttributeKind::Pair { key: "a".into() }, "a b c")],
            ),
            "",
        ),
        (Str("a".into()), "a"),
        (End(Span), "{a=\"a\n> b\n> c\"}"),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
    test_parse!(
        concat!(
            "> a{a=\"\n", //
            "> b\"}\n",   //
        ),
        (Start(Blockquote, Attributes::new()), ">"),
        (Start(Paragraph, Attributes::new()), ""),
        (
            Start(Span, attrs![(AttributeKind::Pair { key: "a".into() }, "b")]),
            "",
        ),
        (Str("a".into()), "a"),
        (End(Span), "{a=\"\n> b\"}"),
        (End(Paragraph), ""),
        (End(Blockquote), ""),
    );
}

#[test]
fn attr_inline_multiline_comment() {
    test_parse!(
        concat!(
            "a{%a\n", //
            "b\n",    //
            "c%}\n",  //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Start(Span, attrs![(AttributeKind::Comment, "a\nb\nc")]), "",),
        (Str("a".into()), "a"),
        (End(Span), "{%a\nb\nc%}"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_multiline_unclosed() {
    test_parse!(
        concat!(
            "a{\n", //
            " b\n", //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a{".into()), "a{"),
        (Softbreak, "\n"),
        (Str("b".into()), "b"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_multiline_invalid() {
    test_parse!(
        concat!(
            "a{a=b\n", //
            " b\n",    //
            "}",       //
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a{a=b".into()), "a{a=b"),
        (Softbreak, "\n"),
        (Str("b".into()), "b"),
        (Softbreak, "\n"),
        (Str("}".into()), "}"),
        (End(Paragraph), ""),
    );
}

#[test]
fn attr_inline_dangling() {
    test_parse!(
        "*a\n{%}",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("*a".into()), "*a"),
        (Softbreak, "\n"),
        (Attributes(attrs![(AttributeKind::Comment, "")]), "{%}"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "a {.b} c",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a ".into()), "a "),
        (Attributes(attrs![(AttributeKind::Class, "b")]), "{.b}"),
        (Str(" c".into()), " c"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "a {%cmt} c",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a ".into()), "a "),
        (
            Attributes(attrs![(AttributeKind::Comment, "cmt")]),
            "{%cmt}",
        ),
        (Str(" c".into()), " c"),
        (End(Paragraph), ""),
    );
    test_parse!(
        "a {%cmt}",
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a ".into()), "a "),
        (
            Attributes(attrs![(AttributeKind::Comment, "cmt")]),
            "{%cmt}",
        ),
        (End(Paragraph), ""),
    );
    test_parse!(
        "{%cmt} a",
        (Start(Paragraph, Attributes::new()), ""),
        (
            Attributes(attrs![(AttributeKind::Comment, "cmt")]),
            "{%cmt}",
        ),
        (Str(" a".into()), " a"),
        (End(Paragraph), ""),
    );
}

#[test]
fn list_item_unordered() {
    test_parse!(
        "- abc",
        (
            Start(
                List {
                    kind: ListKind::Unordered(Dash),
                    tight: true,
                },
                Attributes::new(),
            ),
            "",
        ),
        (Start(ListItem, Attributes::new()), "-"),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("abc".into()), "abc"),
        (End(Paragraph), ""),
        (End(ListItem), ""),
        (
            End(List {
                kind: ListKind::Unordered(Dash),
                tight: true,
            }),
            "",
        ),
    );
}

#[test]
fn list_item_ordered_decimal() {
    test_parse!(
        "123. abc",
        (
            Start(
                List {
                    kind: ListKind::Ordered {
                        numbering: Decimal,
                        style: Period,
                        start: 123,
                    },
                    tight: true,
                },
                Attributes::new(),
            ),
            "",
        ),
        (Start(ListItem, Attributes::new()), "123."),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("abc".into()), "abc"),
        (End(Paragraph), ""),
        (End(ListItem), ""),
        (
            End(List {
                kind: ListKind::Ordered {
                    numbering: Decimal,
                    style: Period,
                    start: 123,
                },
                tight: true,
            }),
            "",
        ),
    );
}

#[test]
fn list_task() {
    test_parse!(
        concat!(
            "- [ ] a\n", //
            "- [x] b\n", //
            "- [X] c\n", //
        ),
        (
            Start(
                List {
                    kind: ListKind::Task(Dash),
                    tight: true,
                },
                Attributes::new(),
            ),
            "",
        ),
        (
            Start(TaskListItem { checked: false }, Attributes::new()),
            "- [ ]",
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("a".into()), "a"),
        (End(Paragraph), ""),
        (End(TaskListItem { checked: false }), ""),
        (
            Start(TaskListItem { checked: true }, Attributes::new()),
            "- [x]",
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("b".into()), "b"),
        (End(Paragraph), ""),
        (End(TaskListItem { checked: true }), ""),
        (
            Start(TaskListItem { checked: true }, Attributes::new()),
            "- [X]",
        ),
        (Start(Paragraph, Attributes::new()), ""),
        (Str("c".into()), "c"),
        (End(Paragraph), ""),
        (End(TaskListItem { checked: true }), ""),
        (
            End(List {
                kind: ListKind::Task(Dash),
                tight: true,
            }),
            "",
        ),
    );
}

#[test]
fn table_consecutive() {
    test_parse!(
        concat!(
            "|a|\n", //
            "\n",    //
            "\n",    //
            "\n",    //
            "|b|\n", //
        ),
        (Start(Table, Attributes::new()), "".into()),
        (
            Start(TableRow { head: false }, Attributes::new()),
            "|".into(),
        ),
        (
            Start(
                TableCell {
                    alignment: Alignment::Unspecified,
                    head: false
                },
                Attributes::new(),
            ),
            "".into(),
        ),
        (Str("a".into()), "a".into()),
        (
            End(TableCell {
                alignment: Alignment::Unspecified,
                head: false
            }),
            "|".into(),
        ),
        (End(TableRow { head: false }), "".into()),
        (End(Table), "".into()),
        (Blankline, "\n".into()),
        (Blankline, "\n".into()),
        (Blankline, "\n".into()),
        (Start(Table, Attributes::new()), "".into()),
        (
            Start(TableRow { head: false }, Attributes::new()),
            "|".into(),
        ),
        (
            Start(
                TableCell {
                    alignment: Alignment::Unspecified,
                    head: false
                },
                Attributes::new()
            ),
            "".into(),
        ),
        (Str("b".into()), "b".into()),
        (
            End(TableCell {
                alignment: Alignment::Unspecified,
                head: false
            }),
            "|".into(),
        ),
        (End(TableRow { head: false }), "".into()),
        (End(Table), "".into()),
    );
}
