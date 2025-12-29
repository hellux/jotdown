use crate::Alignment;
use crate::OrderedListNumbering::*;
use crate::OrderedListStyle::*;

use super::Atom::*;
use super::Container::*;
use super::EventKind::*;
use super::FenceKind;
use super::Kind;
use super::Leaf::*;
use super::ListItemKind;
use super::ListNumber;
use super::ListType::*;
use super::Node::*;

macro_rules! test_parse {
    ($src:expr $(,$($event:expr),* $(,)?)?) => {
        let t = super::TreeParser::new($src).parse();
        let actual = t.into_iter().map(|ev| (ev.kind, &$src[ev.span])).collect::<Vec<_>>();
        let expected = &[$($($event),*,)?];
        assert_eq!(
            actual,
            expected,
            concat!(
                "\n",
                "\x1b[0;1m====================== INPUT =========================\x1b[0m\n",
                "\x1b[2m{}",
                "\x1b[0;1m================ ACTUAL vs EXPECTED ==================\x1b[0m\n",
                "{}",
                "\x1b[0;1m======================================================\x1b[0m\n",
            ),
            $src,
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
fn parse_para_oneline() {
    test_parse!(
        "para\n",
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_para_multiline() {
    test_parse!(
        "para0\npara1\n",
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para0\n"),
        (Inline, "para1"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_heading() {
    test_parse!(
        concat!(
            "# a\n",
            "## b\n", //
        ),
        (Enter(Container(Section { pos: 0 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            "#"
        ),
        (Inline, "a"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            ""
        ),
        (Enter(Container(Section { pos: 4 })), ""),
        (
            Enter(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 4
            })),
            "##"
        ),
        (Inline, "b"),
        (
            Exit(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 4
            })),
            ""
        ),
        (Exit(Container(Section { pos: 4 })), ""),
        (Exit(Container(Section { pos: 0 })), ""),
    );
}

#[test]
fn parse_heading_empty_first_line() {
    test_parse!(
        concat!(
            "#\n",
            "heading\n", //
        ),
        (Enter(Container(Section { pos: 0 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            "#"
        ),
        (Inline, "heading"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            ""
        ),
        (Exit(Container(Section { pos: 0 })), ""),
    );
}

#[test]
fn parse_heading_multi() {
    test_parse!(
        concat!(
            "# 2\n",    //
            "\n",       //
            " #   8\n", //
            "  12\n",   //
            "15\n",     //
        ),
        (Enter(Container(Section { pos: 0 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0,
            })),
            "#"
        ),
        (Inline, "2"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0,
            })),
            ""
        ),
        (Atom(Blankline), "\n"),
        (Exit(Container(Section { pos: 0 })), ""),
        (Enter(Container(Section { pos: 6 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 6,
            })),
            "#"
        ),
        (Inline, "8\n"),
        (Inline, "12\n"),
        (Inline, "15"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 6,
            })),
            ""
        ),
        (Exit(Container(Section { pos: 6 })), ""),
    );
}

#[test]
fn parse_heading_multi_repeat() {
    test_parse!(
        concat!(
            "# a\n",
            "# b\n",
            "c\n",   //
        ),
        (Enter(Container(Section { pos: 0 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            "#"
        ),
        (Inline, "a\n"),
        (Inline, "b\n"),
        (Inline, "c"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0
            })),
            "",
        ),
        (Exit(Container(Section { pos: 0 })), ""),
    );
}

#[test]
fn parse_section() {
    test_parse!(
        concat!(
            "# a\n",
            "\n",
            "## aa\n",
            "\n",
            "#### aaaa\n",
            "\n",
            "## ab\n",
            "\n",
            "### aba\n",
            "\n",
            "# b\n",
        ),
        (Enter(Container(Section { pos: 0 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0,
            })),
            "#"
        ),
        (Inline, "a"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 0,
            })),
            "",
        ),
        (Atom(Blankline), "\n"),
        (Enter(Container(Section { pos: 5 })), ""),
        (
            Enter(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 5,
            })),
            "##"
        ),
        (Inline, "aa"),
        (
            Exit(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 5,
            })),
            "",
        ),
        (Atom(Blankline), "\n"),
        (Enter(Container(Section { pos: 12 })), ""),
        (
            Enter(Leaf(Heading {
                level: 4,
                has_section: true,
                pos: 12,
            })),
            "####"
        ),
        (Inline, "aaaa"),
        (
            Exit(Leaf(Heading {
                level: 4,
                has_section: true,
                pos: 12,
            })),
            "",
        ),
        (Atom(Blankline), "\n"),
        (Exit(Container(Section { pos: 12 })), ""),
        (Exit(Container(Section { pos: 5 })), ""),
        (Enter(Container(Section { pos: 23 })), ""),
        (
            Enter(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 23,
            })),
            "##"
        ),
        (Inline, "ab"),
        (
            Exit(Leaf(Heading {
                level: 2,
                has_section: true,
                pos: 23,
            })),
            "",
        ),
        (Atom(Blankline), "\n"),
        (Enter(Container(Section { pos: 30 })), ""),
        (
            Enter(Leaf(Heading {
                level: 3,
                has_section: true,
                pos: 30,
            })),
            "###"
        ),
        (Inline, "aba"),
        (
            Exit(Leaf(Heading {
                level: 3,
                has_section: true,
                pos: 30,
            })),
            "",
        ),
        (Atom(Blankline), "\n"),
        (Exit(Container(Section { pos: 30 })), ""),
        (Exit(Container(Section { pos: 23 })), ""),
        (Exit(Container(Section { pos: 0 })), ""),
        (Enter(Container(Section { pos: 39 })), ""),
        (
            Enter(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 39,
            })),
            "#"
        ),
        (Inline, "b"),
        (
            Exit(Leaf(Heading {
                level: 1,
                has_section: true,
                pos: 39,
            })),
            "",
        ),
        (Exit(Container(Section { pos: 39 })), ""),
    );
}

#[test]
fn parse_blockquote() {
    test_parse!(
        "> a\n",
        (Enter(Container(Blockquote)), ">"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Blockquote)), ""),
    );
    test_parse!(
        "> a\nb\nc\n",
        (Enter(Container(Blockquote)), ">"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a\n"),
        (Inline, "b\n"),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Blockquote)), ""),
    );
    test_parse!(
        concat!(
            "> a\n",
            ">\n",
            "> ## hl\n",
            ">\n",
            ">  para\n", //
        ),
        (Enter(Container(Blockquote)), ">"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Leaf(Heading {
                level: 2,
                has_section: false,
                pos: 8,
            })),
            "##"
        ),
        (Inline, "hl"),
        (
            Exit(Leaf(Heading {
                level: 2,
                has_section: false,
                pos: 8,
            })),
            ""
        ),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Blockquote)), ""),
    );
}

#[test]
fn parse_blockquote_empty() {
    test_parse!(
        "> \n",
        (Enter(Container(Blockquote)), ">"),
        (Atom(Blankline), "\n"),
        (Exit(Container(Blockquote)), ""),
    );
    test_parse!(
        ">",
        (Enter(Container(Blockquote)), ">"),
        (Atom(Blankline), ""),
        (Exit(Container(Blockquote)), ""),
    );
}

#[test]
fn parse_code_block() {
    test_parse!(
        concat!(
            "```\n", //
            "l0\n"   //
        ),
        (Enter(Leaf(CodeBlock { language: "" })), "```\n",),
        (Inline, "l0\n"),
        (Exit(Leaf(CodeBlock { language: "" })), "",),
    );
    test_parse!(
        concat!(
            "```\n",  //
            "l0\n",   //
            "```\n",  //
            "\n",     //
            "para\n", //
        ),
        (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
        (Inline, "l0\n"),
        (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
    test_parse!(
        concat!(
            "````  lang\n",
            "l0\n",
            "```\n",
            " l1\n",
            "````", //
        ),
        (Enter(Leaf(CodeBlock { language: "lang" })), "````  lang\n",),
        (Inline, "l0\n"),
        (Inline, "```\n"),
        (Inline, " l1\n"),
        (Exit(Leaf(CodeBlock { language: "lang" })), "````"),
    );
    test_parse!(
        concat!(
            "```\n", //
            "a\n",   //
            "```\n", //
            "```\n", //
            "bbb\n", //
            "```\n", //
        ),
        (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
        (Inline, "a\n"),
        (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
        (Enter(Leaf(CodeBlock { language: "" })), "```\n"),
        (Inline, "bbb\n"),
        (Exit(Leaf(CodeBlock { language: "" })), "```\n"),
    );
    test_parse!(
        concat!(
            "~~~\n",
            "code\n",
            "  block\n",
            "~~~\n", //
        ),
        (Enter(Leaf(CodeBlock { language: "" })), "~~~\n"),
        (Inline, "code\n"),
        (Inline, "  block\n"),
        (Exit(Leaf(CodeBlock { language: "" })), "~~~\n"),
    );
    test_parse!(
        "    ```abc\n",
        (Enter(Leaf(CodeBlock { language: "abc" })), "```abc\n"),
        (Exit(Leaf(CodeBlock { language: "abc" })), ""),
    );
}

#[test]
fn parse_link_definition() {
    test_parse!(
        "[tag]: url\n",
        (Enter(Leaf(LinkDefinition { label: "tag" })), "[tag]:"),
        (Inline, "url"),
        (Exit(Leaf(LinkDefinition { label: "tag" })), ""),
    );
}

#[test]
fn parse_footnote() {
    test_parse!(
        "[^tag]: description\n",
        (Enter(Container(Footnote { label: "tag" })), "[^tag]:"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "description"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Footnote { label: "tag" })), ""),
    );
}

#[test]
fn parse_footnote_post() {
    test_parse!(
        concat!(
            "[^a]\n",
            "\n",
            "[^a]: note\n",
            "\n",
            "para\n", //
        ),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "[^a]"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Container(Footnote { label: "a" })), "[^a]:"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "note"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(Footnote { label: "a" })), ""),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_attr() {
    test_parse!(
        "{.some_class}\npara\n",
        (Atom(Attributes), "{.some_class}\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
    test_parse!(
        concat!(
            "{.a}\n", //
            "\n",     //
            "{.b}\n", //
            "\n",     //
            "para\n", //
        ),
        (Atom(Attributes), "{.a}\n"),
        (Atom(Blankline), "\n"),
        (Atom(Attributes), "{.b}\n"),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_list_single_item() {
    test_parse!(
        "- abc",
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "abc"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
    );
}

#[test]
fn parse_list_tight() {
    test_parse!(
        concat!(
            "- a\n", //
            "- b\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
    );
}

#[test]
fn parse_list_loose() {
    test_parse!(
        concat!(
            "- a\n", //
            "- b\n", //
            "\n",    //
            "- c\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: false,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: false,
            })),
            ""
        ),
    );
}

#[test]
fn parse_list_tight_loose() {
    test_parse!(
        concat!(
            "- a\n",    //
            "- b\n",    //
            "\n",       //
            "   - c\n", //
            "\n",       //
            "     d\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: false,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "d"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: false,
            })),
            ""
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
    );
}

#[test]
fn parse_list_tight_nest() {
    test_parse!(
        concat!(
            "- a\n",    //
            "\n",       //
            "  + aa\n", //
            "  + ab\n", //
            "\n",       //
            "- b\n",    //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'+'),
                tight: true,
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "+"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "aa"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "+"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "ab"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'+'),
                tight: true,
            })),
            "",
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
    );
    test_parse!(
        concat!(
            "1. a\n",  //
            "\n",      //
            "  - b\n", //
            "\n",      //
            " c\n",    //
        ),
        (
            Enter(Container(List {
                ty: Ordered(
                    ListNumber {
                        numbering: Decimal,
                        value: 1,
                    },
                    Period,
                ),
                tight: true,
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "1."),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            "",
        ),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Ordered(
                    ListNumber {
                        numbering: Decimal,
                        value: 1,
                    },
                    Period,
                ),
                tight: true,
            })),
            "",
        ),
    );
}

#[test]
fn parse_list_nest() {
    test_parse!(
        concat!(
            "- a\n",     //
            "    \n",    //
            "  + b\n",   //
            "      \n",  //
            "    * c\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'+'),
                tight: true,
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "+"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'*'),
                tight: true,
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "*"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'*'),
                tight: true,
            })),
            "",
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'+'),
                tight: true,
            })),
            "",
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
    );
}

#[test]
fn parse_list_post() {
    test_parse!(
        concat!(
            "- a\n",   //
            "\n",      //
            "  * b\n", //
            "\n",      //
            "cd\n",    //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'*'),
                tight: true
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "*"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'*'),
                tight: true
            })),
            ""
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "cd"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_list_mixed() {
    test_parse!(
        concat!(
            "- a\n", //
            "+ b\n", //
            "+ c\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            ""
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'+'),
                tight: true
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "+"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "+"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "c"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'+'),
                tight: true
            })),
            ""
        ),
    );
}

#[test]
fn parse_description_list() {
    test_parse!(
        concat!(
            ": term\n",         //
            "\n",               //
            "   description\n", //
        ),
        (
            Enter(Container(List {
                ty: Description,
                tight: true,
            })),
            ""
        ),
        (Stale, ":"),
        (Stale, ""),
        (Enter(Leaf(DescriptionTerm)), ":"),
        (Inline, "term"),
        (Exit(Leaf(DescriptionTerm)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Container(ListItem(ListItemKind::Description))), ""),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "description"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::Description))), ""),
        (
            Exit(Container(List {
                ty: Description,
                tight: true,
            })),
            ""
        ),
    );
    test_parse!(
        concat!(
            ": apple\n",
            "   fruit\n",
            "\n",
            "   Paragraph one\n",
            "\n",
            "   Paragraph two\n",
            "\n",
            "   - sub\n",
            "   - list\n",
            "\n",
            ": orange\n",
        ),
        (
            Enter(Container(List {
                ty: Description,
                tight: false
            })),
            "",
        ),
        (Stale, ":"),
        (Stale, ""),
        (Enter(Leaf(DescriptionTerm)), ":"),
        (Inline, "apple\n"),
        (Inline, "fruit"),
        (Exit(Leaf(DescriptionTerm)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Container(ListItem(ListItemKind::Description))), ""),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "Paragraph one"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "Paragraph two"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            "",
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "sub"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "list"),
        (Exit(Leaf(Paragraph)), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true
            })),
            "",
        ),
        (Exit(Container(ListItem(ListItemKind::Description))), ""),
        (Stale, ":"),
        (Stale, ""),
        (Enter(Leaf(DescriptionTerm)), ":"),
        (Inline, "orange"),
        (Exit(Leaf(DescriptionTerm)), ""),
        (Enter(Container(ListItem(ListItemKind::Description))), ""),
        (Exit(Container(ListItem(ListItemKind::Description))), ""),
        (
            Exit(Container(List {
                ty: Description,
                tight: false
            })),
            "",
        ),
    );
}

#[test]
fn parse_description_list_empty() {
    test_parse!(
        ":\n",
        (
            Enter(Container(List {
                ty: Description,
                tight: true,
            })),
            ""
        ),
        (Enter(Leaf(DescriptionTerm)), ":"),
        (Exit(Leaf(DescriptionTerm)), ""),
        (Enter(Container(ListItem(ListItemKind::Description))), ""),
        (Atom(Blankline), "\n"),
        (Exit(Container(ListItem(ListItemKind::Description))), ""),
        (
            Exit(Container(List {
                ty: Description,
                tight: true,
            })),
            ""
        ),
    );
}

#[test]
fn parse_table() {
    test_parse!(
        concat!(
            "|a|b|c|\n", //
            "|-|-|-|\n", //
            "|1|2|3|\n", //
        ),
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: true })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "a"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "b"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "c"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: true })), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "1"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "2"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "3"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), "")
    );
}

#[test]
fn parse_table_empty() {
    test_parse!(
        "||",
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, ""),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), ""),
    );
}

#[test]
fn parse_table_escaped() {
    test_parse!(
        "|a\\|\n",
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "|a\\|"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_table_post() {
    test_parse!(
        "|a|\npara",
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "a"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), ""),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_table_align() {
    test_parse!(
        concat!(
            "|:---|:----:|----:|\n",
            "|left|center|right|\n", //
        ),
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Left))), ""),
        (Inline, "left"),
        (Exit(Leaf(TableCell(Alignment::Left))), "|"),
        (Enter(Leaf(TableCell(Alignment::Center))), ""),
        (Inline, "center"),
        (Exit(Leaf(TableCell(Alignment::Center))), "|"),
        (Enter(Leaf(TableCell(Alignment::Right))), ""),
        (Inline, "right"),
        (Exit(Leaf(TableCell(Alignment::Right))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), "")
    );
    test_parse!(
        concat!(
            "||\n",   //
            "|-:|\n", //
        ),
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: true })), "|"),
        (Enter(Leaf(TableCell(Alignment::Right))), ""),
        (Inline, ""),
        (Exit(Leaf(TableCell(Alignment::Right))), "|"),
        (Exit(Container(TableRow { head: true })), ""),
        (Exit(Container(Table)), ""),
    );
}

#[test]
fn parse_table_caption() {
    test_parse!(
        "|a|\n^ caption",
        (Enter(Container(Table)), ""),
        (Enter(Leaf(Caption)), ""),
        (Inline, "caption"),
        (Exit(Leaf(Caption)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "a"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), ""),
    );
}

#[test]
fn parse_table_caption_multiline() {
    test_parse!(
        concat!(
            "|a|\n",       //
            "\n",          //
            "^ caption\n", //
            "continued\n", //
            "\n",          //
            "para\n",      //
        ),
        (Enter(Container(Table)), ""),
        (Enter(Leaf(Caption)), ""),
        (Inline, "caption\n"),
        (Inline, "continued"),
        (Exit(Leaf(Caption)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "a"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), ""),
        (Atom(Blankline), "\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "para"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_table_caption_empty() {
    test_parse!(
        "|a|\n^ ",
        (Enter(Container(Table)), ""),
        (Enter(Container(TableRow { head: false })), "|"),
        (Enter(Leaf(TableCell(Alignment::Unspecified))), ""),
        (Inline, "a"),
        (Exit(Leaf(TableCell(Alignment::Unspecified))), "|"),
        (Exit(Container(TableRow { head: false })), ""),
        (Exit(Container(Table)), ""),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "^"),
        (Exit(Leaf(Paragraph)), ""),
    );
}

#[test]
fn parse_table_sep_row_only() {
    test_parse!(
        "|-|-|",
        (Enter(Container(Table)), ""),
        (Exit(Container(Table)), "")
    );
}

#[test]
fn parse_div() {
    test_parse!(
        concat!(
            "::: cls\n", //
            "abc\n",     //
            ":::\n",     //
        ),
        (Enter(Container(Div { class: "cls" })), "::: cls\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "abc"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Div { class: "cls" })), ":::\n"),
    );
}

#[test]
fn parse_div_no_class() {
    test_parse!(
        concat!(
            ":::\n", //
            "abc\n", //
            ":::\n", //
        ),
        (Enter(Container(Div { class: "" })), ":::\n"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "abc"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(Div { class: "" })), ":::\n"),
    );
}

#[test]
fn parse_inner_indent() {
    test_parse!(
        concat!(
            "- - a\n", //
            "  - b\n", //
        ),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (
            Enter(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "a"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (Enter(Container(ListItem(ListItemKind::List))), "-"),
        (Enter(Leaf(Paragraph)), ""),
        (Inline, "b"),
        (Exit(Leaf(Paragraph)), ""),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
        (Exit(Container(ListItem(ListItemKind::List))), ""),
        (
            Exit(Container(List {
                ty: Unordered(b'-'),
                tight: true,
            })),
            ""
        ),
    );
}

macro_rules! test_block {
    ($src:expr, $kind:expr, $str:expr, $len:expr $(,)?) => {
        let lines = super::lines($src).map(|sp| &$src[sp]);
        let mb = super::MeteredBlock::new(lines).unwrap();
        assert_eq!(
            (mb.kind, &$src[mb.span], mb.line_count),
            ($kind, $str, $len),
            "\n\n{}\n\n",
            $src
        );
    };
}

#[test]
fn block_blankline() {
    test_block!("\n", Kind::Atom(Blankline), "\n", 1);
    test_block!(" \n", Kind::Atom(Blankline), "\n", 1);
}

#[test]
fn block_multiline() {
    test_block!(
        "# heading\n spanning two lines\n",
        Kind::Heading { level: 1 },
        "#",
        2
    );
}

#[test]
fn block_blockquote() {
    test_block!(
        concat!(
            "> a\n",    //
            ">\n",      //
            "  >  b\n", //
            ">\n",      //
            "> c\n",    //
        ),
        Kind::Blockquote,
        ">",
        5,
    );
}

#[test]
fn block_thematic_break() {
    test_block!("---\n", Kind::Atom(ThematicBreak), "---", 1);
    test_block!(
        concat!(
            "   -*- -*-\n",
            "\n",
            "para", //
        ),
        Kind::Atom(ThematicBreak),
        "-*- -*-",
        1
    );
}

#[test]
fn block_code_block() {
    test_block!(
        concat!(
            "````  lang\n",
            "l0\n",
            "```\n",
            " l1\n",
            "````", //
        ),
        Kind::Fenced {
            indent: 0,
            kind: FenceKind::CodeBlock(b'`'),
            fence_length: 4,
            spec: "lang",
            has_closing_fence: true,
            nested_raw: None,
        },
        "````  lang\n",
        5,
    );
    test_block!(
        concat!(
            "```\n", //
            "a\n",   //
            "```\n", //
            "```\n", //
            "bbb\n", //
            "```\n", //
        ),
        Kind::Fenced {
            indent: 0,
            kind: FenceKind::CodeBlock(b'`'),
            fence_length: 3,
            spec: "",
            has_closing_fence: true,
            nested_raw: None,
        },
        "```\n",
        3,
    );
    test_block!(
        concat!(
            "``` no space in lang specifier\n",
            "l0\n",
            "```\n", //
        ),
        Kind::Paragraph,
        "",
        3,
    );
}

#[test]
fn block_link_definition() {
    test_block!(
        "[tag]: url\n",
        Kind::Definition {
            indent: 0,
            footnote: false,
            label: "tag",
            last_blankline: false,
        },
        "[tag]:",
        1
    );
}

#[test]
fn block_link_definition_multiline() {
    test_block!(
        concat!(
            "[tag]: uuu\n",
            " rl\n", //
        ),
        Kind::Definition {
            indent: 0,
            footnote: false,
            label: "tag",
            last_blankline: false,
        },
        "[tag]:",
        2,
    );
    test_block!(
        concat!(
            "[tag]: url\n",
            "para\n", //
        ),
        Kind::Definition {
            indent: 0,
            footnote: false,
            label: "tag",
            last_blankline: false,
        },
        "[tag]:",
        1,
    );
}

#[test]
fn block_footnote_empty() {
    test_block!(
        "[^tag]:\n",
        Kind::Definition {
            indent: 0,
            footnote: true,
            label: "tag",
            last_blankline: false,
        },
        "[^tag]:",
        1
    );
}

#[test]
fn block_footnote_single() {
    test_block!(
        "[^tag]: a\n",
        Kind::Definition {
            indent: 0,
            footnote: true,
            label: "tag",
            last_blankline: false,
        },
        "[^tag]:",
        1
    );
}

#[test]
fn block_footnote_multiline() {
    test_block!(
        concat!(
            "[^tag]: a\n",
            " b\n", //
        ),
        Kind::Definition {
            indent: 0,
            footnote: true,
            label: "tag",
            last_blankline: false,
        },
        "[^tag]:",
        2,
    );
}

#[test]
fn block_footnote_multiline_post() {
    test_block!(
        concat!(
            "[^tag]: a\n",
            " b\n",
            "\n",
            "para\n", //
        ),
        Kind::Definition {
            indent: 0,
            footnote: true,
            label: "tag",
            last_blankline: false,
        },
        "[^tag]:",
        3,
    );
}

#[test]
fn block_list_bullet() {
    test_block!(
        "- abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Unordered(b'-'),
            last_blankline: false,
        },
        "-",
        1
    );
    test_block!(
        "+ abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Unordered(b'+'),
            last_blankline: false,
        },
        "+",
        1
    );
    test_block!(
        "* abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Unordered(b'*'),
            last_blankline: false,
        },
        "*",
        1
    );
}

#[test]
fn block_list_task() {
    test_block!(
        "- [ ] abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Task(b'-'),
            last_blankline: false,
        },
        "- [ ]",
        1
    );
    test_block!(
        "+ [x] abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Task(b'+'),
            last_blankline: false,
        },
        "+ [x]",
        1
    );
    test_block!(
        "* [X] abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Task(b'*'),
            last_blankline: false,
        },
        "* [X]",
        1
    );
}

#[test]
fn block_list_ordered() {
    test_block!(
        "123. abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Ordered(
                ListNumber {
                    numbering: Decimal,
                    value: 123,
                },
                Period,
            ),
            last_blankline: false,
        },
        "123.",
        1
    );
    test_block!(
        "i. abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Ordered(
                ListNumber {
                    numbering: RomanLower,
                    value: 1
                },
                Period,
            ),
            last_blankline: false,
        },
        "i.",
        1
    );
    test_block!(
        "I. abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Ordered(
                ListNumber {
                    numbering: RomanUpper,
                    value: 1,
                },
                Period,
            ),
            last_blankline: false,
        },
        "I.",
        1
    );
    test_block!(
        "(a) abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Ordered(
                ListNumber {
                    numbering: AlphaLower,
                    value: 1,
                },
                ParenParen,
            ),
            last_blankline: false,
        },
        "(a)",
        1
    );
    test_block!(
        "a) abc\n",
        Kind::ListItem {
            indent: 0,
            ty: Ordered(
                ListNumber {
                    numbering: AlphaLower,
                    value: 1,
                },
                Paren,
            ),
            last_blankline: false,
        },
        "a)",
        1
    );
}
