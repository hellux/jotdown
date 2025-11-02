use jotdown::AttributeKind;
use jotdown::AttributeKind::*;
use jotdown::AttributeValue;
use jotdown::Attributes;

macro_rules! test_attr {
    ($src:expr, [$($exp:expr),* $(,)?], [$($exp_uniq:expr),* $(,)?] $(,)?) => {
        #[allow(unused)]
        let mut attr = Attributes::try_from($src).unwrap();

        let actual = attr.iter().map(|(k, v)| (k.clone(), v.to_string())).collect::<Vec<_>>();
        let expected = &[$($exp),*].map(|(k, v): (_, &str)| (k, v.to_string()));
        assert_eq!(actual, expected, "\n\n{}\n\n", $src);

        let actual = attr.unique_pairs().map(|(k, v)| (k, v.to_string())).collect::<Vec<_>>();
        let expected = &[$($exp_uniq),*].map(|(k, v): (_, &str)| (k, v.to_string()));
        assert_eq!(actual, expected, "\n\n{}\n\n", $src);
    };
}

#[test]
fn empty() {
    test_attr!("{}", [], []);
}

#[test]
fn class_id() {
    test_attr!(
        "{.some_class #some_id}",
        [(Class, "some_class"), (Id, "some_id")],
        [("class", "some_class"), ("id", "some_id")],
    );
    test_attr!("{.a .b}", [(Class, "a"), (Class, "b")], [("class", "a b")]);
    test_attr!("{#a #b}", [(Id, "a"), (Id, "b")], [("id", "b")]);
}

#[test]
fn value_unquoted() {
    test_attr!(
        "{attr0=val0 attr1=val1}",
        [
            (
                Pair {
                    key: "attr0".into()
                },
                "val0"
            ),
            (
                Pair {
                    key: "attr1".into()
                },
                "val1"
            ),
        ],
        [("attr0", "val0"), ("attr1", "val1")],
    );
}

#[test]
fn value_quoted() {
    test_attr!(
        r#"{attr0="val0" attr1="val1"}"#,
        [
            (
                Pair {
                    key: "attr0".into()
                },
                "val0"
            ),
            (
                Pair {
                    key: "attr1".into()
                },
                "val1"
            ),
        ],
        [("attr0", "val0"), ("attr1", "val1")],
    );
    test_attr!(
        r#"{#id .class style="color:red"}"#,
        [
            (Id, "id"),
            (Class, "class"),
            (
                Pair {
                    key: "style".into()
                },
                "color:red"
            ),
        ],
        [("id", "id"), ("class", "class"), ("style", "color:red")]
    );
}

#[test]
fn value_newline() {
    test_attr!(
        "{attr0=\"abc\ndef\"}",
        [(
            Pair {
                key: "attr0".into()
            },
            "abc def"
        )],
        [("attr0", "abc def")]
    );
}

#[test]
fn comment() {
    test_attr!("{%}", [(Comment, "")], []);
    test_attr!("{%%}", [(Comment, "")], []);
    test_attr!("{ % abc % }", [(Comment, " abc ")], []);
    test_attr!(
        "{ .some_class % #some_id }",
        [(Class, "some_class"), (Comment, " #some_id ")],
        [("class", "some_class")]
    );
    test_attr!(
        "{ .some_class % abc % #some_id}",
        [(Class, "some_class"), (Comment, " abc "), (Id, "some_id")],
        [("class", "some_class"), ("id", "some_id")],
    );
}

#[test]
fn comment_newline() {
    test_attr!("{%a\nb%}", [(Comment, "a\nb")], []);
    test_attr!("{%\nb%}", [(Comment, "\nb")], []);
    test_attr!("{%a\n%}", [(Comment, "a\n")], []);
    test_attr!("{%a\n}", [(Comment, "a\n")], []);
    test_attr!("{%\nb\n%}", [(Comment, "\nb\n")], []);
}

#[test]
fn escape() {
    test_attr!(
        r#"{attr="with escaped \~ char"}"#,
        [(Pair { key: "attr".into() }, "with escaped ~ char")],
        [("attr", "with escaped ~ char")]
    );
    test_attr!(
        r#"{key="quotes \" should be escaped"}"#,
        [(Pair { key: "key".into() }, r#"quotes " should be escaped"#)],
        [("key", r#"quotes " should be escaped"#)]
    );
}

#[test]
fn escape_backslash() {
    test_attr!(
        r#"{attr="with\\backslash"}"#,
        [(Pair { key: "attr".into() }, r"with\backslash")],
        [("attr", r"with\backslash")]
    );
    test_attr!(
        r#"{attr="with many backslashes\\\\"}"#,
        [(Pair { key: "attr".into() }, r"with many backslashes\\")],
        [("attr", r"with many backslashes\\")]
    );
    test_attr!(
        r#"{attr="\\escaped backslash at start"}"#,
        [(Pair { key: "attr".into() }, r"\escaped backslash at start")],
        [("attr", r"\escaped backslash at start")]
    );
}

#[test]
fn only_escape_punctuation() {
    test_attr!(
        r#"{attr="do not \escape"}"#,
        [(Pair { key: "attr".into() }, r"do not \escape")],
        [("attr", r"do not \escape")]
    );
    test_attr!(
        r#"{attr="\backslash at the beginning"}"#,
        [(Pair { key: "attr".into() }, r"\backslash at the beginning")],
        [("attr", r"\backslash at the beginning")]
    );
}

#[test]
fn get_value_named() {
    assert_eq!(
        Attributes::try_from("{x=a}").unwrap().get_value("x"),
        Some("a".into()),
    );
    assert_eq!(
        Attributes::try_from("{x=a x=b}").unwrap().get_value("x"),
        Some("b".into()),
    );
}

#[test]
fn get_value_id() {
    assert_eq!(
        Attributes::try_from("{#a}").unwrap().get_value("id"),
        Some("a".into()),
    );
    assert_eq!(
        Attributes::try_from("{#a #b}").unwrap().get_value("id"),
        Some("b".into()),
    );
    assert_eq!(
        Attributes::try_from("{#a id=b}").unwrap().get_value("id"),
        Some("b".into()),
    );
    assert_eq!(
        Attributes::try_from("{id=a #b}").unwrap().get_value("id"),
        Some("b".into()),
    );
}

#[test]
fn get_value_class() {
    assert_eq!(
        Attributes::try_from("{.a #a .b #b .c}")
            .unwrap()
            .get_value("class"),
        Some("a b c".into()),
    );
    assert_eq!(
        Attributes::try_from("{#a}").unwrap().get_value("class"),
        None,
    );
    assert_eq!(
        Attributes::try_from("{.a}").unwrap().get_value("class"),
        Some("a".into()),
    );
    assert_eq!(
        Attributes::try_from("{.a #a class=b #b .c}")
            .unwrap()
            .get_value("class"),
        Some("a b c".into()),
    );
}

#[test]
fn from_to_vec() {
    let v0: Vec<(AttributeKind, AttributeValue)> = vec![(Class, "a".into()), (Id, "b".into())];
    let a: Attributes = v0.clone().into();
    assert_eq!(format!("{:?}", a), "{.a #b}");
    let v1: Vec<(AttributeKind, AttributeValue)> = a.into();
    assert_eq!(v0, v1);
}
