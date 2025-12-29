#[test]
fn valid_full() {
    let src = "{.class %comment%}";
    assert_eq!(super::valid(src), src.len());
}

#[test]
fn valid_unicode() {
    let src = r#"{a="б"}"#;
    assert_eq!(super::valid(src), src.len());
}

#[test]
fn valid_empty() {
    let src = "{}";
    assert_eq!(super::valid(src), src.len());
}

#[test]
fn valid_whitespace() {
    let src = "{ \n }";
    assert_eq!(super::valid(src), src.len());
}

#[test]
fn valid_comment() {
    let src = "{%comment%}";
    assert_eq!(super::valid(src), src.len());
}

#[test]
fn valid_trailing() {
    let src = "{.class}{.ignore}";
    let src_valid = "{.class}";
    assert_eq!(super::valid(src), src_valid.len());
}
