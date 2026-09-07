#[path = "modules/parse_events.rs"]
mod parse_events;

#[path = "modules/attr.rs"]
mod attr;

#[cfg(feature = "cli")]
#[path = "modules/cli.rs"]
mod cli;

#[cfg(feature = "html")]
#[path = "."]
mod html {
    #[path = "modules/html_indent.rs"]
    mod indent;

    mod ut {
        #[markup_test::test("tests/html-ut")]
        #[ignore(test_38d85f9 = "multi-line block attributes")]
        #[ignore(test_6c14561 = "multi-line block attributes")]
        #[ignore(test_45d4313 = "multi-line block attributes")]
        #[ignore(test_a25dde2 = "multi-line block attributes")]
        #[ignore(test_2fa94d1 = "bugged left/right quote")]
        #[ignore(test_a227d42 = "bugged left/right quote")]
        #[ignore(test_e1f5b5e = "untrimmed whitespace before linebreak")]
        #[ignore(test_8423412 = "heading id conflict with existing id")]
        #[ignore(test_a347df6 = "line break in footnote reference label")]
        #[ignore(test_1315fc6 = "line break in footnote reference label")]
        #[ignore(test_42828d8 = "extra space in footnote definition label not handled")]
        #[ignore(test_012c0fc = "different class / src order in <img> element")]
        #[ignore(test_a5dde08 = "span with empty attributes not present in html")]
        #[disable(a = "ast test")]
        #[disable(ap = "ast pos test")]
        fn html(input: &str, expected: &str) {
            let actual = jotdown::html::render_to_string(jotdown::Parser::new(input));
            crate::assert_eq(&actual, expected, input);
        }
    }
}

mod list_bullet_type {
    #[test]
    fn to_u8() {
        assert_eq!(u8::from(jotdown::ListBulletType::Dash), b'-');
        assert_eq!(u8::from(jotdown::ListBulletType::Star), b'*');
        assert_eq!(u8::from(jotdown::ListBulletType::Plus), b'+');
    }

    #[test]
    fn to_char() {
        assert_eq!(char::from(jotdown::ListBulletType::Dash), '-');
        assert_eq!(char::from(jotdown::ListBulletType::Star), '*');
        assert_eq!(char::from(jotdown::ListBulletType::Plus), '+');
    }

    #[test]
    fn from_u8() {
        assert_eq!(b'-'.try_into(), Ok(jotdown::ListBulletType::Dash));
        assert_eq!(b'*'.try_into(), Ok(jotdown::ListBulletType::Star));
        assert_eq!(b'+'.try_into(), Ok(jotdown::ListBulletType::Plus));
        assert_eq!(jotdown::ListBulletType::try_from(b'='), Err(()));
    }

    #[test]
    fn from_char() {
        assert_eq!('-'.try_into(), Ok(jotdown::ListBulletType::Dash));
        assert_eq!('*'.try_into(), Ok(jotdown::ListBulletType::Star));
        assert_eq!('+'.try_into(), Ok(jotdown::ListBulletType::Plus));
        assert_eq!(jotdown::ListBulletType::try_from('='), Err(()));
    }
}

#[cfg(feature = "html")]
mod render {
    #[test]
    fn write_events() {
        use jotdown::Render;
        let mut bytes = Vec::new();
        jotdown::html::Renderer::default()
            .write_events(
                jotdown::Parser::new("para"),
                &mut std::io::BufWriter::new(std::io::Cursor::new(&mut bytes)),
            )
            .unwrap();
        assert_eq!(std::str::from_utf8(&bytes).unwrap(), "<p>para</p>\n");
    }

    #[test]
    fn write_events_error() {
        use jotdown::Render;

        struct FailingWriter;
        impl std::io::Write for FailingWriter {
            fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "some io error",
                ))
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        assert_eq!(
            format!(
                "{:?}",
                jotdown::html::Renderer::default()
                    .write_events(jotdown::Parser::new("para"), &mut FailingWriter)
            ),
            r#"Err(Custom { kind: Other, error: "some io error" })"#,
        );
    }
}

fn assert_eq(actual: &str, expected: &str, input: &str) {
    assert_eq!(
        actual.trim(),
        expected.trim(),
        concat!(
            "\n",
            "\x1b[0;1m========================= INPUT ============================\x1b[0m\n",
            "\x1b[2m{}",
            "\x1b[0;1m=================== ACTUAL vs EXPECTED =====================\x1b[0m\n",
            "{}",
            "\x1b[0;1m============================================================\x1b[0m\n",
        ),
        input,
        {
            let a = actual.trim().split('\n');
            let b = expected.trim().split('\n');
            let max = a.clone().count().max(b.clone().count());
            let a_width = a.clone().map(|a| a.len()).max().unwrap_or(0);
            a.chain(std::iter::repeat(""))
                .zip(b.chain(std::iter::repeat("")))
                .take(max)
                .map(|(a, b)| {
                    format!(
                        "\x1b[{}m{:a_width$}\x1b[0m    {}=    \x1b[{}m{}\x1b[0m\n",
                        if a == b { "2" } else { "31" },
                        a,
                        if a == b { '=' } else { '!' },
                        if a == b { "2" } else { "32" },
                        b,
                        a_width = a_width,
                    )
                })
                .collect::<String>()
        },
    );
}
