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
