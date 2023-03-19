#[rustfmt::skip]
#[cfg(feature = "suite_bench")]
mod bench;
#[rustfmt::skip]
#[cfg(feature = "suite")]
mod suite;

#[cfg(any(feature = "suite", feature = "suite_bench"))]
#[macro_export]
macro_rules! suite_test {
    ($src:expr, $expected:expr) => {
        use jotdown::Render;
        let src = $src;
        let expected = $expected;
        let p = jotdown::Parser::new(src);
        let mut actual = String::new();
        jotdown::html::Renderer::default()
            .push(p, &mut actual)
            .unwrap();
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
            $src,
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
    };
}
