use jotup::html::Indentation;
use jotup::RenderExt;

macro_rules! test_html {
    ($src:expr, $expected:expr $(,$indent:expr)? $(,)?) => {
        #[allow(unused)]
        let mut renderer = jotup::html::Renderer::minified();
        $(renderer = jotup::html::Renderer::indented($indent);)?
        renderer
            .render_document($src).expect("Can't fail");
        let actual = renderer.into_inner();
        assert_eq!(actual, $expected);
    };
    ($src:expr, $expected:expr, $(,)?) => {
        test_html!($src, $expected, Newlines)
    };
}

#[test]
fn mini_soft_break() {
    test_html!(
        concat!(
            "a\n", //
            "b\n",
        ),
        concat!(
            "<p>a\n", //
            "b</p>"
        ),
    );
}

#[test]
fn mini_hard_break() {
    test_html!(
        concat!(
            "a\\\n", //
            "b\n",
        ),
        "<p>a<br>b</p>",
    );
}

#[test]
fn mini_blank_line() {
    test_html!(
        concat!(
            "a\n", //
            "\n",  //
            "\n",  //
            "b\n",
        ),
        "<p>a</p><p>b</p>",
    );
}

#[test]
fn mini_code_block() {
    test_html!(
        concat!(
            "```\n", //
            "a\n",   //
            "b\n",   //
            "```\n",
        ),
        concat!(
            "<pre><code>a\n", //
            "b\n",
            "</code></pre>",
        ),
    );
}

#[test]
fn indent_para() {
    test_html!(
        concat!(
            "> a\n", //
            "> b\n",
        ),
        concat!(
            "<blockquote>\n", //
            "\t<p>a\n",
            "\tb</p>\n",
            "</blockquote>\n",
        ),
        Indentation::default(),
    );
}

#[test]
fn indent_code_block() {
    test_html!(
        concat!(
            "> ```\n", //
            "> fn x() {\n",
            ">     todo!()\n",
            "> }\n",
            "> ```\n",
        ),
        concat!(
            "<blockquote>\n",
            "\t<pre><code>fn x() {\n",
            "    todo!()\n",
            "}\n",
            "</code></pre>\n",
            "</blockquote>\n",
        ),
        Indentation::default(),
    );
}
