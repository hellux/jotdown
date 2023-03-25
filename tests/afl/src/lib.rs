use jotdown::Render;

use html5ever::tendril;
use html5ever::tendril::TendrilSink;
use html5ever::tokenizer;
use html5ever::tree_builder;

pub fn parse(data: &[u8]) {
    if let Ok(s) = std::str::from_utf8(data) {
        jotdown::Parser::new(s).last();
    }
}

pub fn html(data: &[u8]) {
    if data.iter().any(|i| *i == 0) {
        return;
    }
    if let Ok(s) = std::str::from_utf8(data) {
        if !s.contains("=html") {
            let p = jotdown::Parser::new(s);
            let mut html = "<!DOCTYPE html>\n".to_string();
            jotdown::html::Renderer::default()
                .push(p, &mut html)
                .unwrap();
            validate_html(&html);
        }
    }
}

fn validate_html(html: &str) {
    #[cfg(feature = "debug")]
    let mut has_error = false;

    html5ever::parse_document(
        Dom {
            names: Vec::new(),
            #[cfg(feature = "debug")]
            has_error: &mut has_error,
            #[cfg(feature = "debug")]
            line_no: 1,
            #[cfg(not(feature = "debug"))]
            _lifetime: std::marker::PhantomData,
        },
        html5ever::ParseOpts {
            tokenizer: tokenizer::TokenizerOpts {
                exact_errors: true,
                ..tokenizer::TokenizerOpts::default()
            },
            tree_builder: tree_builder::TreeBuilderOpts {
                exact_errors: true,
                scripting_enabled: false,
                ..tree_builder::TreeBuilderOpts::default()
            },
        },
    )
    .from_utf8()
    .read_from(&mut std::io::Cursor::new(html))
    .unwrap();

    #[cfg(feature = "debug")]
    if has_error {
        eprintln!("html:");
        html.split('\n').enumerate().for_each(|(i, l)| {
            eprintln!("{:>2}:{}", i + 1, l);
        });
        eprintln!("\n");
        panic!();
    }
}

struct Dom<'a> {
    names: Vec<html5ever::QualName>,
    #[cfg(feature = "debug")]
    has_error: &'a mut bool,
    #[cfg(feature = "debug")]
    line_no: u64,
    #[cfg(not(feature = "debug"))]
    _lifetime: std::marker::PhantomData<&'a ()>,
}

impl<'a> tree_builder::TreeSink for Dom<'a> {
    type Handle = usize;
    type Output = Self;

    fn get_document(&mut self) -> usize {
        0
    }

    fn finish(self) -> Self {
        self
    }

    fn same_node(&self, x: &usize, y: &usize) -> bool {
        x == y
    }

    fn elem_name(&self, i: &usize) -> html5ever::ExpandedName {
        self.names[i - 1].expanded()
    }

    fn create_element(
        &mut self,
        name: html5ever::QualName,
        _: Vec<html5ever::Attribute>,
        _: tree_builder::ElementFlags,
    ) -> usize {
        self.names.push(name);
        self.names.len()
    }

    fn parse_error(&mut self, msg: std::borrow::Cow<'static, str>) {
        let whitelist = &[
            "Bad character",       // bad characters in input will pass through
            "Duplicate attribute", // djot is case-sensitive while html is not
            // tags may be nested incorrectly, e.g. <a> within <a>
            "Unexpected token Tag",
            "Found special tag while closing generic tag",
            "Formatting element not current node",
            "Formatting element not open",
            // FIXME bug caused by empty table at end of list
            "No matching tag to close",
            "Unexpected open element while closing",
        ];
        if !whitelist.iter().any(|e| msg.starts_with(e)) {
            #[cfg(feature = "debug")]
            {
                *self.has_error = true;
                eprintln!("{}: {}\n", self.line_no, msg);
            }
            #[cfg(not(feature = "debug"))]
            {
                panic!("invalid html");
            }
        }
    }

    fn set_quirks_mode(&mut self, _: tree_builder::QuirksMode) {}

    #[cfg(feature = "debug")]
    fn set_current_line(&mut self, l: u64) {
        self.line_no = l;
    }
    #[cfg(not(feature = "debug"))]
    fn set_current_line(&mut self, _: u64) {}

    fn append(&mut self, _: &usize, _: tree_builder::NodeOrText<usize>) {}
    fn append_before_sibling(&mut self, _: &usize, _: tree_builder::NodeOrText<usize>) {}
    fn append_based_on_parent_node(
        &mut self,
        _: &usize,
        _: &usize,
        _: tree_builder::NodeOrText<usize>,
    ) {
    }
    fn append_doctype_to_document(
        &mut self,
        _: tendril::StrTendril,
        _: tendril::StrTendril,
        _: tendril::StrTendril,
    ) {
    }
    fn remove_from_parent(&mut self, _: &usize) {}
    fn reparent_children(&mut self, _: &usize, _: &usize) {}

    fn mark_script_already_started(&mut self, _: &usize) {}

    fn add_attrs_if_missing(&mut self, _: &usize, _: Vec<html5ever::Attribute>) {
        panic!();
    }

    fn create_pi(&mut self, _: tendril::StrTendril, _: tendril::StrTendril) -> usize {
        panic!()
    }

    fn get_template_contents(&mut self, _: &usize) -> usize {
        panic!();
    }

    fn create_comment(&mut self, _: tendril::StrTendril) -> usize {
        panic!()
    }
}
