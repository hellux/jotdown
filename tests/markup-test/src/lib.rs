#[derive(Default, Debug)]
struct TestDecl {
    name: String,
    input: String,
    output: String,
    ignore: Option<String>,
}

#[proc_macro_attribute]
pub fn glob(
    args: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let glob = syn::parse_macro_input!(args as syn::LitStr).value();
    let mut dut_fn = syn::parse_macro_input!(item as syn::ItemFn);

    let mut test_files = Vec::new();
    for e in glob::glob(&glob).unwrap() {
        let e = e.expect("failed to read glob entry");
        let path = e.as_path();
        if std::fs::File::open(path).is_ok()
            && path.extension().and_then(|e| e.to_str()) == Some("test")
        {
            test_files.push(path.to_owned());
        }
    }
    assert!(!test_files.is_empty(), "No files matched '{glob}'");

    let mut disable = std::collections::HashMap::new();
    let mut ignore = std::collections::HashMap::new();
    for attr in dut_fn.attrs.drain(..) {
        let kv = |input: syn::parse::ParseStream<'_>| {
            let key = input.parse::<syn::Ident>()?;
            input.parse::<syn::Token![=]>()?;
            let value = input.parse::<syn::LitStr>()?;

            Ok::<_, syn::Error>((key, value))
        };
        match attr.path().get_ident().unwrap().to_string().as_str() {
            "disable" => {
                let (key, value) = attr.parse_args_with(kv).unwrap();
                disable.insert(key.to_string(), value.value());
            }
            "ignore" => {
                let (key, value) = attr.parse_args_with(kv).unwrap();
                ignore.insert(key.to_string(), value.value());
            }
            _ => panic!("unhandled attr: {attr:?}"),
        }
    }

    let mut modules = Vec::new();
    for f in &test_files {
        let src = std::fs::read_to_string(f).expect("failed to read file");

        let mut test_decls: Vec<TestDecl> = Vec::new();
        let mut decl_current = None;
        let mut output_started = false;
        for (e, sp) in jotdown::Parser::new(&src).into_offset_iter() {
            let loc = format!(
                "{}:{}",
                f.display(),
                src[..sp.start].chars().filter(|c| *c == '\n').count() + 1
            );

            match e {
                jotdown::Event::Start(jotdown::Container::CodeBlock { language, .. }, a) => {
                    assert!(a.is_empty(), "unexpected attrs at {loc}");
                    assert!(decl_current.is_none());
                    decl_current = Some(TestDecl {
                        name: language.to_string(),
                        ..TestDecl::default()
                    });
                    output_started = false;
                }
                jotdown::Event::Str(s, ..) => {
                    if let Some(decl) = &mut decl_current {
                        if s == ".\n" && !output_started {
                            output_started = true;
                        } else if output_started {
                            decl.output.push_str(&s)
                        } else {
                            decl.input.push_str(&s);
                        }
                    }
                }
                jotdown::Event::End(jotdown::Container::CodeBlock { .. }) => {
                    assert!(!sp.is_empty(), "unclosed code block at {loc}");
                    let mut decl = decl_current.take().unwrap();
                    if output_started {
                        if decl.input == decl.output {
                            eprintln!(
                                "warning: {} has identical input and output (output can be omitted)",
                                decl.name,
                            );
                        }
                    } else {
                        decl.output = decl.input.clone();
                    }
                    if decl.name.is_empty() {
                        decl.name = format!(
                            "test_{}",
                            &format!("{:x}", md5::compute(decl.input.as_bytes()))[..7],
                        );
                    }
                    if !disable.contains_key(&decl.name) {
                        decl.ignore = ignore.get(&decl.name).cloned();
                        assert!(
                            test_decls.iter().all(|t| t.name != decl.name),
                            "duplicate test name {} at {loc}",
                            decl.name,
                        );
                        test_decls.push(decl);
                    }
                }
                e => match e {
                    jotdown::Event::Start(c, _) | jotdown::Event::End(c) => match c {
                        jotdown::Container::Document
                        | jotdown::Container::Paragraph
                        | jotdown::Container::Section { .. }
                        | jotdown::Container::Heading { .. } => {}
                        c if c.is_inline() => {}
                        _ => panic!("unexpected container {c:?} at {loc}"),
                    },
                    jotdown::Event::Blankline | jotdown::Event::Str(..) => {}
                    e if e.is_inline() => {}
                    _ => panic!("unexpected event {e:?} at {loc}"),
                },
            }
        }

        modules.push((f.file_stem().unwrap().to_string_lossy(), test_decls));
    }

    let modules = modules.iter().map(|(mod_name, test_decls)| {
        let mod_name = syn::Ident::new(mod_name, proc_macro2::Span::call_site());
        let tests = test_decls
            .iter()
            .map(|t| {
                let uut_fn_name = &dut_fn.sig.ident;
                let test_name = syn::Ident::new(&t.name, proc_macro2::Span::call_site());
                let input = &t.input;
                let output = &t.output;
                let ignore = t.ignore.iter();
                quote::quote! {
                    #(
                        #[ignore = #ignore]
                    )*
                    #[test]
                    fn #test_name() {
                        super::#uut_fn_name(#input, #output);
                    }
                }
            })
            .collect::<Vec<_>>();

        quote::quote! {
            mod #mod_name {
                #(#tests)*
            }
        }
    });

    quote::quote! {
        #dut_fn

        #(#modules)*
    }
    .into()
}
