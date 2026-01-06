#![no_main]

use libfuzzer_sys::fuzz_target;
use jotup::{Parser, RenderExt};
use jotup::r#async::AsyncRenderExt;

fuzz_target!(|data: &[u8]| {
    // Convert bytes to valid UTF-8 string, return early if invalid
    let input = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    // Parse the input once to get events
    let events: Vec<_> = Parser::new(input).collect();

    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .expect("Failed to create tokio runtime");

    // Test default renderer (newlines, no indentation)
    {
        let mut sync_renderer = jotdown::html::Renderer::default();
        sync_renderer.render_events(events.iter().cloned()).expect("Rendering to String cannot fail");
        let sync_html = sync_renderer.into_inner();

        let async_html = rt.block_on(async {
            let mut renderer = jotdown::html::tokio::Renderer::default();
            renderer.render_events(events.iter().cloned()).await.expect("Rendering to String cannot fail");
            let bytes = renderer.into_inner().into_inner();
            String::from_utf8(bytes).expect("HTML output must be valid UTF-8")
        });

        assert_eq!(
            sync_html, async_html,
            "Default: Sync and async renderers produced different HTML output!\nInput: {:?}\nSync: {:?}\nAsync: {:?}",
            input, sync_html, async_html
        );
    }

    // Test minified renderer (no whitespace)
    {
        let mut sync_renderer = jotdown::html::Renderer::minified();
        sync_renderer.render_events(events.iter().cloned()).expect("Rendering to String cannot fail");
        let sync_html = sync_renderer.into_inner();

        let async_html = rt.block_on(async {
            let mut renderer = jotdown::html::tokio::Renderer::minified();
            renderer.render_events(events.iter().cloned()).await.expect("Rendering to String cannot fail");
            let bytes = renderer.into_inner().into_inner();
            String::from_utf8(bytes).expect("HTML output must be valid UTF-8")
        });

        assert_eq!(
            sync_html, async_html,
            "Minified: Sync and async renderers produced different HTML output!\nInput: {:?}\nSync: {:?}\nAsync: {:?}",
            input, sync_html, async_html
        );
    }

    // Test indented renderer (with tab indentation)
    {
        let mut sync_renderer = jotdown::html::Renderer::indented(jotdown::html::Indentation::default());
        sync_renderer.render_events(events.iter().cloned()).expect("Rendering to String cannot fail");
        let sync_html = sync_renderer.into_inner();

        let async_html = rt.block_on(async {
            let mut renderer = jotdown::html::tokio::Renderer::indented(jotdown::html::tokio::Indentation::default());
            renderer.render_events(events.iter().cloned()).await.expect("Rendering to String cannot fail");
            let bytes = renderer.into_inner().into_inner();
            String::from_utf8(bytes).expect("HTML output must be valid UTF-8")
        });

        assert_eq!(
            sync_html, async_html,
            "Indented: Sync and async renderers produced different HTML output!\nInput: {:?}\nSync: {:?}\nAsync: {:?}",
            input, sync_html, async_html
        );
    }
});
