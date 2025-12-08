use crate::{Attributes, Container, Event, Render, RenderOutput};

/// Sanitize html rendering
///
/// Rendering filter that will strip rendered djot document
/// from things that could be used to inject arbitrary
/// html and styling to the rendered output, leaving
/// only content that is safe to display directly as html
/// from an untrusted djot input.
///
/// ````
/// use jotdown::{Render, RenderOutputExt};
/// use jotdown::html::filters::SanitizeExt;
///
/// let src = r#"
/// ```=html
/// <p>foo</p>
/// ```
/// "#;
/// let out = jotdown::html::Renderer::minified()
///   .sanitize()
///   .render_into_document(src)
///   .unwrap();
///
/// assert_eq!(
///   out,
///   "<pre><code class=\"language-html\">&lt;p&gt;foo&lt;/p&gt;</code></pre>"
/// );
/// ````
pub struct Sanitize<R>(R);

impl<'s, R> Render<'s> for Sanitize<R>
where
    R: Render<'s>,
{
    type Error = R::Error;

    fn begin(&mut self) -> Result<(), Self::Error> {
        self.0.begin()
    }

    fn emit(&mut self, event: Event<'s>) -> Result<(), Self::Error> {
        match event {
            // Render raw html as code blocks to avoid arbitrary html injection.
            Event::Start(Container::RawBlock { format }, _attrs)
            | Event::Start(Container::RawInline { format }, _attrs)
                if format == "html" =>
            {
                self.0.emit(Event::Start(
                    Container::CodeBlock { language: format },
                    Attributes::new(),
                ))
            }
            // Strip all attributes from containers
            Event::Start(container, _attrs) => {
                self.0.emit(Event::Start(container, Attributes::new()))
            }
            _ => self.0.emit(event),
        }
    }

    fn finish(&mut self) -> Result<(), Self::Error> {
        self.0.finish()
    }
}

impl<'s, R> RenderOutput<'s> for Sanitize<R>
where
    R: RenderOutput<'s>,
{
    type Output = R::Output;

    fn into_output(self) -> Self::Output {
        self.0.into_output()
    }
}

pub trait SanitizeExt {
    fn sanitize(self) -> Sanitize<Self>
    where
        Self: Sized,
    {
        Sanitize(self)
    }
}

impl<'s, R> SanitizeExt for R where R: Sized + Render<'s> {}

#[test]
fn sanitize_me() {
    use crate::RenderOutputExt;
    let src = r#"
```=html
<p>foo</p>
```
"#;
    let out = super::Renderer::minified()
        .sanitize()
        .render_into_document(src)
        .unwrap();

    assert_eq!(
        out,
        "<pre><code class=\"language-html\">&lt;p&gt;foo&lt;/p&gt;</code></pre>"
    );
}
