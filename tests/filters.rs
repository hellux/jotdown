use jotdown::{Container, Event, Render, RenderExt as _, RenderOutput};
use std::borrow::Cow;

struct RickrollRenderer<R>(R);

impl<'s, R> Render<'s> for RickrollRenderer<R>
where
    R: Render<'s>,
{
    type Error = R::Error;

    fn begin(&mut self) -> Result<(), Self::Error> {
        self.0.begin()
    }

    fn emit(&mut self, event: Event<'s>) -> Result<(), Self::Error> {
        match event {
            Event::Start(Container::Link(_link, t), attrs) => self.0.emit(Event::Start(
                Container::Link(
                    Cow::Owned("https://www.youtube.com/watch?v=E4WlUXrJgy4".to_owned()),
                    t,
                ),
                attrs,
            )),
            _ => self.0.emit(event),
        }
    }

    fn finish(&mut self) -> Result<(), Self::Error> {
        self.0.finish()
    }
}

impl<'s, R> RenderOutput<'s> for RickrollRenderer<R>
where
    R: RenderOutput<'s>,
{
    type Output = R::Output;

    fn into_output(self) -> Self::Output {
        self.0.into_output()
    }
}

#[test]
fn rickroll_me() {
    use jotdown::RenderOutputExt;
    let src = "[interesting link](https://example.com)";
    let out = RickrollRenderer(jotdown::html::Renderer::minified())
        .render_into_document(src)
        .unwrap();

    assert_eq!(
        out,
        "<p><a href=\"https://www.youtube.com/watch?v=E4WlUXrJgy4\">interesting link</a></p>"
    );
}
