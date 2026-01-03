//! Async rendering traits for Djot documents.

use crate::{Attributes, Container, Event, Parser};

/// An async implementation of rendering a djot document
///
/// This interface will be called by the djot parser with elements
/// parsed by it.
#[async_trait::async_trait]
pub trait AsyncRender<'s> {
    type Error;

    /// Called iteratively with every single event emitted by parsing djot document
    async fn emit(&mut self, event: Event<'s>) -> Result<(), Self::Error>;
}

/// Utility extensions method for [`AsyncRender`] trait
#[async_trait::async_trait]
pub trait AsyncRenderExt<'s>: AsyncRender<'s> {
    /// Parse and render the whole document with `renderer`
    async fn render_document(&mut self, src: &'s str) -> Result<(), Self::Error> {
        self.render_events(Parser::new(src)).await
    }

    /// Render document as a list of events already parsed by the [`Parser`]
    async fn render_events<I>(&mut self, events: I) -> Result<(), Self::Error>
    where
        I: Iterator<Item = Event<'s>> + Send,
    {
        self.emit(Event::Start(Container::Document, Attributes::new()))
            .await?;

        for event in events {
            self.emit(event).await?;
        }

        self.emit(Event::End).await
    }
}

#[async_trait::async_trait]
impl<'s, R> AsyncRenderExt<'s> for R where R: AsyncRender<'s> + Send {}

/// An async `Render` that produces an output
#[async_trait::async_trait]
pub trait AsyncRenderOutput<'s>: AsyncRender<'s> {
    type Output;
    fn into_output(self) -> Self::Output;
}

/// Utility extension method for [`AsyncRenderOutput`] trait
#[async_trait::async_trait]
pub trait AsyncRenderOutputExt<'s>: AsyncRenderOutput<'s> {
    async fn render_into_document(
        mut self,
        input: &'s str,
    ) -> Result<Self::Output, <Self as AsyncRender<'s>>::Error>
    where
        Self: Sized,
    {
        AsyncRenderExt::<'s>::render_document(&mut self, input).await?;
        Ok(self.into_output())
    }
}

#[async_trait::async_trait]
impl<'s, R> AsyncRenderOutputExt<'s> for R where R: AsyncRenderOutput<'s> + Send {}
