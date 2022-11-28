use crate::Event;

pub fn push_html<'s, I: Iterator<Item = Event<'s>>>(s: &mut String, events: I) {
    Writer::new(events).write()
}

struct Writer<I> {
    events: I,
}

impl<'s, I: Iterator<Item = Event<'s>>> Writer<I> {
    fn new(events: I) -> Self {
        Self { events }
    }

    fn write(self) {}
}
