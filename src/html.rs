use crate::Event;

pub fn push_html<'s, I: Iterator<Item = Event>>(s: &mut String, events: I) {
    Writer::new(events).write()
}

struct Writer<I> {
    events: I,
}

impl<I: Iterator<Item = Event>> Writer<I> {
    fn new(events: I) -> Self {
        Self { events }
    }

    fn write(self) {}
}
