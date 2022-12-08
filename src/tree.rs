use crate::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventKind<C, E> {
    Enter(C),
    Element(E),
    Exit(C),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event<C, A> {
    pub kind: EventKind<C, A>,
    pub span: Span,
}

pub struct Object<C, E> {
    kind: ObjectKind<C, E>,
    span: Span,
}

pub enum ObjectKind<C, E> {
    Container(C),
    Element(E),
}

#[derive(Debug, Clone)]
pub struct Tree<C, E> {
    nodes: Vec<Node<C, E>>,
    branch: Vec<NodeIndex>,
    head: Option<NodeIndex>,
}

impl<C: Copy, E: Copy> Tree<C, E> {
    fn new(nodes: Vec<Node<C, E>>) -> Self {
        let head = nodes[NodeIndex::root().index()].next;
        Self {
            nodes,
            branch: Vec::new(),
            head,
        }
    }

    pub fn neighbors(&self) -> impl Iterator<Item = Object<C, E>> + '_ {
        let mut head = self.head;
        std::iter::from_fn(move || {
            head.take().map(|h| {
                let n = &self.nodes[h.index()];
                let kind = match &n.kind {
                    NodeKind::Root => unreachable!(),
                    NodeKind::Container(c, _) => ObjectKind::Container(*c),
                    NodeKind::Element(e) => ObjectKind::Element(*e),
                };
                let span = n.span;
                head = n.next;
                Object { kind, span }
            })
        })
    }
}

impl<C: Copy, E: Copy> Iterator for Tree<C, E> {
    type Item = Event<C, E>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(head) = self.head {
            let n = &self.nodes[head.index()];
            let kind = match &n.kind {
                NodeKind::Root => unreachable!(),
                NodeKind::Container(c, child) => {
                    self.branch.push(head);
                    self.head = *child;
                    EventKind::Enter(*c)
                }
                NodeKind::Element(e) => {
                    self.head = n.next;
                    EventKind::Element(*e)
                }
            };
            Some(Event { kind, span: n.span })
        } else if let Some(block_ni) = self.branch.pop() {
            let Node { next, kind, span } = &self.nodes[block_ni.index()];
            let cont = if let NodeKind::Container(c, _) = kind {
                c
            } else {
                panic!();
            };
            self.head = *next;
            Some(Event {
                kind: EventKind::Exit(*cont),
                span: *span,
            })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NodeIndex(std::num::NonZeroUsize);

impl NodeIndex {
    fn new(i: usize) -> Self {
        assert_ne!(i, usize::MAX);
        Self((i + 1).try_into().unwrap())
    }

    fn root() -> Self {
        Self::new(0)
    }

    fn index(self) -> usize {
        usize::from(self.0) - 1
    }
}

#[derive(Debug, Clone)]
enum NodeKind<C, E> {
    Root,
    Container(C, Option<NodeIndex>),
    Element(E),
}

#[derive(Debug, Clone)]
struct Node<C, E> {
    span: Span,
    kind: NodeKind<C, E>,
    next: Option<NodeIndex>,
}

#[derive(Debug, Clone)]
pub struct Builder<C, E> {
    nodes: Vec<Node<C, E>>,
    branch: Vec<NodeIndex>,
    head: Option<NodeIndex>,
}

impl<C: Copy, E: Copy> Builder<C, E> {
    pub(super) fn new() -> Self {
        Builder {
            nodes: vec![Node {
                span: Span::default(),
                kind: NodeKind::Root,
                next: None,
            }],
            branch: vec![],
            head: Some(NodeIndex::root()),
        }
    }

    pub(super) fn elem(&mut self, e: E, span: Span) {
        self.add_node(Node {
            span,
            kind: NodeKind::Element(e),
            next: None,
        });
    }

    pub(super) fn enter(&mut self, c: C, span: Span) {
        self.add_node(Node {
            span,
            kind: NodeKind::Container(c, None),
            next: None,
        });
    }

    pub(super) fn exit(&mut self) {
        if self.head.is_some() {
            self.head = None;
        } else {
            let last = self.branch.pop();
            assert_ne!(last, None);
        }
    }

    pub(super) fn finish(self) -> Tree<C, E> {
        Tree::new(self.nodes)
    }

    fn add_node(&mut self, node: Node<C, E>) {
        let ni = NodeIndex::new(self.nodes.len());
        self.nodes.push(node);
        if let Some(head_ni) = &mut self.head {
            let mut head = &mut self.nodes[head_ni.index()];
            match &mut head.kind {
                NodeKind::Root | NodeKind::Element(_) => {
                    // update next pointer of previous node
                    assert_eq!(head.next, None);
                    head.next = Some(ni);
                }
                NodeKind::Container(_, child) => {
                    self.branch.push(*head_ni);
                    // update child pointer of current container
                    assert_eq!(*child, None);
                    *child = Some(ni);
                }
            }
        } else if let Some(block) = self.branch.pop() {
            let mut block = &mut self.nodes[block.index()];
            assert!(matches!(block.kind, NodeKind::Container(..)));
            block.next = Some(ni);
        } else {
            panic!()
        }
        self.head = Some(ni);
    }
}

impl<C: Copy + std::fmt::Display, E: Copy + std::fmt::Display> std::fmt::Display for Builder<C, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.clone().finish().fmt(f)
    }
}

impl<C: Copy + std::fmt::Display, E: Copy + std::fmt::Display> std::fmt::Display for Tree<C, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const INDENT: &str = "  ";
        let mut level = 0;
        for e in self.clone() {
            let indent = INDENT.repeat(level);
            match e.kind {
                EventKind::Enter(container) => {
                    write!(f, "{}{}", indent, container)?;
                    level += 1;
                }
                EventKind::Exit(_) => {
                    level -= 1;
                    continue;
                }
                EventKind::Element(element) => {
                    write!(f, "{}{}", indent, element)?;
                }
            }
            writeln!(f, " ({}:{})", e.span.start(), e.span.end())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::Span;

    #[test]
    fn fmt_linear() {
        let mut tree: super::Builder<u8, u8> = super::Builder::new();
        tree.elem(1, Span::new(0, 1));
        tree.elem(2, Span::new(1, 2));
        tree.elem(3, Span::new(3, 4));
        assert_eq!(
            tree.to_string(),
            concat!(
                "1 (0:1)\n",
                "2 (1:2)\n",
                "3 (3:4)\n", //
            )
        );
    }

    #[test]
    fn fmt_container() {
        let mut tree: super::Builder<u8, u16> = super::Builder::new();
        tree.enter(1, Span::new(0, 1));
        tree.elem(11, Span::new(0, 1));
        tree.elem(12, Span::new(0, 1));
        tree.exit();
        tree.enter(2, Span::new(1, 5));
        tree.enter(21, Span::new(2, 5));
        tree.enter(211, Span::new(3, 4));
        tree.elem(2111, Span::new(3, 4));
        tree.exit();
        tree.exit();
        tree.enter(22, Span::new(4, 5));
        tree.elem(221, Span::new(4, 5));
        tree.exit();
        tree.exit();
        tree.enter(3, Span::new(5, 6));
        tree.elem(31, Span::new(5, 6));
        tree.exit();
        assert_eq!(
            tree.to_string(),
            concat!(
                "1 (0:1)\n",
                "  11 (0:1)\n",
                "  12 (0:1)\n",
                "2 (1:5)\n",
                "  21 (2:5)\n",
                "    211 (3:4)\n",
                "      2111 (3:4)\n",
                "  22 (4:5)\n",
                "    221 (4:5)\n",
                "3 (5:6)\n",
                "  31 (5:6)\n",
            )
        );
    }
}
