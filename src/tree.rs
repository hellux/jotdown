use crate::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventKind<C, A> {
    Enter(C),
    Inline,
    Exit(C),
    Atom(A),
}

#[derive(Debug)]
pub struct Node<'a, C, A> {
    pub index: NodeIndex,
    pub elem: Element<'a, C, A>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Element<'a, C, A> {
    Container(&'a mut C),
    Atom(&'a mut A),
    Inline,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event<C, A> {
    pub kind: EventKind<C, A>,
    pub span: Span,
}

#[derive(Clone)]
pub struct Tree<C, A> {
    nodes: std::rc::Rc<[InternalNode<C, A>]>,
    branch: Vec<NodeIndex>,
    head: Option<NodeIndex>,
}

impl<C: Clone, A: Clone> Tree<C, A> {
    /// Count number of direct children nodes.
    pub fn count_children(&self) -> usize {
        let mut head = self.head;
        let mut count = 0;
        while let Some(h) = head {
            let n = &self.nodes[h.index()];
            head = n.next;
            count += 1;
        }
        count
    }

    /// Retrieve all inlines until the end of the current container. Panics if any upcoming node is
    /// not an inline node.
    pub fn take_inlines(&mut self) -> impl Iterator<Item = Span> + '_ {
        let mut head = self.head.take();
        std::iter::from_fn(move || {
            head.take().map(|h| {
                let n = &self.nodes[h.index()];
                debug_assert!(matches!(n.kind, NodeKind::Inline));
                head = n.next;
                n.span
            })
        })
    }

    pub fn branch_is_empty(&self) -> bool {
        matches!(self.head, None)
    }
}

impl<C: Clone, A: Clone> Iterator for Tree<C, A> {
    type Item = Event<C, A>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(head) = self.head {
            let n = &self.nodes[head.index()];
            let kind = match &n.kind {
                NodeKind::Root => unreachable!(),
                NodeKind::Container(c, child) => {
                    self.branch.push(head);
                    self.head = *child;
                    EventKind::Enter(c.clone())
                }
                NodeKind::Atom(a) => {
                    self.head = n.next;
                    EventKind::Atom(a.clone())
                }
                NodeKind::Inline => {
                    self.head = n.next;
                    EventKind::Inline
                }
            };
            Some(Event { kind, span: n.span })
        } else if let Some(block_ni) = self.branch.pop() {
            let InternalNode { next, kind, span } = &self.nodes[block_ni.index()];
            let kind = EventKind::Exit(kind.container().unwrap().clone());
            self.head = *next;
            Some(Event { kind, span: *span })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIndex(std::num::NonZeroUsize);

impl NodeIndex {
    fn new(i: usize) -> Self {
        debug_assert_ne!(i, usize::MAX);
        Self((i + 1).try_into().unwrap())
    }

    fn root() -> Self {
        Self::new(0)
    }

    fn index(self) -> usize {
        usize::from(self.0) - 1
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NodeKind<C, A> {
    Root,
    Container(C, Option<NodeIndex>),
    Atom(A),
    Inline,
}

#[derive(Debug, Clone)]
struct InternalNode<C, A> {
    span: Span,
    kind: NodeKind<C, A>,
    next: Option<NodeIndex>,
}

#[derive(Clone)]
pub struct Builder<C, A> {
    nodes: Vec<InternalNode<C, A>>,
    branch: Vec<NodeIndex>,
    head: Option<NodeIndex>,
    depth: usize,
}

impl<C, A> NodeKind<C, A> {
    fn child(&self) -> Option<NodeIndex> {
        if let NodeKind::Container(_, child) = self {
            *child
        } else {
            None
        }
    }

    fn child_mut(&mut self) -> &mut Option<NodeIndex> {
        if let NodeKind::Container(_, child) = self {
            child
        } else {
            panic!()
        }
    }

    fn container(&self) -> Option<&C> {
        if let NodeKind::Container(c, _) = self {
            Some(c)
        } else {
            None
        }
    }
}

impl<'a, C, A> From<&'a mut NodeKind<C, A>> for Element<'a, C, A> {
    fn from(kind: &'a mut NodeKind<C, A>) -> Self {
        match kind {
            NodeKind::Root => unreachable!(),
            NodeKind::Container(c, ..) => Element::Container(c),
            NodeKind::Atom(a) => Element::Atom(a),
            NodeKind::Inline => Element::Inline,
        }
    }
}

impl<C, A> Builder<C, A> {
    pub(super) fn new() -> Self {
        Builder {
            nodes: vec![InternalNode {
                span: Span::default(),
                kind: NodeKind::Root,
                next: None,
            }],
            branch: vec![],
            head: Some(NodeIndex::root()),
            depth: 0,
        }
    }

    pub(super) fn atom(&mut self, a: A, span: Span) {
        self.add_node(InternalNode {
            span,
            kind: NodeKind::Atom(a),
            next: None,
        });
    }

    pub(super) fn inline(&mut self, span: Span) {
        self.add_node(InternalNode {
            span,
            kind: NodeKind::Inline,
            next: None,
        });
    }

    pub(super) fn enter(&mut self, c: C, span: Span) -> NodeIndex {
        self.depth += 1;
        self.add_node(InternalNode {
            span,
            kind: NodeKind::Container(c, None),
            next: None,
        })
    }

    pub(super) fn exit(&mut self) {
        self.depth -= 1;
        if let Some(head) = self.head.take() {
            if matches!(self.nodes[head.index()].kind, NodeKind::Container(..)) {
                self.branch.push(head);
            }
        } else {
            let last = self.branch.pop();
            debug_assert_ne!(last, None);
        }
    }

    /// Exit and discard all the contents of the current container.
    pub(super) fn exit_discard(&mut self) {
        self.exit();
        let exited = self.branch.pop().unwrap();
        self.nodes.drain(exited.index()..);
        let (prev, has_parent) = self.replace(exited, None);
        if has_parent {
            self.head = Some(prev);
        } else {
            self.branch.push(prev);
        }
    }

    /// Swap the node and its children with either its parent or the node before.
    pub fn swap_prev(&mut self, node: NodeIndex) {
        let next = self.nodes[node.index()].next;
        if let Some(n) = next {
            self.replace(n, None);
        }
        let (prev, _) = self.replace(node, next);
        self.replace(prev, Some(node));
        self.nodes[node.index()].next = Some(prev);
    }

    /// Remove the specified node and its children.
    pub fn remove(&mut self, node: NodeIndex) {
        let next = self.nodes[node.index()].next;
        self.replace(node, next);
    }

    pub(super) fn depth(&self) -> usize {
        self.depth
    }

    pub(super) fn elem(&mut self, ni: NodeIndex) -> Element<C, A> {
        match &mut self.nodes[ni.index()].kind {
            NodeKind::Root => unreachable!(),
            NodeKind::Container(c, ..) => Element::Container(c),
            NodeKind::Atom(a) => Element::Atom(a),
            NodeKind::Inline => Element::Inline,
        }
    }

    /// Retrieve all children nodes for the specified node, in the order that they were added.
    pub(super) fn children(&mut self, node: NodeIndex) -> impl Iterator<Item = Node<C, A>> {
        // XXX assumes no modifications
        let n = &self.nodes[node.index()];
        let range = if let Some(start) = n.kind.child() {
            start.index()..n.next.map_or(self.nodes.len(), NodeIndex::index)
        } else {
            0..0
        };
        range
            .clone()
            .map(NodeIndex::new)
            .zip(self.nodes[range].iter_mut())
            .map(|(index, n)| Node {
                index,
                elem: Element::from(&mut n.kind),
                span: n.span,
            })
    }

    pub(super) fn finish(self) -> Tree<C, A> {
        debug_assert_eq!(self.depth, 0);
        let head = self.nodes[NodeIndex::root().index()].next;
        Tree {
            nodes: self.nodes.into_boxed_slice().into(),
            branch: Vec::new(),
            head,
        }
    }

    fn add_node(&mut self, node: InternalNode<C, A>) -> NodeIndex {
        let ni = NodeIndex::new(self.nodes.len());
        self.nodes.push(node);
        if let Some(head_ni) = &mut self.head {
            let mut head = &mut self.nodes[head_ni.index()];
            match &mut head.kind {
                NodeKind::Root | NodeKind::Inline | NodeKind::Atom(_) => {
                    // set next pointer of previous node
                    debug_assert_eq!(head.next, None);
                    head.next = Some(ni);
                }
                NodeKind::Container(_, child) => {
                    self.branch.push(*head_ni);
                    // set child pointer of current container
                    debug_assert_eq!(*child, None);
                    *child = Some(ni);
                }
            }
        } else if let Some(block) = self.branch.pop() {
            let mut block = &mut self.nodes[block.index()];
            debug_assert!(matches!(block.kind, NodeKind::Container(..)));
            block.next = Some(ni);
        } else {
            panic!()
        }
        self.head = Some(ni);
        ni
    }

    /// Remove the link from the node that points to the specified node. Optionally replace the
    /// node with another node. Return the pointer node and whether it is a container or not.
    fn replace(&mut self, node: NodeIndex, next: Option<NodeIndex>) -> (NodeIndex, bool) {
        for (i, n) in self.nodes.iter_mut().enumerate().rev() {
            let ni = NodeIndex::new(i);
            if n.next == Some(node) {
                n.next = next;
                return (ni, false);
            } else if n.kind.child() == Some(node) {
                *n.kind.child_mut() = next;
                return (ni, true);
            }
        }
        panic!("node is never linked to")
    }
}

impl<C: std::fmt::Debug + Clone, A: std::fmt::Debug + Clone> std::fmt::Debug for Builder<C, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.clone().finish().fmt(f)
    }
}

impl<C: std::fmt::Debug + Clone, A: std::fmt::Debug + Clone> std::fmt::Debug for Tree<C, A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const INDENT: &str = "  ";
        let mut level = 0;
        writeln!(f)?;
        for e in self.clone() {
            let indent = INDENT.repeat(level);
            match e.kind {
                EventKind::Enter(c) => {
                    write!(f, "{}{:?}", indent, c)?;
                    level += 1;
                }
                EventKind::Inline => write!(f, "{}Inline", indent)?,
                EventKind::Exit(..) => {
                    level -= 1;
                    continue;
                }
                EventKind::Atom(a) => write!(f, "{}{:?}", indent, a)?,
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
    fn fmt() {
        let mut tree = super::Builder::new();
        tree.enter(1, Span::new(0, 1));
        tree.atom(11, Span::new(0, 1));
        tree.atom(12, Span::new(0, 1));
        tree.exit();
        tree.enter(2, Span::new(1, 5));
        tree.enter(21, Span::new(2, 5));
        tree.enter(211, Span::new(3, 4));
        tree.atom(2111, Span::new(3, 4));
        tree.exit();
        tree.exit();
        tree.enter(22, Span::new(4, 5));
        tree.atom(221, Span::new(4, 5));
        tree.exit();
        tree.exit();
        tree.enter(3, Span::new(5, 6));
        tree.atom(31, Span::new(5, 6));
        tree.exit();
        assert_eq!(
            format!("{:?}", tree.finish()),
            concat!(
                "\n",
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
