/// Based on: https://blog.nlnetlabs.nl/donkeys-mules-horses/#adonkeythebinarytree

#[derive(Clone)]
pub struct DonkeyTrieNode<T: Clone> {
    meta: Option<T>,
    left: Option<Box<DonkeyTrieNode<T>>>,
    right: Option<Box<DonkeyTrieNode<T>>>,
}

impl<T: Clone> DonkeyTrieNode<T> {
    fn visit<F>(&self, depth: usize, callback: &mut F)
    where
        F: FnMut(&DonkeyTrieNode<T>, usize),
    {
        (callback)(self, depth);
        if let Some(node) = &self.left {
            node.visit(depth + 1, callback);
        }
        if let Some(node) = &self.right {
            node.visit(depth + 1, callback);
        }
    }

    pub fn meta(&self) -> Option<&T> {
        self.meta.as_ref()
    }

    pub fn set_meta(&mut self, meta: T) {
        self.meta.replace(meta);
    }

    pub fn has_meta(&self) -> bool {
        self.meta.is_some()
    }
}

impl<T: Clone + ToString> ptree::TreeItem for DonkeyTrieNode<T> {
    type Child = Self;

    fn write_self<W: std::io::Write>(
        &self,
        f: &mut W,
        style: &ptree::Style,
    ) -> std::io::Result<()> {
        let out = match (&self.left, &self.right) {
            (None, Some(_)) => "1",
            (Some(_), None) => "0",
            (Some(_), Some(_)) => "01",
            (None, None) => "",
        };
        let m = if let Some(m) = &self.meta {
            m.to_string()
        } else {
            String::new()
        };
        write!(f, "{} {}", style.paint(out), style.paint(m))
    }

    fn children(&self) -> std::borrow::Cow<[Self::Child]> {
        let mut children: Vec<DonkeyTrieNode<T>> = Vec::new();
        if let Some(left) = &self.left {
            children.push(*left.clone());
        }
        if let Some(right) = &self.right {
            children.push(*right.clone());
        }
        std::borrow::Cow::from(children)
    }
}

impl<T: Clone> DonkeyTrieNode<T> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<T: Clone> Default for DonkeyTrieNode<T> {
    fn default() -> Self {
        Self {
            meta: Default::default(),
            left: Default::default(),
            right: Default::default(),
        }
    }
}

pub struct DonkeyTrie<T: Clone + std::fmt::Display> {
    root: Box<DonkeyTrieNode<T>>,
}

impl<T: Clone + std::fmt::Display> Default for DonkeyTrie<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + std::fmt::Display> DonkeyTrie<T> {
    pub fn new() -> Self {
        Self {
            root: Box::new(DonkeyTrieNode::new()),
        }
    }

    #[time_graph::instrument(name = "donkey_trie_push")]
    pub fn push(&mut self, bits: u32, len: u8) -> &mut Box<DonkeyTrieNode<T>> {
        if len == 0 {
            return &mut self.root;
        }

        let mut node = &mut self.root;

        // zero the host bits
        let bits = bits & u32::MAX << (32 - len);

        // create mask with the leftmost bit set
        #[allow(clippy::unusual_byte_groupings)]
        let mut mask: u32 = 0b10000000_00000000_00000000_00000000;

        for _ in 0..len {
            // descend to the left if the current prefix bit is unset, else descend to the right
            let insertion_point = if (bits & mask) == 0 {
                &mut node.left
            } else {
                &mut node.right
            };

            node = insertion_point.get_or_insert_with(Default::default);

            // move the mask one bit to the right
            mask >>= 1;
        }

        // return the leaf node so that the caller can set their metadata on it
        node
    }

    pub fn print(&self) {
        ptree::print_tree(&*self.root).unwrap();
    }

    pub fn visit<F>(&self, callback: &mut F)
    where
        F: FnMut(&DonkeyTrieNode<T>, usize),
    {
        self.root.visit(0, callback)
    }

    /// This implementation of longest match using a binary tree suffers from cache read misses, as shown by callgrind:
    ///
    /// Ir           :  608,748,306 ( 9.51%)
    /// Dr           :  114,187,183 ( 9.00%)
    /// Dw           :   12,395,426 ( 1.77%)
    /// I1mr         :            5 ( 0.10%)
    /// D1mr         :    2,225,654 (16.25%)  <-- here
    /// D1mw         :            0
    /// ILmr         :            5 ( 0.11%)
    /// DLmr         :    2,225,654 (16.53%)  <-- here
    /// DLmw         :            .
    /// file:function:  ???:donkey_mule_horse::DonkeyTrie<T>::longest_match
    ///
    /// This is not surprising as each node in the tree is stored at an uncontrolled location in memory, i.e. this
    /// design doesn't attempt to ensure needed data is likely to be in the CPU cache when accessed.
    #[time_graph::instrument]
    pub fn longest_match(
        &mut self,
        prefix_addr: u32,
        prefix_len: u8,
    ) -> Option<(u32, u8, Option<&T>)> {
        if prefix_len == 0 {
            return Some((0, 0, self.root.meta.as_ref()));
        }

        let mut node = &self.root;

        // create mask with the leftmost bit set
        #[allow(clippy::unusual_byte_groupings)]
        let mut mask: u32 = 0b10000000_00000000_00000000_00000000;

        // start with an empty IPv4 addr and build it up as we go
        let mut current: u32 = 0;
        let mut match_prefix: u32 = 0;
        let mut match_len: u8 = 0;

        for i in 1..=32 {
            // descend to the left if the current prefix bit is unset, else descend to the right
            let next_node = if (prefix_addr & mask) == 0 {
                if node.left.is_some() {
                    current <<= 1;
                }
                &node.left
            } else {
                if node.right.is_some() {
                    current <<= 1;
                    current |= 1;
                }
                &node.right
            };

            if next_node.is_none() {
                break;
            } else {
                node = next_node.as_ref().unwrap();
                if node.meta.is_some() {
                    match_prefix = current;
                    match_len = i;
                }
            }

            // move the mask one bit to the right
            mask >>= 1;
        }

        match_prefix <<= 32 - match_len;
        Some((match_prefix, match_len, node.meta.as_ref()))
    }
}
