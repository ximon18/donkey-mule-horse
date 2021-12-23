/// IPv4 only variable stride tree bitmap in-memory prefix store.
use std::net::{IpAddr, Ipv4Addr};

use routecore::addr::Prefix;

use crate::treebitmap::{error::Error, variablenode::VariableSizeStrideNode};

#[derive(Debug)]
pub struct TreeBitMap {
    strides: Vec<u8>,
    pub nodes: Vec<VariableSizeStrideNode>,
    pub prefixes: Vec<Prefix>, // (prefix ipv4, prefix len)
}

impl TreeBitMap {
    pub fn new(strides: Vec<u8>) -> Result<Self, Error> {
        // Check that the given stride sizes are supported.
        strides.iter().try_for_each(|x| {
            let _ = VariableSizeStrideNode::new(*x)?;
            Ok(())
        })?;

        // Check that the given total stride size is supported.
        if strides.iter().sum::<u8>() != 32 {
            return Err(Error::UnsupportedTotalStrideSize);
        }

        let root_node = VariableSizeStrideNode::new(strides[0].into())?;

        Ok(Self {
            strides,
            nodes: vec![root_node],
            prefixes: Vec::new(),
        })
    }

    pub fn statistics(&self) -> (usize, usize) {
        (self.nodes.len(), self.prefixes.len())
    }

    #[time_graph::instrument(name = "donkey_tree_bitmap_push")]
    pub fn push(&mut self, bits: u32, len: u8) {
        let prefix = Prefix::new_v4(Ipv4Addr::from(bits), len).unwrap();
        self.prefixes.push(prefix);
        let prefix_idx = self.prefixes.len() - 1;

        // Walk the tree inserting the bits of the prefix sequentially into the tree in pieces sized according to the
        // stride length supported by each level of the tree.
        let mut node_idx = 0;
        let len = usize::from(len);
        let mut depth = 0;

        // Copy the bits so we can shift them left as we process them.
        let mut bits = bits;

        // Prefixes of length zero always match the default route 0/0 (i.e. 0.0.0.0/0 for IPv4 and ::/0 for IPv6 - we
        // only currently deal with IPv4, not IPv6). Hence we don't need to store anything in the tree for prefixes of
        // length zero and instead only process those with a length of at least one.
        if len > 0 {
            let mut i: usize = 0;
            while i < len {
                let stride_size = self.nodes[node_idx].stride_size();
                let remaining_pfx_len = len - i;
                let pfx_len_in_stride = stride_size.min(remaining_pfx_len);

                let (pfxbitarr_bit_idx, ptrbitarr_bit_idx) =
                self.nodes[node_idx].get_matching_bitarr_indices(bits, pfx_len_in_stride);

                if remaining_pfx_len <= stride_size {
                    // Set the pfxbitarr bit if not set. If we set it, insert the prefix node idx into pfxvec.
                    self.nodes[node_idx].add_prefix(pfxbitarr_bit_idx, prefix_idx);
                } else {
                    // The prefix cannot be stored at this depth of the tree, move down.
                    // Does a child node for the remaining prefix bits of this stride exist?
                    depth += 1;
                    node_idx = if let Some(node_idx) =
                        self.nodes[node_idx].get_child_node_idx(ptrbitarr_bit_idx)
                    {
                        node_idx
                    } else {
                        // Safety: We checked in `new()` that all the stride sizes can be constructed so it's safe to
                        // `unwrap()` here.
                        let new_node =
                            VariableSizeStrideNode::new(self.strides[depth].into()).unwrap();
                        self.nodes.push(new_node);
                        let new_node_idx = self.nodes.len() - 1;
                        self.nodes[node_idx].add_child_node(ptrbitarr_bit_idx, new_node_idx);
                        new_node_idx
                    };
                }

                i += stride_size;
                bits <<= stride_size;
            }
        }
    }

    #[time_graph::instrument(name = "donkey_tree_bitmap_longest_match")]
    pub fn longest_match(&mut self, prefix_addr: u32, prefix_len: u8) -> Option<(u32, u8)> {
        // Walk the tree upto prefix_len bits of prefix deep looking for the longest exact match
        let mut node = &self.nodes[0];
        let mut bits = prefix_addr;
        let mut i = 1;
        let mut best_prefix: Option<&Prefix> = None;

        while i <= prefix_len {
            let last_i = i;
            let stride_size = node.stride_size() as u8;
            let pfx_len_in_stride = stride_size.min(prefix_len - i + 1);
            for sub_len in (1..=pfx_len_in_stride).rev() {
                let (pfxbitarr_idx, ptrbitarr_idx) =
                    node.get_matching_bitarr_indices(bits, sub_len as usize);

                // Is the pfxbitarr set indicating that this node contains the prefix and thus our search is
                // finished?
                if let Some(prefix_idx) = node.get_prefix_node_idx(pfxbitarr_idx) {
                    let prefix = &self.prefixes[prefix_idx];
                    if let Some(current_best_prefix) = best_prefix {
                        // if more specific than the last best match but still less or as specific as the search prefix
                        if prefix.len() > current_best_prefix.len() && prefix.len() <= prefix_len {
                            best_prefix = Some(prefix);
                        }
                    } else {
                        best_prefix = Some(prefix);
                    }
                }

                // Is the ptrbitarr bit set? If so we must ascend the tree to pursue this prefix
                if let Some(node_idx) = node.get_child_node_idx(ptrbitarr_idx) {
                    node = &self.nodes[node_idx];
                    i += sub_len;
                    bits <<= sub_len;
                    break;
                }
            }

            if last_i == i {
                break;
            }
        }

        if let Some(prefix) = best_prefix {
            if let IpAddr::V4(addr) = prefix.addr() {
                return Some((u32::from(addr), prefix.len()));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::{TreeBitMap, VariableSizeStrideNode};

    #[test]
    fn compare_with_blog_article_data() {
        // The first two strides must be size 3 to match the setup used in the blog article, the rest don't matter as
        // we should only end up using the first two, but whatever the other stride sizes are the total must be 32.
        let mut tree = TreeBitMap::new(vec![3, 3, 8, 8, 8, 2]).unwrap();
        tree.push(0b01u32 << 30, 2);
        tree.push(0b10u32 << 30, 2);
        tree.push(0b110u32 << 29, 3);
        tree.push(0b000u32 << 29, 3);
        tree.push(0b11001u32 << 27, 5);
        tree.push(0b111u32 << 29, 3);

        println!("{:?}", tree);

        // Expect the data structure to match that shown in the tree bitmap diagram in the "Pointer free" section of
        // Jaspers' blog article
        assert_eq!(tree.nodes.len(), 2);
        assert_eq!(tree.prefixes.len(), 6);

        assert_eq!(tree.nodes[0].stride_size(), 3);
        if let VariableSizeStrideNode::Size3(node) = &tree.nodes[0] {
            assert_eq!(node.ptrbitarr.len(), 1); // 8-bit
            assert_eq!(node.ptrbitarr[0], 0b00000010u8);
            assert_eq!(node.ptrvec.len(), 1);
            assert_eq!(node.ptrvec, [1]);

            assert_eq!(node.pfxbitarr.len(), 2); // 16-bit
            assert_eq!(node.pfxbitarr[0], 0b00001101u8);
            assert_eq!(node.pfxbitarr[1], 0b00000110u8);
            assert_eq!(node.pfxvec.len(), 5);
            assert_eq!(node.pfxvec, [0, 1, 3, 2, 5]);
        }

        assert_eq!(tree.nodes[1].stride_size(), 3);
        if let VariableSizeStrideNode::Size3(node) = &tree.nodes[1] {
            assert_eq!(node.ptrbitarr.len(), 1); // 8-bit
            assert_eq!(node.ptrbitarr[0], 0b00000000u8);
            assert_eq!(node.ptrvec.len(), 0);

            assert_eq!(node.pfxbitarr.len(), 2); // 16-bit
            assert_eq!(node.pfxbitarr[0], 0b00001000u8);
            assert_eq!(node.pfxbitarr[1], 0b00000000u8);
            assert_eq!(node.pfxvec.len(), 1);
            assert_eq!(node.pfxvec, [4]);
        }
    }
}
