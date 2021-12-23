/// Based on: https://blog.nlnetlabs.nl/donkeys-mules-horses/#pointerfree
/// An implementaton of a variable sized stride tree bitmap using nightly Rust support for const generics to represent
/// stride size dependent pfx and ptr bit arrays as fixed length byte arrays whose length is fixed at compile time for
/// the stride size being represented. It is likely more efficient to use different sized types instead of variable
/// numbers of bytes, e.g. use u64 instead of [u8; 8], so this is just an experimental approach, it is not expected to
/// be fast enough for production use.
use std::net::Ipv4Addr;

use routecore::addr::Prefix;

/// Based on: https://blog.nlnetlabs.nl/donkeys-mules-horses/#pointerfree
pub const fn max(a: usize, b: usize) -> usize {
    [a, b][(a < b) as usize]
}

#[derive(Debug)]
pub enum VariableSizeStrideNode {
    Size1(StrideNode<1>),
    Size2(StrideNode<2>),
    Size3(StrideNode<3>),
    Size4(StrideNode<4>),
    Size5(StrideNode<5>),
    Size6(StrideNode<6>),
    Size7(StrideNode<7>),
    Size8(StrideNode<8>),
}

macro_rules! with_node {
    ($self:ident => $member_fn:ident ( $( $arg:ident ),* )) => {
        match $self {
            VariableSizeStrideNode::Size1(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size2(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size3(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size4(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size5(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size6(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size7(sized_node) => sized_node.$member_fn($($arg),*),
            VariableSizeStrideNode::Size8(sized_node) => sized_node.$member_fn($($arg),*),
        }
    };
}

// Generate code for calculating (pfxbitarr_bit_idx, ptrbitarr_bit_idx) results
// equivalent to match blocks of the following form:
//
//  stride size 1:
//     match bits & 0b10000000_00000000_00000000_00000000 {
//         0b00000000_00000000_00000000_00000000 => (1, 0),
//         0b10000000_00000000_00000000_00000000 => (2, 1),
//         _ => unreachable!(),
//     },
//
//  stride size 2:
//     match bits & 0b11000000_00000000_00000000_00000000 {
//         0b00000000_00000000_00000000_00000000 => (3, 0),
//         0b01000000_00000000_00000000_00000000 => (4, 1),
//         0b10000000_00000000_00000000_00000000 => (5, 2),
//         0b11000000_00000000_00000000_00000000 => (6, 3),
//         _ => unreachable!(),
//     }
//
// etc.
macro_rules! bitarr_indices_from_bits {
    ($stride_size:literal, $bits:ident) => {
        {
            const MASK: u32 = u32::MAX << (32 - $stride_size);
            const MAX: u32 = MASK >> (32 - $stride_size);
            let ptrbitarr_bit_idx = ($bits & MASK) >> (32 - $stride_size);
            let pfxbitarr_bit_idx = MAX + ptrbitarr_bit_idx;
            (pfxbitarr_bit_idx as usize, ptrbitarr_bit_idx as usize)
        }
    }
}

impl VariableSizeStrideNode {
    pub fn new(stride: usize) -> Self {
        match stride {
            1 => VariableSizeStrideNode::Size1(StrideNode::<1>::new()),
            2 => VariableSizeStrideNode::Size2(StrideNode::<2>::new()),
            3 => VariableSizeStrideNode::Size3(StrideNode::<3>::new()),
            4 => VariableSizeStrideNode::Size4(StrideNode::<4>::new()),
            5 => VariableSizeStrideNode::Size5(StrideNode::<5>::new()),
            6 => VariableSizeStrideNode::Size6(StrideNode::<6>::new()),
            7 => VariableSizeStrideNode::Size7(StrideNode::<7>::new()),
            8 => VariableSizeStrideNode::Size8(StrideNode::<8>::new()),
            _ => unimplemented!(),
        }
    }

    pub fn stride_size(&self) -> usize {
        with_node!(self => stride_size())
    }

    pub fn add_prefix(&mut self, bit_idx: usize, prefix_idx: usize) {
        with_node!(self => add_prefix(bit_idx, prefix_idx))
    }

    pub fn add_child_node(&mut self, bit_idx: usize, node_idx: usize) {
        with_node!(self => add_child_node(bit_idx, node_idx))
    }

    pub fn get_child_node_idx(&mut self, bit_idx: usize) -> Option<usize> {
        with_node!(self => get_child_node_idx(bit_idx))
    }

    pub fn get_matching_bitarr_indices(&self, bits: u32, len: usize) -> (usize, usize) {
        // Do the remaining prefix bits fit in this node and if so which pfxbitarr bucket needs to be ticked
        // to indicate that that prefix exists in this node?
        //
        // In a 3-bit wide stride the pfxbitarr is 16-bits long and the bits have meaning as follows:
        //
        //   stride 3: fits in 1x16 bits and 1x8 bits
        //   ------------------------------------------------------------------------------------------------------
        //   bit idx:         0    1    2    3    4    5    6    7    8    9   10   11   12   13   14   15
        //   ------------------------------------------------------------------------------------------------------
        //   prefix bits      *    0    1   00   01   10   11  000  001  010  011  100  101  110  111    !
        //   pfxbitarr:       .    .    .    .    .    .    .    .    .    .    .    .    .    .    .    !  15 bits
        //   ptrbitarr:                                          .    .    .    .    .    .    .    .        8 bits
        //   ------------------------------------------------------------------------------------------------------
        //   bucket label:         a    a    b    b    b    b    c    c    c    c    c    c    c    c
        //
        // If the remaining prefix length is 1 we should check/set the one of the fields marked 'a'.
        // If the remaining prefix length is 2 we should check/set the one of the fields marked 'b'.
        // If the remaining prefix length is 3 we should check/set the one of the fields marked 'c'.
        // If the remaining prefix length is >3 the prefix will not be set in this node, instead we should look
        // for the child node (if any) that handles the next part of this prefix.
        //
        // The logic is similar for other stride sizes.
        let stride_size = self.stride_size();

        match len {
            1 if stride_size >= 1 => bitarr_indices_from_bits!(1, bits),
            2 if stride_size >= 2 => bitarr_indices_from_bits!(2, bits),
            3 if stride_size >= 3 => bitarr_indices_from_bits!(3, bits),
            4 if stride_size >= 4 => bitarr_indices_from_bits!(4, bits),
            5 if stride_size >= 5 => bitarr_indices_from_bits!(5, bits),
            6 if stride_size >= 6 => bitarr_indices_from_bits!(6, bits),
            7 if stride_size >= 7 => bitarr_indices_from_bits!(7, bits),
            8 if stride_size >= 8 => bitarr_indices_from_bits!(8, bits),
            _ => unreachable!()
        }
    }
}

#[cfg(test)]
mod tests2 {
    use super::*;

    #[test]
    fn indices_check() {
        let sn = VariableSizeStrideNode::new(1);
        assert_eq!(sn.get_matching_bitarr_indices(0b00000000_00000000_00000000_00000000u32, 1), (1, 0));
        assert_eq!(sn.get_matching_bitarr_indices(0b10000000_00000000_00000000_00000000u32, 1), (2, 1));

        let sn = VariableSizeStrideNode::new(2);
        assert_eq!(sn.get_matching_bitarr_indices(0b00000000_00000000_00000000_00000000u32, 2), (3, 0));
        assert_eq!(sn.get_matching_bitarr_indices(0b01000000_00000000_00000000_00000000u32, 2), (4, 1));
        assert_eq!(sn.get_matching_bitarr_indices(0b10000000_00000000_00000000_00000000u32, 2), (5, 2));
        assert_eq!(sn.get_matching_bitarr_indices(0b11000000_00000000_00000000_00000000u32, 2), (6, 3));

        // For stride size 3 the (a, b) values we expect can be compared to the diagram above.
        // (a, b) denotes (pfxbitarr bit index, ptrbitarr bit index).
        // E.g. (10, 3) refers to bit 10 (counting from zero from the left) in pfxbitarr which represents bucket 011,
        // which is correct for the test input value of 0b011....u32.
        // Likewise the 3 refers to bit 3 (counting from zero from the left) in ptrbitarr which also represents bucket
        // 011 but this time in the _ptr_ bit array rather than the _pfx_ bit array.
        let sn = VariableSizeStrideNode::new(3);
        assert_eq!(sn.get_matching_bitarr_indices(0b00000000_00000000_00000000_00000000u32, 3), (7, 0));
        assert_eq!(sn.get_matching_bitarr_indices(0b00100000_00000000_00000000_00000000u32, 3), (8, 1));
        assert_eq!(sn.get_matching_bitarr_indices(0b01000000_00000000_00000000_00000000u32, 3), (9, 2));
        assert_eq!(sn.get_matching_bitarr_indices(0b01100000_00000000_00000000_00000000u32, 3), (10, 3));
        assert_eq!(sn.get_matching_bitarr_indices(0b10000000_00000000_00000000_00000000u32, 3), (11, 4));
        assert_eq!(sn.get_matching_bitarr_indices(0b10100000_00000000_00000000_00000000u32, 3), (12, 5));
        assert_eq!(sn.get_matching_bitarr_indices(0b11000000_00000000_00000000_00000000u32, 3), (13, 6));
        assert_eq!(sn.get_matching_bitarr_indices(0b11100000_00000000_00000000_00000000u32, 3), (14, 7));
    }
}

/// A stride represents a sequence of one or more prefix bits where 1 <= T <= 8 is the number of bits.
///
///   . denotes used bits
///   ! denotes unused bits
///   
///   stride 1: fits in 2x8 bits (could even fit in 1x8 bits)
///                    *    0    1    !    !    !    !    !
///   pfxbitarr:       .    .    .    !    !    !    !    !  3 bits
///   ptrbitarr:  !    !    !    !    !    !    .    .       2 bits
///   
///   stride 2: fits in 2x8 bits
///                    *    0    1   00   01   10   11    !
///   pfxbitarr:       .    .    .    .    .    .    .    !  7 bits
///   ptrbitarr:  !    !    !    !    .    .    .    .       4 bits
///   
///   stride 3: fits in 1x16 bits and 1x8 bits
///                    *    0    1   00   01   10   11  000  001  010  011  100  101  110  111    !
///   pfxbitarr:       .    .    .    .    .    .    .    .    .    .    .    .    .    .    .    !  15 bits
///   ptrbitarr:                                          .    .    .    .    .    .    .    .        8 bits
///   
///   stride 4: fits in 1x32 bits and 1x16 bits
///                    *    0    1   00   01   10   11  000  001  010  011  100  101  110  111  0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111    !
///   pfxbitarr:       .    .    .    .    .    .    .    .    .    .    .    .    .    .    .     .    .    .    .    .    .    .    .    .    .    .    .    .    .    .    .    !  31 bits
///   ptrbitarr:                                                                                   .    .    .    .    .    .    .    .    .    .    .    .    .    .    .    .       16 bits
///
/// So the number of bytes needed for ptrbitarr is 2<<(T-1)>>3 and for pfxbitarr is 2<<T>>3
/// A zero size is rounded up to 1 byte which is shown in (parentheses).
///
///   T   ptrbitarr      pfxbitarr
///   --------------------------------
///   1   2<<0>>3=0 (1)  2<<1>>3=0 (1)
///   2   2<<1>>3=0 (1)  2<<2>>3=1
///   3   2<<2>>3=1      2<<3>>3=2
///   4   2<<3>>3=2      2<<4>>3=4
///   5   2<<4>>3=4      2<<5>>3=8
///   6   2<<5>>3=8      2<<6>>3=16
///   7   2<<6>>3=16     2<<7>>3=32
///   8   2<<7>>3=32     2<<8>>3=64
pub struct StrideNode<const T: usize>
where
    [u8; max(1, 2 << (T - 1) >> 3)]: Sized,
    [u8; max(1, 2 << T >> 3)]: Sized,
{
    pub ptrbitarr: [u8; max(1, 2 << (T - 1) >> 3)],
    pub pfxbitarr: [u8; max(1, 2 << T >> 3)],

    // Use usize node indices because we index into a global node array held by the tree which may hold a large
    // number of prefixes. If we instead each node had its own collections of referenced nodes and prefixes we
    // could use a much smaller index value type, but would then have to do more memory management on tree updates.
    pub ptrvec: Vec<usize>,
    pub pfxvec: Vec<usize>,
}

impl<const T: usize> Default for StrideNode<T>
where
    [u8; max(1, 2 << (T - 1) >> 3)]: Sized,
    [u8; max(1, 2 << T >> 3)]: Sized,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const T: usize> StrideNode<T>
where
    [u8; max(1, 2 << (T - 1) >> 3)]: Sized,
    [u8; max(1, 2 << T >> 3)]: Sized,
{
    pub fn new() -> Self {
        Self {
            ptrbitarr: [0; max(1, 2 << (T - 1) >> 3)],
            pfxbitarr: [0; max(1, 2 << T >> 3)],
            ptrvec: Vec::new(),
            pfxvec: Vec::new(),
        }
    }

    pub const fn stride_size(&self) -> usize {
        T
    }

    pub fn add_prefix(&mut self, bit_idx: usize, prefix_idx: usize) {
        if !self.pfxbitarr.set_bit(bit_idx) {
            let insert_idx = self.pfxbitarr.count_ones_upto(bit_idx) - 1;
            self.pfxvec.insert(insert_idx, prefix_idx);
        }
    }

    pub fn add_child_node(&mut self, bit_idx: usize, node_idx: usize) {
        if !self.ptrbitarr.set_bit(bit_idx) {
            let insert_idx = self.ptrbitarr.count_ones_upto(bit_idx) - 1;
            self.ptrvec.insert(insert_idx, node_idx);
        } else {
            panic!("Attempted to add child node but ptrbitarr is already set at bit idx {}", bit_idx);
        }
    }

    pub fn get_child_node_idx(&mut self, bit_idx: usize) -> Option<usize> {
        if self.ptrbitarr.bit_set(bit_idx) {
            let idx = self.ptrbitarr.count_ones_upto(bit_idx) - 1;
            Some(self.ptrvec[idx].into())
        } else {
            None
        }
    }
}

impl<const T: usize> std::fmt::Debug for StrideNode<T>
where
    [u8; max(1, 2 << (T - 1) >> 3)]: Sized,
    [u8; max(1, 2 << T >> 3)]: Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn format_bit_arr(iter: std::slice::Iter<u8>) -> String {
            let mut bit_string = String::new();
            let mut num_bytes = 0;
            for byte in iter {
                bit_string.push_str(&format!("{:0>8b}", byte));
                num_bytes += 1;
            }
            let num_bits = num_bytes << 3;
            format!("{:0>width$}", &bit_string, width = num_bits)
        }

        f.debug_struct("StrideNode")
            .field("ptrbitarr", &format_bit_arr(self.ptrbitarr.iter()))
            .field("pfxbitarr", &format_bit_arr(self.pfxbitarr.iter()))
            .field("ptrvec", &self.ptrvec)
            .field("pfxvec", &self.pfxvec)
            .finish()
    }
}

trait PfxBitArrayOps<const T: usize> {
    /// Is the specified bit set?
    fn bit_set(&self, bit_idx: usize) -> bool;

    /// Set the bit at the specified 0-based counting from the left bit index.
    /// Returns true if the bit was already set, false otherwise.
    fn set_bit(&mut self, bit_idx: usize) -> bool;

    /// Count the number of leading ones upto and including the specified 0-based counting from the left bit index.
    fn count_ones_upto(&self, bit_idx: usize) -> usize;
}

impl<const T: usize> PfxBitArrayOps<T> for [u8; T] {
    fn bit_set(&self, bit_idx: usize) -> bool {
        let byte_idx = bit_idx >> 3;
        let shift_by = bit_idx % 8;
        let mask = 0b10000000_u8 >> shift_by;
        self[byte_idx] & mask != 0
    }

    fn set_bit(&mut self, bit_idx: usize) -> bool {
        let byte_idx = bit_idx >> 3;
        let shift_by = bit_idx % 8;
        let mask = 0b10000000_u8 >> shift_by;
        let val = self[byte_idx] & mask;
        self[byte_idx] |= mask;
        val != 0
    }

    fn count_ones_upto(&self, bit_idx: usize) -> usize {
        let mut num_ones: usize = 0;

        let max_byte_idx = bit_idx >> 3;
        let bit_idx = bit_idx % 8;

        for byte in self.iter().take(max_byte_idx) {
            let count = byte.count_ones() as usize;
            num_ones += count;
        }

        let mask = if bit_idx < 7 {
            0b11111111_u8 << (8 - (bit_idx + 1))
        } else {
            0b11111111_u8
        };

        let v = self[max_byte_idx] & mask;
        num_ones + (v.count_ones() as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_byte() {
        let mut v = [0u8; 1];
        let mut mask = 0b10000000_u8;

        for i in 0..8 {
            assert_eq!(v.count_ones_upto(7), i);
            assert!(!v.set_bit(i));
            assert_eq!(v.count_ones_upto(7), i + 1);
            assert_eq!(mask, v[0]);
            assert!(v.set_bit(i));
            mask >>= 1;
            mask |= 0b10000000_u8;
        }
    }

    #[test]
    fn double_byte() {
        let mut v = [0u8; 2];

        let mut byte0_mask = 0b10000000_u8;
        for i in 0..8 {
            assert_eq!(v.count_ones_upto(15), i);
            assert!(!v.set_bit(i));
            assert_eq!(v.count_ones_upto(15), i + 1);
            assert_eq!(byte0_mask, v[0]);
            assert!(v.set_bit(i));
            byte0_mask >>= 1;
            byte0_mask |= 0b10000000_u8;
        }

        let mut byte1_mask = 0b10000000_u8;
        for i in 8..16 {
            assert_eq!(v.count_ones_upto(15), i);
            assert!(!v.set_bit(i));
            assert_eq!(v.count_ones_upto(15), i + 1);
            assert_eq!(byte0_mask, v[0]);
            assert_eq!(byte1_mask, v[1]);
            assert!(v.set_bit(i));
            byte1_mask >>= 1;
            byte1_mask |= 0b10000000_u8;
        }
    }
}

#[derive(Debug)]
pub struct TreeBitMap {
    strides: Vec<u8>,
    pub nodes: Vec<VariableSizeStrideNode>,
    pub prefixes: Vec<Prefix>, // (prefix ipv4, prefix len)
}

impl TreeBitMap {
    pub fn new(strides: Vec<u8>) -> Self {
        // TODO: sanity check the given stride configuration.

        let root_node = VariableSizeStrideNode::new(strides[0].into());

        Self {
            strides,
            nodes: vec![root_node],
            prefixes: Vec::new(),
        }
    }

    pub fn statistics(&self) -> (usize, usize) {
        (self.nodes.len(), self.prefixes.len())
    }

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
                        let new_node = VariableSizeStrideNode::new(self.strides[depth].into());
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
}
