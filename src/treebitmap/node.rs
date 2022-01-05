/// Based on: https://blog.nlnetlabs.nl/donkeys-mules-horses/#pointerfree
use fixedbitset::FixedBitSet;

use crate::treebitmap::Error;

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
pub struct StrideNode {
    pub stride_size: usize,
    
    pub ptrbitarr: FixedBitSet,
    pub pfxbitarr: FixedBitSet,

    // Use usize node indices because we index into a global node array held by the tree which may hold a large
    // number of prefixes. If we instead each node had its own collections of referenced nodes and prefixes we
    // could use a much smaller index value type, but would then have to do more memory management on tree updates.
    pub ptrvec: Vec<usize>,
    pub pfxvec: Vec<usize>,
}

impl StrideNode {
    pub fn new(n: u8) -> Result<Self, Error> {
        if n > 8 {
            Err(Error::UnsupportedStrideSize(n))
        } else {
            Ok(Self {
                stride_size: n as usize,
                ptrbitarr: FixedBitSet::with_capacity(1.max(2 << (n - 1))),
                pfxbitarr: FixedBitSet::with_capacity(1.max(2 << n)),
                ptrvec: Vec::new(),
                pfxvec: Vec::new(),
            })
        }
    }

    pub const fn stride_size(&self) -> usize {
        self.stride_size
    }

    pub fn add_prefix(&mut self, bit_idx: usize, prefix_idx: usize) {
        if !self.pfxbitarr.put(bit_idx) {
            let insert_idx = self.pfxbitarr.count_ones(0..(bit_idx+1)) - 1;
            self.pfxvec.insert(insert_idx, prefix_idx);
        }
    }

    pub fn add_child_node(&mut self, bit_idx: usize, node_idx: usize) {
        if !self.ptrbitarr.put(bit_idx) {
            let insert_idx = self.ptrbitarr.count_ones(0..(bit_idx+1)) - 1;
            self.ptrvec.insert(insert_idx, node_idx);
        } else {
            panic!(
                "Attempted to add child node but ptrbitarr is already set at bit idx {}",
                bit_idx
            );
        }
    }

    pub fn get_child_node_idx(&self, bit_idx: usize) -> Option<usize> {
        if self.ptrbitarr.contains(bit_idx) {
            let idx = self.ptrbitarr.count_ones(0..(bit_idx+1)) - 1;
            Some(self.ptrvec[idx].into())
        } else {
            None
        }
    }

    pub fn get_prefix_node_idx(&self, bit_idx: usize) -> Option<usize> {
        if self.pfxbitarr.contains(bit_idx) {
            let idx = self.pfxbitarr.count_ones(0..(bit_idx+1)) - 1;
            Some(self.pfxvec[idx].into())
        } else {
            None
        }
    }
}

impl std::fmt::Debug for StrideNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StrideNode")
            .field("ptrbitarr", &self.ptrbitarr)
            .field("pfxbitarr", &self.pfxbitarr)
            .field("ptrvec", &self.ptrvec)
            .field("pfxvec", &self.pfxvec)
            .finish()
    }
}
