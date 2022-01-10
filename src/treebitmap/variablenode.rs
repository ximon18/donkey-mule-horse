use crate::treebitmap::node::StrideNode;

pub type VariableSizeStrideNode = StrideNode;

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
    ($stride_size:literal, $bits:ident) => {{
        const MASK: u32 = u32::MAX << (32 - $stride_size);
        const MAX: u32 = MASK >> (32 - $stride_size);
        let ptrbitarr_bit_idx = ($bits & MASK) >> (32 - $stride_size);
        let pfxbitarr_bit_idx = MAX + ptrbitarr_bit_idx;
        (pfxbitarr_bit_idx as usize, ptrbitarr_bit_idx as usize)
    }};
}

impl StrideNode {
    /// Returns (pfxbitarr idx, ptrbitarr idx) where each idx is 0-based counting from the left.
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
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[rustfmt::skip]
    fn indices_check() {
        let sn = VariableSizeStrideNode::new(1).unwrap();
        assert_eq!(sn.get_matching_bitarr_indices(0b00000000_00000000_00000000_00000000u32, 1), (1, 0));
        assert_eq!(sn.get_matching_bitarr_indices(0b10000000_00000000_00000000_00000000u32, 1), (2, 1));

        let sn = VariableSizeStrideNode::new(2).unwrap();
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
        let sn = VariableSizeStrideNode::new(3).unwrap();
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
