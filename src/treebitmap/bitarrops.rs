// TODO: Consider using https://docs.rs/fixedbitset/0.4.0/fixedbitset/struct.FixedBitSet.html

pub trait PfxBitArrayOps<const T: usize> {
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
