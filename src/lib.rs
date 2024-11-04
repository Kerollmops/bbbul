use std::{mem, ptr::NonNull};

use bitpacking::{BitPacker, BitPacker4x};
use bumpalo::Bump;

#[derive(Debug)]
pub struct Bbbul<'b> {
    bump: &'b Bump,
    last: Option<u32>,
    area_len: usize,
    area: [u32; BitPacker4x::BLOCK_LEN],
    nodes: Option<(&'b [u8], u32)>,
}

impl<'b> Bbbul<'b> {
    pub fn new_in(bump: &'b Bump) -> Bbbul<'b> {
        Bbbul {
            bump,
            last: None,
            area_len: 0,
            area: [0; BitPacker4x::BLOCK_LEN],
            nodes: None,
        }
    }

    /// You *must not* insert the same integer multiple times
    /// or it may panic.
    pub fn insert(&mut self, n: u32) {
        if self.last != Some(n) {
            self.last = Some(n);
            self.area[self.area_len] = n;
            self.area_len += 1;
            if self.area_len == self.area.len() {
                self.area.sort_unstable();
                // Just checking in debug that the working area
                // does not contain duplicated integers.
                debug_assert!({
                    let mut vec = self.area.to_vec();
                    vec.dedup();
                    vec.len() == self.area.len()
                });

                let pre_largest = self.nodes.map(|(_, l)| l);
                let bitpacker = BitPacker4x::new();
                let num_bits = bitpacker.num_bits_strictly_sorted(pre_largest, &self.area);
                let block_size = BitPacker4x::compressed_block_size(num_bits);
                let alloc = self.bump.alloc_slice_fill_copy(block_size, 0);
                let actual_size =
                    bitpacker.compress_strictly_sorted(pre_largest, &self.area, alloc, num_bits);
                debug_assert_eq!(alloc.len(), actual_size);

                // ...
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
