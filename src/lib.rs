use std::alloc::Layout;
use std::mem::{self, needs_drop};
use std::ptr::{self, NonNull};
use std::slice;

use bitpacking::{BitPacker, BitPacker4x};
use bumpalo::Bump;

#[derive(Debug)]
pub struct Bbbul<'bump> {
    bump: &'bump Bump,
    last: Option<u32>,
    area_len: usize,
    area: [u32; BitPacker4x::BLOCK_LEN],
    /// We must not have multiple references to the same memory
    /// when one of them is mutable. When reading the list from
    /// the head we make sure to first drop the &mut Node below.
    head: Option<NonNull<Node>>,
    /// Here we only keep &mut Node once. We made sure above to
    /// only have a pointer to the head and the next nodes.
    tail: Option<(&'bump mut Node, u32)>,
}

#[derive(Debug)]
#[repr(C)]
struct Node {
    next: Option<NonNull<Node>>,
    num_bits: u8,
    bytes: [u8],
}

impl Node {
    const BASE_SIZE: usize = mem::size_of::<(Option<NonNull<Node>>, u8)>();

    #[allow(clippy::mut_from_ref)]
    fn new_in(block_size: usize, bump: &Bump) -> &mut Node {
        let total_size = Self::BASE_SIZE + block_size;
        let align = mem::align_of::<Option<NonNull<Node>>>();
        let layout = Layout::from_size_align(total_size, align).unwrap();
        let ptr = bump.alloc_layout(layout).as_ptr();

        unsafe {
            // Init everything to zero and the next pointer too!
            ptr::write_bytes(ptr, 0, total_size);
            let slice = slice::from_raw_parts_mut(ptr, total_size);
            mem::transmute::<&mut [u8], &mut Node>(slice)
        }
    }
}

impl<'bump> Bbbul<'bump> {
    pub fn new_in(bump: &'bump Bump) -> Bbbul<'bump> {
        Bbbul {
            bump,
            last: None,
            area_len: 0,
            area: [0; BitPacker4x::BLOCK_LEN],
            head: None,
            tail: None,
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
                // Checking in debug that the working area
                // does not contain duplicated integers.
                debug_assert!({
                    let mut vec = self.area.to_vec();
                    vec.dedup();
                    vec.len() == self.area.len()
                });

                let last = self.tail.as_ref().map(|(_, l)| *l);
                let bp = BitPacker4x::new();
                let bits = bp.num_bits_strictly_sorted(last, &self.area);
                let block_size = BitPacker4x::compressed_block_size(bits);

                let node = Node::new_in(block_size, self.bump);
                node.num_bits = bits;
                debug_assert!(node.next.is_none());

                let last_compressed = *self.area.last().unwrap();
                let size = bp.compress_strictly_sorted(last, &self.area, &mut node.bytes, bits);
                debug_assert_eq!(node.bytes.len(), size);

                match &mut self.tail {
                    Some((tail, last)) => {
                        *last = last_compressed;
                        debug_assert!(tail.next.is_none());
                        tail.next = NonNull::new(node);
                        *tail = node;
                    }
                    None => {
                        debug_assert!(self.head.is_none());
                        self.head = NonNull::new(node);
                        self.tail = Some((node, last_compressed));
                    }
                }

                self.area_len = 0;

                // I need to push at the end of the list so I need
                //  - Pointer to optional last maillon of the list
                //  - Pointer to the optional head
                //
                // I need to create a FrozenBbbul that is sync and send (unsafe).
            }
        }
    }
}

pub struct FrozenBbbul<'a, 'bump>(&'a mut Bbbul<'bump>);

impl<'a, 'bump> FrozenBbbul<'a, 'bump> {
    /// Creates a `FrozenBbbul` that is `Send` and will never drop, allocate nor deallocate anything.
    pub fn new(bbbul: &'a mut Bbbul<'bump>) -> FrozenBbbul<'a, 'bump> {
        // We must make sure we do not read nodes while we have still
        // have a mutable reference on one of them. So, we remove the
        // &mut Node in the tail and only keep the head NonNull<Node>.
        bbbul.tail = None;
        FrozenBbbul(bbbul)
    }

    /// Removes all the numbers stored in this `Bbbul`.
    pub fn clear(&mut self) {
        self.0.area_len = 0;
        self.0.head = None;
        self.0.tail = None;
    }

    /// Returns wether this `Bbbul` is empty.
    pub fn is_empty(&self) -> bool {
        self.0.area_len == 0 && self.0.head.is_some()
    }

    /// Gives an iterator of block of integers and clears the `Bbbul` at the same time.
    pub fn iter_and_clear(&mut self) -> IterAndClear<'_> {
        IterAndClear {
            area_len: mem::replace(&mut self.0.area_len, 0),
            area: self.0.area,
            initial: None,
            head: self.0.head.take().map(|nn| unsafe { &*nn.as_ptr() }),
        }
    }
}

/// # Safety
///
/// - The FrozenBbbul never reallocates.
/// - The FrozenBbbul does not leak a shared reference to the allocator.
///
/// So, it is safe to send the contained shared reference to the allocator
unsafe impl<'a, 'bump> Send for FrozenBbbul<'a, 'bump> {}

pub struct IterAndClear<'bump> {
    area_len: usize,
    area: [u32; BitPacker4x::BLOCK_LEN],
    initial: Option<u32>,
    head: Option<&'bump Node>,
}

impl IterAndClear<'_> {
    pub fn next_block(&mut self) -> Option<&[u32]> {
        if self.area_len != 0 {
            let numbers = &self.area[..self.area_len];
            self.area_len = 0;
            Some(numbers)
        } else if let Some(node) = self.head.take() {
            self.head = node.next.map(|nn| unsafe { &*nn.as_ptr() });

            let bp = BitPacker4x::new();
            let actual_size = bp.decompress_strictly_sorted(
                self.initial,
                &node.bytes,
                &mut self.area,
                node.num_bits,
            );

            debug_assert_eq!(actual_size, self.area.len());
            self.initial = self.area.last().copied();

            Some(&self.area)
        } else {
            None
        }
    }
}

/// Make sure that Bbbul does not need drop.
const _BBBUL_NEEDS_DROP: () = if needs_drop::<Bbbul>() {
    unreachable!()
};

/// Make sure that FrozenBbbul does not need drop.
const _FROZEN_BBBUL_NEEDS_DROP: () = if needs_drop::<FrozenBbbul>() {
    unreachable!()
};

#[cfg(test)]
mod tests {
    use std::mem::needs_drop;

    use super::*;

    #[test]
    fn does_not_drop() {
        assert!(!needs_drop::<Bbbul>())
    }
}
