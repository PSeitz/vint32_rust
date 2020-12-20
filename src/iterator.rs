use crate::*;
use std::iter::FusedIterator;

#[derive(Debug, Clone)]
pub struct VintArrayIterator<'a> {
    /// the slice containing only vint encoded data
    pub data: &'a [u8],
    /// the current offset in the slice
    pub pos: usize,
}

impl<'a> VintArrayIterator<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        VintArrayIterator { data, pos: 0 }
    }

    /// Generates a `VintArrayIterator` from a serialized `VintArray`.
    /// The expected format is the vint32-encoded size and then the data.
    #[inline]
    pub fn from_serialized_vint_array(data: &'a [u8]) -> Self {
        let mut iter = VintArrayIterator::new(data);
        if let Some(size) = iter.next() {
            VintArrayIterator::new(&data[iter.pos..iter.pos + size as usize])
        } else {
            VintArrayIterator::new(&data[..0])
        }
    }
}

impl<'a> Iterator for VintArrayIterator<'a> {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<u32> {
        decode_varint_slice(self.data, &mut self.pos)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            self.data.len() - self.pos / 2,
            Some(self.data.len() - self.pos),
        )
    }
}

impl<'a> FusedIterator for VintArrayIterator<'a> {}
