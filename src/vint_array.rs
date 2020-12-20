use crate::iterator::VintArrayIterator;
use crate::*;

#[derive(Debug, Clone, Default)]
pub struct VIntArray {
    pub data: Vec<u8>,
}

/// Encodes `vint32` unsigned 32-bit integers into a vec.
///
impl VIntArray {
    /// Creates a `VIntArray` from a slice of u32
    #[inline]
    pub fn from_vals(vals: &[u32]) -> VIntArray {
        let mut arr = VIntArray::default();
        arr.encode_vals(vals);
        arr
    }

    /// Encode `vals` into `VIntArray`
    #[inline]
    pub fn encode_vals(&mut self, vals: &[u32]) {
        for val in vals {
            encode_varint_into(&mut self.data, *val);
        }
    }

    /// serializes `VIntArray`, by appending its size vint-encoded and then the data.
    /// Maximum supported size of encoded data is therefore u32::MAX
    #[inline]
    pub fn serialize(&self) -> Vec<u8> {
        let mut serialized = Vec::with_capacity(self.data.len() + 4);
        encode_varint_into(&mut serialized, self.data.len() as u32);
        serialized.extend_from_slice(&self.data);
        serialized
    }

    /// Encode single `val` into `VIntArray`
    #[inline]
    pub fn encode(&mut self, val: u32) {
        encode_varint_into(&mut self.data, val);
    }

    pub fn iter(&self) -> VintArrayIterator {
        VintArrayIterator::new(&self.data)
    }
}
