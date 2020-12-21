/*! 
VIntArrayEncodeMostCommon reserves one bit to encode the most common element as the following element.

`0b11000000`

So the upper limits to encode values are halfed.
0    -  2^6     -> 1 byte
2^6  -  2^13    -> 2 byte
2^13 -  2^20    -> 3 byte
2^20 -  2^27    -> 4 byte
2^27 >          -> 5 byte


# Examples
```
use vint32::common_encode::VIntArrayEncodeMostCommon; 
let mut vint = VIntArrayEncodeMostCommon::default();
let dat = vec![4_000_000_000];
vint.encode_vals(&dat);
let decoded_data: Vec<u32> = vint.iter().collect();
assert_eq!(&dat, &decoded_data);;

```

*/

use crate::encode_varint_into;
use crate::iterator::VintArrayIterator;
use itertools::Itertools;
use std::iter::FusedIterator;
use std::mem::transmute;
use crate::util::*;

#[derive(Debug, Clone, Default)]
pub struct VIntArrayEncodeMostCommon {
    pub data: Vec<u8>,
    pub most_common_val: Option<u32>,
}

const BITS_NEEDED_FOR_MOST_COMMON_ENCODING: usize = 1;

#[derive(Debug)]
enum BytesRequired {
    One = 1,
    Two,
    Three,
    Four,
    Five,
}

fn get_bytes_required(val: u32) -> BytesRequired {
    if val < 1 << 6 {
        //64  1 byte for most_common, 1 bit to signal more
        BytesRequired::One
    } else if val < 1 << 13 {
        BytesRequired::Two
    } else if val < 1 << 20 {
        BytesRequired::Three
    } else if val < 1 << 27 {
        BytesRequired::Four
    } else {
        BytesRequired::Five
    }
}

pub fn push_compact(num: u32, data: &mut Vec<u8>) {
    encode_varint_into(data, num);
}

/// VIntArrayEncodeMostCommon reserves one bit to encode the most common element as the following element.
///
/// `0b11000000`
///
/// So the upper limits to encode values are halfed.
/// 0    -  2^6     -> 1 byte
/// 2^6  -  2^13    -> 2 byte
/// 2^13 -  2^20    -> 3 byte
/// 2^20 -  2^27    -> 4 byte
/// 2^27 >          -> 5 byte
///
impl VIntArrayEncodeMostCommon {
    pub fn get_space_used_by_most_common_val(&mut self, vals: &[u32]) -> (u32, u32) {
        let mut newvec: Vec<u32> = vals.to_vec();
        newvec.sort_unstable();

        let mut current_biggest_el = 0;
        let mut current_biggest_el_bytes_required = 0;
        for (el, group) in &newvec.iter().group_by(|el| *el) {
            let bytes_required = get_bytes_required(*el) as u32;
            let total_bytes_required = group.count() as u32 * bytes_required;
            if total_bytes_required > current_biggest_el_bytes_required {
                current_biggest_el_bytes_required = total_bytes_required;
                current_biggest_el = *el;
            }
        }
        (current_biggest_el, current_biggest_el_bytes_required)
    }

    #[inline]
    pub fn serialize(&self) -> Vec<u8> {
        let mut serialized = Vec::with_capacity(self.data.len() + 4);
        // encode values, as normal vint
        push_compact(self.data.len() as u32, &mut serialized);
        push_compact(self.most_common_val.unwrap_or(0), &mut serialized);
        serialized.extend_from_slice(&self.data);
        serialized
    }

    #[inline]
    /// decodes data from a slice and returns the total size of the data in the slice in bytes
    pub fn decode_from_slice(data: &[u8]) -> (Vec<u32>, u32) {
        let mut iter = VintArrayIterator::new(data); // the first two, are encoded as normal vint
        if let Some(size) = iter.next() {
            let most_common_val = iter.next().expect("wrong vint format, expexted most_common_val, but got nothing");
            let mut iter_data = VintArrayMostCommonIterator::new(&data[iter.pos..iter.pos + size as usize], most_common_val);
            let mut data = vec![];
            while let Some(el) = iter_data.next() {
                data.push(el);
            }
            (data, iter.pos as u32 + iter_data.pos as u32)
        } else {
            (vec![], iter.pos as u32)
        }
    }

    pub fn encode_vals(&mut self, vals: &[u32]) {
        if vals.is_empty() {
            return;
        }
        if self.most_common_val.is_none() {
            let (most_common_val, _space_used) = self.get_space_used_by_most_common_val(vals);
            self.most_common_val = Some(most_common_val);
        }
        let mut iter = vals.iter().peekable();
        while let Some(val) = iter.next() {
            let mut move_iter = false;
            if let Some(next_val) = iter.peek() {
                if **next_val == self.most_common_val.unwrap() {
                    self.encode(*val, true);
                    move_iter = true;
                } else {
                    self.encode(*val, false);
                }
            } else {
                self.encode(*val, false);
            }
            if move_iter {
                iter.next(); // move_iter, because next val is already encoded
            };
        }
    }

    fn encode_large(&mut self, val: u32, next_is_most_common_val: bool) {
        let mut pos = 0;
        let mut el = val;
        let mut push_n_set = |last_block: bool| {
            if pos == 4 {
                let mut el_u64: u64 = u64::from(val);
                el_u64 <<= 5;
                let bytes: [u8; 8] = unsafe { transmute(el_u64) };
                self.data.push(bytes[pos]);
                return;
            }
            let is_first_block = pos == 0;
            if pos > 0 {
                el <<= 1;
            }
            let mut byte = unsafe { transmute::<u32, [u8; 4]>(el)[pos] };
            if is_first_block {
                if next_is_most_common_val {
                    byte = set_second_high_bit_u8(byte);
                } else {
                    byte = unset_second_high_bit_u8(byte);
                }
            }
            if last_block {
                self.data.push(byte);
            } else {
                self.data.push(set_high_bit_u8(byte));
            }
            if pos == 0 {
                el <<= 1;
            }
            pos += 1;
        };

        push_n_set(false);
        push_n_set(false);
        push_n_set(false);
        push_n_set(false);
        push_n_set(true);
    }

    fn encode(&mut self, val: u32, next_is_most_common_val: bool) {
        let bytes_req = get_bytes_required(val);
        if val >= 1 << 27 {
            self.encode_large(val.to_le(), next_is_most_common_val);
            return;
        }

        let mut pos = 0;
        let mut el = val.to_le();
        let mut push_n_set = |last_block: bool| {
            let is_first_block = pos == 0;
            if pos > 0 {
                el <<= 1;
            }
            let mut byte = unsafe { transmute::<u32, [u8; 4]>(el)[pos] };
            if is_first_block {
                if next_is_most_common_val {
                    byte = set_second_high_bit_u8(byte);
                } else {
                    byte = unset_second_high_bit_u8(byte);
                }
            }
            if last_block {
                self.data.push(byte);
            } else {
                self.data.push(set_high_bit_u8(byte));
            }
            if pos == 0 {
                el <<= 1;
            }
            pos += 1;
        };

        match bytes_req {
            BytesRequired::One => {
                push_n_set(true);
            }
            BytesRequired::Two => {
                push_n_set(false);
                push_n_set(true);
            }
            BytesRequired::Three => {
                push_n_set(false);
                push_n_set(false);
                push_n_set(true);
            }
            BytesRequired::Four => {
                push_n_set(false);
                push_n_set(false);
                push_n_set(false);
                push_n_set(true);
            }
            _ => {
                panic!("should not happen");
            }
        }
    }

    pub fn iter(&self) -> VintArrayMostCommonIterator {
        VintArrayMostCommonIterator::new(&self.data, self.most_common_val.unwrap_or(0))
    }
}

#[derive(Debug, Clone)]
pub struct VintArrayMostCommonIterator<'a> {
    pub data: &'a [u8],
    pub pos: usize,
    next_val: Option<u32>,
    pub most_common_val: u32,
}

impl<'a> VintArrayMostCommonIterator<'a> {
    pub fn new(data: &'a [u8], most_common_val: u32) -> Self {
        VintArrayMostCommonIterator {
            data,
            pos: 0,
            next_val: None,
            most_common_val,
        }
    }

    #[inline]
    pub fn from_slice(data: &'a [u8]) -> Self {
        let mut iter = VintArrayIterator::new(data); // the first two, are encoded as normal vint
        if let Some(size) = iter.next() {
            let most_common_val = iter.next().expect("wrong vint format, expexted most_common_val, but got nothing");
            VintArrayMostCommonIterator::new(&data[iter.pos..iter.pos + size as usize], most_common_val)
        } else {
            VintArrayMostCommonIterator::new(&data[..0], 0)
        }
    }

    #[inline]
    fn decode_u8(&self, pos: usize) -> (u8, bool) {
        unsafe {
            let el = *self.data.get_unchecked(pos);
            if is_high_bit_set(el) {
                (unset_high_bit_u8(el), true)
            } else {
                (el, false)
            }
        }
    }

    #[inline]
    fn get_apply_bits(&self, pos: usize, offset: usize, val: &mut u32) -> bool {
        let (val_u8, has_more) = self.decode_u8(pos);

        let mut bytes: [u8; 4] = [0, 0, 0, 0];
        bytes[offset] = val_u8;
        let mut add_val: u32 = unsafe { transmute(bytes) };
        add_val >>= offset + BITS_NEEDED_FOR_MOST_COMMON_ENCODING;
        *val |= add_val;

        has_more
    }
}

impl<'a> Iterator for VintArrayMostCommonIterator<'a> {
    type Item = u32;

    #[inline]
    fn next(&mut self) -> Option<u32> {
        if let Some(next_val) = self.next_val {
            self.next_val = None;
            return Some(next_val);
        }

        if self.pos == self.data.len() {
            None
        } else {
            let (mut val_u8, has_more) = self.decode_u8(self.pos);
            if is_second_high_bit_set(val_u8) {
                val_u8 = unset_second_high_bit_u8(val_u8);
                self.next_val = Some(self.most_common_val);
            }
            self.pos += 1;
            let mut val = u32::from(val_u8);
            if has_more {
                let has_more = self.get_apply_bits(self.pos, 1, &mut val);
                self.pos += 1;
                if has_more {
                    let has_more = self.get_apply_bits(self.pos, 2, &mut val);
                    self.pos += 1;
                    if has_more {
                        let has_more = self.get_apply_bits(self.pos, 3, &mut val);
                        self.pos += 1;
                        if has_more {
                            let el = unsafe { *self.data.get_unchecked(self.pos) };
                            let bytes: [u8; 8] = [0, 0, 0, 0, el, 0, 0, 0];
                            let mut add_val: u64 = unsafe { transmute(bytes) };
                            add_val >>= 5;
                            val |= add_val as u32;
                            self.pos += 1;
                        }
                    }
                }
            }
            Some(u32::from_le(val))
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.data.len() - self.pos / 2, Some(self.data.len() - self.pos))
    }
}

impl<'a> FusedIterator for VintArrayMostCommonIterator<'a> {}

#[test]
fn test_serialize() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![4_000, 1_000, 2_000, 4_000, 4_000];
    vint.encode_vals(&dat);

    let data = vint.serialize();

    let iter = VintArrayMostCommonIterator::from_slice(&data);
    let decoded_data: Vec<u32> = iter.collect();
    assert_eq!(&dat, &decoded_data);
}

#[test]
fn test_serialize_and_recreate_from_slice() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![4_000, 1_000, 2_000, 4_000, 4_000];
    vint.encode_vals(&dat);

    let data = vint.serialize();

    let (data, _) = VIntArrayEncodeMostCommon::decode_from_slice(&data);
    assert_eq!(&dat, &data);
}

#[test]
fn test_empty_iter() {
    let dat = vec![];
    let iter = VintArrayMostCommonIterator::from_slice(&dat);
    let decoded_data: Vec<u32> = iter.collect();
    let nothing: Vec<u32> = vec![];
    assert_eq!(nothing, decoded_data);
}

#[test]
fn test_encode_decode_vint_most_common_1000() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![1000, 1000, 1000];
    vint.encode_vals(&dat);
    let decoded_data: Vec<u32> = vint.iter().collect();
    assert_eq!(&dat, &decoded_data);
}

#[test]
fn test_encode_decode_vint_most_common_testo() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![4_000, 1_000, 2_000, 4_000, 4_000];
    vint.encode_vals(&dat);
    let decoded_data: Vec<u32> = vint.iter().collect();
    assert_eq!(&dat, &decoded_data);
}

#[test]
fn test_encode_decode_vint_most_common_single() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![10];
    vint.encode_vals(&dat);
    let decoded_data: Vec<u32> = vint.iter().collect();
    assert_eq!(&dat, &decoded_data);
}

#[test]
fn test_encode_decode_vint_most_common_very_large_number() {
    let mut vint = VIntArrayEncodeMostCommon::default();
    let dat = vec![4_000_000_000];
    vint.encode_vals(&dat);
    let decoded_data: Vec<u32> = vint.iter().collect();
    assert_eq!(&dat, &decoded_data);
}
