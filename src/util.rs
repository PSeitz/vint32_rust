
// #[inline(always)]
// pub fn set_bit_at(input: &mut u8, n: u8) {
//     *input |= 1 << n
// }

const ONLY_HIGH_BIT_U8: u8 = 0b_1000_0000;
const ONLY_SECOND_HIGH_BIT_U8: u8 = 0b_0100_0000;

#[inline(always)]
pub fn set_high_bit_u8(input: u8) -> u8 {
    input | ONLY_HIGH_BIT_U8
}

#[inline(always)]
pub fn unset_high_bit_u8(input: u8) -> u8 {
    input << 1 >> 1
}
#[inline(always)]
pub fn unset_second_high_bit_u8(input: u8) -> u8 {
    input << 2 >> 2
}

#[inline(always)]
pub fn is_high_bit_set(input: u8) -> bool {
    input & ONLY_HIGH_BIT_U8 != 0
}

#[inline(always)]
pub fn set_second_high_bit_u8(input: u8) -> u8 {
    input | ONLY_SECOND_HIGH_BIT_U8
}
#[inline(always)]
pub fn is_second_high_bit_set(input: u8) -> bool {
    input & ONLY_SECOND_HIGH_BIT_U8 != 0
}
