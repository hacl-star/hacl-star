use std::convert::TryInto;

pub fn load32_le(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes.try_into().unwrap())
}

pub fn store32_le(bytes: &mut[u8], x: u32) {
    bytes.copy_from_slice(&u32::to_le_bytes(x))
}
