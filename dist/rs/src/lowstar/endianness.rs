use std::convert::TryInto;

// Little Endian

pub fn load32_le(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes[0..4].try_into().unwrap())
}

pub fn store32_le(bytes: &mut[u8], x: u32) {
    bytes[0..4].copy_from_slice(&u32::to_le_bytes(x))
}

pub fn load64_le(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes[0..8].try_into().unwrap())
}

pub fn store64_le(bytes: &mut[u8], x: u64) {
    bytes[0..8].copy_from_slice(&u64::to_le_bytes(x))
}

// Big Endian

pub fn load32_be(bytes: &[u8]) -> u32 {
    u32::from_be_bytes(bytes[0..4].try_into().unwrap())
}

pub fn store32_be(bytes: &mut[u8], x: u32) {
    bytes[0..4].copy_from_slice(&u32::to_be_bytes(x))
}

pub fn load64_be(bytes: &[u8]) -> u64 {
    u64::from_be_bytes(bytes[0..8].try_into().unwrap())
}

pub fn store64_be(bytes: &mut[u8], x: u64) {
    bytes[0..8].copy_from_slice(&u64::to_be_bytes(x))
}
