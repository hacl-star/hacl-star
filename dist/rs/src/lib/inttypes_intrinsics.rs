pub fn add_carry_u32(cin: u32, x: u32, y: u32, r: &mut [u32]) -> u32 {
    crate::hacl::inttypes_intrinsics::add_carry_u32(cin, x, y, r)
}

pub fn sub_borrow_u32(cin: u32, x: u32, y: u32, r: &mut [u32]) -> u32
{
    crate::hacl::inttypes_intrinsics::sub_borrow_u32(cin, x, y, r)
}

pub fn add_carry_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    crate::hacl::inttypes_intrinsics::add_carry_u64(cin, x, y, r)
}

pub fn sub_borrow_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    crate::hacl::inttypes_intrinsics::sub_borrow_u64(cin, x, y, r)
}
