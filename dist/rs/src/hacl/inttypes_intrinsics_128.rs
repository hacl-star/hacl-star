#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn add_carry_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    let res: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::uint64_to_uint128(x),
                crate::fstar::uint128::uint64_to_uint128(cin)
            ),
            crate::fstar::uint128::uint64_to_uint128(y)
        );
    let c: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(res, 64u32));
    r[0usize] = crate::fstar::uint128::uint128_to_uint64(res);
    c
}

pub fn sub_borrow_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    let res: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::sub_mod(
            crate::fstar::uint128::sub_mod(
                crate::fstar::uint128::uint64_to_uint128(x),
                crate::fstar::uint128::uint64_to_uint128(y)
            ),
            crate::fstar::uint128::uint64_to_uint128(cin)
        );
    let c: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(res, 64u32))
        &
        1u64;
    r[0usize] = crate::fstar::uint128::uint128_to_uint64(res);
    c
}
