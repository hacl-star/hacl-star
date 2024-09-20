#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn add_carry_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    let res: fstar::uint128::uint128 =
        fstar::uint128::add_mod(
            fstar::uint128::add_mod(
                fstar::uint128::uint64_to_uint128(x),
                fstar::uint128::uint64_to_uint128(cin)
            ),
            fstar::uint128::uint64_to_uint128(y)
        );
    let c: u64 = fstar::uint128::uint128_to_uint64(fstar::uint128::shift_right(res, 64u32));
    r[0usize] = fstar::uint128::uint128_to_uint64(res);
    c
}

pub fn sub_borrow_u64(cin: u64, x: u64, y: u64, r: &mut [u64]) -> u64
{
    let res: fstar::uint128::uint128 =
        fstar::uint128::sub_mod(
            fstar::uint128::sub_mod(
                fstar::uint128::uint64_to_uint128(x),
                fstar::uint128::uint64_to_uint128(y)
            ),
            fstar::uint128::uint64_to_uint128(cin)
        );
    let c: u64 = fstar::uint128::uint128_to_uint64(fstar::uint128::shift_right(res, 64u32)) & 1u64;
    r[0usize] = fstar::uint128::uint128_to_uint64(res);
    c
}
