pub fn add(len: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{ crate::hacl::bignum_base::bn_add_eq_len_u32(len, a, b, res) }

pub fn sub(len: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{ crate::hacl::bignum_base::bn_sub_eq_len_u32(len, a, b, res) }

pub fn add_mod(len: u32, n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{ crate::hacl::bignum::bn_add_mod_n_u32(len, n, a, b, res) }

pub fn sub_mod(len: u32, n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{ crate::hacl::bignum::bn_sub_mod_n_u32(len, n, a, b, res) }

pub fn lt_mask(len: u32, a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut acc: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    acc
}

pub fn eq_mask(len: u32, a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut mask: u32 = 0xFFFFFFFFu32;
    for i in 0u32..len
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u32 = mask;
    mask1
}