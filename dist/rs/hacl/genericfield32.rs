#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub type pbn_mont_ctx_u32 <'a> = &'a [bignum::bignum::bn_mont_ctx_u32];

/**
Check whether this library will work for a modulus `n`.

  The function returns false if any of the following preconditions are violated,
  true otherwise.
  • n % 2 = 1
  • 1 < n
*/
pub fn
field_modulus_check(len: u32, n: &[u32]) ->
    bool
{
    let m: u32 = bignum::bignum::bn_check_modulus_u32(len, n);
    m == 0xFFFFFFFFu32
}

/**
Heap-allocate and initialize a montgomery context.

  The argument n is meant to be `len` limbs in size, i.e. uint32_t[len].

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n % 2 = 1
  • 1 < n

  The caller will need to call Hacl_GenericField32_field_free on the return value
  to avoid memory leaks.
*/
pub fn
field_init(len: u32, n: &[u32]) ->
    Box<[bignum::bignum::bn_mont_ctx_u32]>
{
    let mut r2: Box<[u32]> = vec![0u32; len as usize].into_boxed_slice();
    let mut n1: Box<[u32]> = vec![0u32; len as usize].into_boxed_slice();
    let r21: &mut [u32] = &mut r2;
    let n11: &mut [u32] = &mut n1;
    (n11[0usize..len as usize]).copy_from_slice(&n[0usize..len as usize]);
    let nBits: u32 = 32u32.wrapping_mul(bignum::bignum_base::bn_get_top_index_u32(len, n));
    bignum::bignum::bn_precomp_r2_mod_n_u32(len, nBits, n, r21);
    let mu: u32 = bignum::bignum::mod_inv_uint32(n[0usize]);
    let res: bignum::bignum::bn_mont_ctx_u32 =
        bignum::bignum::bn_mont_ctx_u32 { len, n: (*n11).into(), mu, r2: (*r21).into() };
    let buf: Box<[bignum::bignum::bn_mont_ctx_u32]> = vec![res].into_boxed_slice();
    buf
}

/**
Return the size of a modulus `n` in limbs.

  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
field_get_len(k: &[bignum::bignum::bn_mont_ctx_u32]) ->
    u32
{ (k[0usize]).len }

/**
Convert a bignum from the regular representation to the Montgomery representation.

  Write `a * R mod n` in `aM`.

  The argument a and the outparam aM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
to_field(k: &[bignum::bignum::bn_mont_ctx_u32], a: &[u32], aM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    bignum::bignum::bn_to_mont_u32(len1, &uu____0.n, uu____0.mu, &uu____0.r2, a, aM)
}

/**
Convert a result back from the Montgomery representation to the regular representation.

  Write `aM / R mod n` in `a`, i.e.
  Hacl_GenericField32_from_field(k, Hacl_GenericField32_to_field(k, a)) == a % n

  The argument aM and the outparam a are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
from_field(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], a: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    bignum::bignum::bn_from_mont_u32(len1, &uu____0.n, uu____0.mu, aM, a)
}

/**
Write `aM + bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
add(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], bM: &[u32], cM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    let mut a_copy: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
    let mut b_copy: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
    ((&mut a_copy)[0usize..len1 as usize]).copy_from_slice(&aM[0usize..len1 as usize]);
    ((&mut b_copy)[0usize..len1 as usize]).copy_from_slice(&bM[0usize..len1 as usize]);
    bignum::bignum::bn_add_mod_n_u32(len1, &uu____0.n, &a_copy, &b_copy, cM)
}

/**
Write `aM - bM mod n` to `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
sub(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], bM: &[u32], cM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    bignum::bignum::bn_sub_mod_n_u32(len1, &(k[0usize]).n, aM, bM, cM)
}

/**
Write `aM * bM mod n` in `cM`.

  The arguments aM, bM, and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
mul(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], bM: &[u32], cM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    bignum::bignum::bn_mont_mul_u32(len1, &uu____0.n, uu____0.mu, aM, bM, cM)
}

/**
Write `aM * aM mod n` in `cM`.

  The argument aM and the outparam cM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
sqr(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], cM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    bignum::bignum::bn_mont_sqr_u32(len1, &uu____0.n, uu____0.mu, aM, cM)
}

/**
Convert a bignum `one` to its Montgomery representation.

  The outparam oneM is meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.
*/
pub fn
one(k: &[bignum::bignum::bn_mont_ctx_u32], oneM: &mut [u32])
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    bignum::bignum::bn_from_mont_u32(len1, &uu____0.n, uu____0.mu, &uu____0.r2, oneM)
}

/**
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  This function is constant-time over its argument b, at the cost of a slower
  execution time than exp_vartime.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits
*/
pub fn
exp_consttime(
    k: &[bignum::bignum::bn_mont_ctx_u32],
    aM: &[u32],
    bBits: u32,
    b: &[u32],
    resM: &mut [u32]
)
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    let mut aMc: Box<[u32]> = vec![0u32; uu____0.len as usize].into_boxed_slice();
    ((&mut aMc)[0usize..uu____0.len as usize]).copy_from_slice(&aM[0usize..uu____0.len as usize]);
    if bBits < 200u32
    {
        let mut ctx: Box<[u32]> = vec![0u32; len1.wrapping_add(len1) as usize].into_boxed_slice();
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(&(&uu____0.n)[0usize..len1 as usize]);
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&uu____0.r2)[0usize..len1 as usize]
        );
        let mut sw: [u32; 1] = [0u32; 1usize];
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(len1 as usize);
        bignum::bignum::bn_from_mont_u32(len1, ctx_r2.0, uu____0.mu, ctx_r2.1, resM);
        for i in 0u32..bBits
        {
            let i1: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_div(32u32);
            let j: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            let sw1: u32 = bit ^ (&sw)[0usize];
            for i0 in 0u32..len1
            {
                let dummy: u32 = 0u32.wrapping_sub(sw1) & (resM[i0 as usize] ^ (&aMc)[i0 as usize]);
                resM[i0 as usize] ^= dummy;
                (&mut aMc)[i0 as usize] = (&aMc)[i0 as usize] ^ dummy
            };
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            bignum::bignum::bn_mont_mul_u32(len1, ctx_n0.1, uu____0.mu, &aMc, resM, &mut aMc);
            let ctx_n1: (&[u32], &[u32]) = ctx_n0.1.split_at(0usize);
            bignum::bignum::bn_mont_sqr_u32(len1, ctx_n1.1, uu____0.mu, resM, resM);
            (&mut sw)[0usize] = bit
        };
        let sw0: u32 = (&sw)[0usize];
        for i in 0u32..len1
        {
            let dummy: u32 = 0u32.wrapping_sub(sw0) & (resM[i as usize] ^ (&aMc)[i as usize]);
            resM[i as usize] ^= dummy;
            (&mut aMc)[i as usize] = (&aMc)[i as usize] ^ dummy
        }
    }
    else
    {
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: Box<[u32]> = vec![0u32; len1.wrapping_add(len1) as usize].into_boxed_slice();
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(&(&uu____0.n)[0usize..len1 as usize]);
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&uu____0.r2)[0usize..len1 as usize]
        );
        let mut table: Box<[u32]> =
            vec![0u32; 16u32.wrapping_mul(len1) as usize].into_boxed_slice();
        let mut tmp: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
        let t0: (&mut [u32], &mut [u32]) = table.split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(len1 as usize);
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(len1 as usize);
        bignum::bignum::bn_from_mont_u32(len1, ctx_r2.0, uu____0.mu, ctx_r2.1, t1.0);
        (t1.1[0usize..len1 as usize]).copy_from_slice(&(&aMc)[0usize..len1 as usize]);
        lowstar::ignore::ignore::<&[u32]>(&table);
        krml::unroll_for!(
            7,
            "i",
            0u32,
            1u32,
            {
                let t11: (&[u32], &[u32]) =
                    table.split_at(i.wrapping_add(1u32).wrapping_mul(len1) as usize);
                let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
                bignum::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, uu____0.mu, t11.1, &mut tmp);
                ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                    i
                ).wrapping_add(2u32).wrapping_mul(len1)
                as
                usize
                +
                len1 as usize]).copy_from_slice(&(&tmp)[0usize..len1 as usize]);
                let t2: (&[u32], &[u32]) =
                    table.split_at(
                        2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize
                    );
                let ctx_n1: (&[u32], &[u32]) = ctx_n0.1.split_at(0usize);
                bignum::bignum::bn_mont_mul_u32(len1, ctx_n1.1, uu____0.mu, &aMc, t2.1, &mut tmp);
                ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                    i
                ).wrapping_add(3u32).wrapping_mul(len1)
                as
                usize
                +
                len1 as usize]).copy_from_slice(&(&tmp)[0usize..len1 as usize])
            }
        );
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = bignum::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            (resM[0usize..len1 as usize]).copy_from_slice(
                &(&(&table)[0u32.wrapping_mul(len1) as usize..] as &[u32])[0usize..len1 as usize]
            );
            krml::unroll_for!(
                15,
                "i0",
                0u32,
                1u32,
                {
                    let c: u32 = fstar::uint32::eq_mask(bits_c, i0.wrapping_add(1u32));
                    let res_j: (&[u32], &[u32]) =
                        table.split_at(i0.wrapping_add(1u32).wrapping_mul(len1) as usize);
                    for i1 in 0u32..len1
                    {
                        let x: u32 = c & res_j.1[i1 as usize] | ! c & resM[i1 as usize];
                        let os: (&mut [u32], &mut [u32]) = resM.split_at_mut(0usize);
                        os.1[i1 as usize] = x
                    }
                }
            )
        }
        else
        {
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            let ctx_r20: (&[u32], &[u32]) = ctx_n0.1.split_at(len1 as usize);
            bignum::bignum::bn_from_mont_u32(len1, ctx_r20.0, uu____0.mu, ctx_r20.1, resM)
        };
        let mut tmp0: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            krml::unroll_for!(
                4,
                "_i",
                0u32,
                1u32,
                {
                    let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
                    bignum::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, uu____0.mu, resM, resM)
                }
            );
            let k2: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = bignum::bignum_base::bn_get_bits_u32(bLen, b, k2, 4u32);
            lowstar::ignore::ignore::<&[u32]>(&table);
            ((&mut tmp0)[0usize..len1 as usize]).copy_from_slice(
                &(&(&table)[0u32.wrapping_mul(len1) as usize..] as &[u32])[0usize..len1 as usize]
            );
            krml::unroll_for!(
                15,
                "i0",
                0u32,
                1u32,
                {
                    let c: u32 = fstar::uint32::eq_mask(bits_l, i0.wrapping_add(1u32));
                    let res_j: (&[u32], &[u32]) =
                        table.split_at(i0.wrapping_add(1u32).wrapping_mul(len1) as usize);
                    for i1 in 0u32..len1
                    {
                        let x: u32 = c & res_j.1[i1 as usize] | ! c & (&tmp0)[i1 as usize];
                        let os: (&mut [u32], &mut [u32]) = tmp0.split_at_mut(0usize);
                        os.1[i1 as usize] = x
                    }
                }
            );
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            bignum::bignum::bn_mont_mul_u32(len1, ctx_n0.1, uu____0.mu, resM, &tmp0, resM)
        }
    }
}

/**
Write `aM ^ b mod n` in `resM`.

  The argument aM and the outparam resM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

  The argument b is a bignum of any size, and bBits is an upper bound on the
  number of significant bits of b. A tighter bound results in faster execution
  time. When in doubt, the number of bits for the bignum size is always a safe
  default, e.g. if b is a 256-bit bignum, bBits should be 256.

  The function is *NOT* constant-time on the argument b. See the
  exp_consttime function for constant-time variant.

  Before calling this function, the caller will need to ensure that the following
  precondition is observed.
  • b < pow2 bBits
*/
pub fn
exp_vartime(
    k: &[bignum::bignum::bn_mont_ctx_u32],
    aM: &[u32],
    bBits: u32,
    b: &[u32],
    resM: &mut [u32]
)
{
    let len1: u32 = crate::genericfield32::field_get_len(k);
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    let mut aMc: Box<[u32]> = vec![0u32; uu____0.len as usize].into_boxed_slice();
    ((&mut aMc)[0usize..uu____0.len as usize]).copy_from_slice(&aM[0usize..uu____0.len as usize]);
    if bBits < 200u32
    {
        let mut ctx: Box<[u32]> = vec![0u32; len1.wrapping_add(len1) as usize].into_boxed_slice();
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(&(&uu____0.n)[0usize..len1 as usize]);
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&uu____0.r2)[0usize..len1 as usize]
        );
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(len1 as usize);
        bignum::bignum::bn_from_mont_u32(len1, ctx_r2.0, uu____0.mu, ctx_r2.1, resM);
        for i in 0u32..bBits
        {
            let i1: u32 = i.wrapping_div(32u32);
            let j: u32 = i.wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            if bit != 0u32
            {
                let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
                bignum::bignum::bn_mont_mul_u32(len1, ctx_n0.1, uu____0.mu, resM, &aMc, resM)
            };
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            bignum::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, uu____0.mu, &aMc, &mut aMc)
        }
    }
    else
    {
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: Box<[u32]> = vec![0u32; len1.wrapping_add(len1) as usize].into_boxed_slice();
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(&(&uu____0.n)[0usize..len1 as usize]);
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&uu____0.r2)[0usize..len1 as usize]
        );
        let mut table: Box<[u32]> =
            vec![0u32; 16u32.wrapping_mul(len1) as usize].into_boxed_slice();
        let mut tmp: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
        let t0: (&mut [u32], &mut [u32]) = table.split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(len1 as usize);
        let ctx_n: (&[u32], &[u32]) = ctx.split_at(0usize);
        let ctx_r2: (&[u32], &[u32]) = ctx_n.1.split_at(len1 as usize);
        bignum::bignum::bn_from_mont_u32(len1, ctx_r2.0, uu____0.mu, ctx_r2.1, t1.0);
        (t1.1[0usize..len1 as usize]).copy_from_slice(&(&aMc)[0usize..len1 as usize]);
        lowstar::ignore::ignore::<&[u32]>(&table);
        krml::unroll_for!(
            7,
            "i",
            0u32,
            1u32,
            {
                let t11: (&[u32], &[u32]) =
                    table.split_at(i.wrapping_add(1u32).wrapping_mul(len1) as usize);
                let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
                bignum::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, uu____0.mu, t11.1, &mut tmp);
                ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                    i
                ).wrapping_add(2u32).wrapping_mul(len1)
                as
                usize
                +
                len1 as usize]).copy_from_slice(&(&tmp)[0usize..len1 as usize]);
                let t2: (&[u32], &[u32]) =
                    table.split_at(
                        2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize
                    );
                let ctx_n1: (&[u32], &[u32]) = ctx_n0.1.split_at(0usize);
                bignum::bignum::bn_mont_mul_u32(len1, ctx_n1.1, uu____0.mu, &aMc, t2.1, &mut tmp);
                ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                    i
                ).wrapping_add(3u32).wrapping_mul(len1)
                as
                usize
                +
                len1 as usize]).copy_from_slice(&(&tmp)[0usize..len1 as usize])
            }
        );
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = bignum::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            let bits_l32: u32 = bits_c;
            let a_bits_l: (&[u32], &[u32]) = table.split_at(bits_l32.wrapping_mul(len1) as usize);
            (resM[0usize..len1 as usize]).copy_from_slice(&a_bits_l.1[0usize..len1 as usize])
        }
        else
        {
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            let ctx_r20: (&[u32], &[u32]) = ctx_n0.1.split_at(len1 as usize);
            bignum::bignum::bn_from_mont_u32(len1, ctx_r20.0, uu____0.mu, ctx_r20.1, resM)
        };
        let mut tmp0: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            krml::unroll_for!(
                4,
                "_i",
                0u32,
                1u32,
                {
                    let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
                    bignum::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, uu____0.mu, resM, resM)
                }
            );
            let k2: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = bignum::bignum_base::bn_get_bits_u32(bLen, b, k2, 4u32);
            lowstar::ignore::ignore::<&[u32]>(&table);
            let bits_l32: u32 = bits_l;
            let a_bits_l: (&[u32], &[u32]) = table.split_at(bits_l32.wrapping_mul(len1) as usize);
            ((&mut tmp0)[0usize..len1 as usize]).copy_from_slice(&a_bits_l.1[0usize..len1 as usize]);
            let ctx_n0: (&[u32], &[u32]) = ctx_r2.1.split_at(0usize - len1 as usize);
            bignum::bignum::bn_mont_mul_u32(len1, ctx_n0.1, uu____0.mu, resM, &tmp0, resM)
        }
    }
}

/**
Write `aM ^ (-1) mod n` in `aInvM`.

  The argument aM and the outparam aInvM are meant to be `len` limbs in size, i.e. uint32_t[len].
  The argument k is a montgomery context obtained through Hacl_GenericField32_field_init.

  Before calling this function, the caller will need to ensure that the following
  preconditions are observed.
  • n is a prime
  • 0 < aM
*/
pub fn
inverse(k: &[bignum::bignum::bn_mont_ctx_u32], aM: &[u32], aInvM: &mut [u32])
{
    let uu____0: &bignum::bignum::bn_mont_ctx_u32 = &k[0usize];
    let len1: u32 = uu____0.len;
    let mut n2: Box<[u32]> = vec![0u32; len1 as usize].into_boxed_slice();
    let c0: u32 =
        lib::inttypes_intrinsics::sub_borrow_u32(
            0u32,
            (&uu____0.n)[0usize],
            2u32,
            &mut (&mut n2)[0usize..]
        );
    let c: u32 =
        if 1u32 < len1
        {
            let a1: &[u32] = &(&uu____0.n)[1usize..];
            let res1: (&mut [u32], &mut [u32]) = n2.split_at_mut(1usize);
            let mut c: [u32; 1] = [c0; 1usize];
            for i in 0u32..len1.wrapping_sub(1u32).wrapping_div(4u32)
            {
                let t1: u32 = a1[4u32.wrapping_mul(i) as usize];
                let res_i: (&mut [u32], &mut [u32]) =
                    res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                (&mut c)[0usize] =
                    lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1);
                let t10: u32 = a1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t10, 0u32, res_i0.1);
                let t11: u32 = a1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t11, 0u32, res_i1.1);
                let t12: u32 = a1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t12, 0u32, res_i2.1)
            };
            for
            i
            in
            len1.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..len1.wrapping_sub(1u32)
            {
                let t1: u32 = a1[i as usize];
                let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(i as usize);
                (&mut c)[0usize] =
                    lib::inttypes_intrinsics::sub_borrow_u32((&c)[0usize], t1, 0u32, res_i.1)
            };
            let c1: u32 = (&c)[0usize];
            c1
        }
        else
        { c0 };
    lowstar::ignore::ignore::<u32>(c);
    crate::genericfield32::exp_vartime(k, aM, uu____0.len.wrapping_mul(32u32), &n2, aInvM)
}
