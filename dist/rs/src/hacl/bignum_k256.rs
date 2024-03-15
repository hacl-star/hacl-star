#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] pub fn is_felem_zero_vartime(f: &mut [u64]) -> bool
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    f0 == 0u64 && f1 == 0u64 && f2 == 0u64 && f3 == 0u64 && f4 == 0u64
}

#[inline] pub fn is_felem_eq_vartime(f1: &mut [u64], f2: &mut [u64]) -> bool
{
    let a0: u64 = f1[0usize];
    let a1: u64 = f1[1usize];
    let a2: u64 = f1[2usize];
    let a3: u64 = f1[3usize];
    let a4: u64 = f1[4usize];
    let b0: u64 = f2[0usize];
    let b1: u64 = f2[1usize];
    let b2: u64 = f2[2usize];
    let b3: u64 = f2[3usize];
    let b4: u64 = f2[4usize];
    a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4
}

#[inline] pub fn is_felem_lt_prime_minus_order_vartime(f: &mut [u64]) -> bool
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    if f4 > 0u64
    { false }
    else
    if f3 > 0u64
    { false }
    else
    if f2 < 0x1455123u64
    { true }
    else
    if f2 > 0x1455123u64
    { false }
    else
    if f1 < 0x1950b75fc4402u64
    { true }
    else
    if f1 > 0x1950b75fc4402u64 { false } else { f0 < 0xda1722fc9baeeu64 }
}

#[inline] pub fn load_felem(f: &mut [u64], b: &mut [u8]) -> ()
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = b.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_be(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let s0: u64 = (&mut tmp)[3usize];
    let s1: u64 = (&mut tmp)[2usize];
    let s2: u64 = (&mut tmp)[1usize];
    let s3: u64 = (&mut tmp)[0usize];
    let f0: u64 = s0 & 0xfffffffffffffu64;
    let f1: u64 = s0.wrapping_shr(52u32) | (s1 & 0xffffffffffu64).wrapping_shl(12u32);
    let f2: u64 = s1.wrapping_shr(40u32) | (s2 & 0xfffffffu64).wrapping_shl(24u32);
    let f3: u64 = s2.wrapping_shr(28u32) | (s3 & 0xffffu64).wrapping_shl(36u32);
    let f4: u64 = s3.wrapping_shr(16u32);
    let f00: u64 = f0;
    let f10: u64 = f1;
    let f20: u64 = f2;
    let f30: u64 = f3;
    let f40: u64 = f4;
    f[0usize] = f00;
    f[1usize] = f10;
    f[2usize] = f20;
    f[3usize] = f30;
    f[4usize] = f40
}

#[inline] pub fn load_felem_lt_prime_vartime(f: &mut [u64], b: &mut [u8]) -> bool
{
    load_felem(f, b);
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let is_ge_p: bool =
        f0 >= 0xffffefffffc2fu64 && f1 == 0xfffffffffffffu64 && f2 == 0xfffffffffffffu64
        &&
        f3 == 0xfffffffffffffu64
        &&
        f4 == 0xffffffffffffu64;
    ! is_ge_p
}

#[inline] pub fn store_felem(b: &mut [u8], f: &mut [u64]) -> ()
{
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let o0: u64 = f0 | f1.wrapping_shl(52u32);
    let o1: u64 = f1.wrapping_shr(12u32) | f2.wrapping_shl(40u32);
    let o2: u64 = f2.wrapping_shr(24u32) | f3.wrapping_shl(28u32);
    let o3: u64 = f3.wrapping_shr(36u32) | f4.wrapping_shl(16u32);
    let f00: u64 = o0;
    let f10: u64 = o1;
    let f20: u64 = o2;
    let f30: u64 = o3;
    (&mut tmp)[0usize] = f30;
    (&mut tmp)[1usize] = f20;
    (&mut tmp)[2usize] = f10;
    (&mut tmp)[3usize] = f00;
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store64_be(
            &mut b[i.wrapping_mul(8u32) as usize..],
            (&mut tmp)[i as usize]
        )
    }
}

#[inline] pub fn fmul_small_num(out: &mut [u64], f: &mut [u64], num: u64) -> ()
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let o0: u64 = f0.wrapping_mul(num);
    let o1: u64 = f1.wrapping_mul(num);
    let o2: u64 = f2.wrapping_mul(num);
    let o3: u64 = f3.wrapping_mul(num);
    let o4: u64 = f4.wrapping_mul(num);
    let f00: u64 = o0;
    let f10: u64 = o1;
    let f20: u64 = o2;
    let f30: u64 = o3;
    let f40: u64 = o4;
    out[0usize] = f00;
    out[1usize] = f10;
    out[2usize] = f20;
    out[3usize] = f30;
    out[4usize] = f40
}

#[inline] pub fn fadd(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    let a0: u64 = f1[0usize];
    let a1: u64 = f1[1usize];
    let a2: u64 = f1[2usize];
    let a3: u64 = f1[3usize];
    let a4: u64 = f1[4usize];
    let b0: u64 = f2[0usize];
    let b1: u64 = f2[1usize];
    let b2: u64 = f2[2usize];
    let b3: u64 = f2[3usize];
    let b4: u64 = f2[4usize];
    let o0: u64 = a0.wrapping_add(b0);
    let o1: u64 = a1.wrapping_add(b1);
    let o2: u64 = a2.wrapping_add(b2);
    let o3: u64 = a3.wrapping_add(b3);
    let o4: u64 = a4.wrapping_add(b4);
    let f0: u64 = o0;
    let f11: u64 = o1;
    let f21: u64 = o2;
    let f3: u64 = o3;
    let f4: u64 = o4;
    out[0usize] = f0;
    out[1usize] = f11;
    out[2usize] = f21;
    out[3usize] = f3;
    out[4usize] = f4
}

#[inline] pub fn fsub(out: &mut [u64], f1: &mut [u64], f2: &mut [u64], x: u64) -> ()
{
    let a0: u64 = f1[0usize];
    let a1: u64 = f1[1usize];
    let a2: u64 = f1[2usize];
    let a3: u64 = f1[3usize];
    let a4: u64 = f1[4usize];
    let b0: u64 = f2[0usize];
    let b1: u64 = f2[1usize];
    let b2: u64 = f2[2usize];
    let b3: u64 = f2[3usize];
    let b4: u64 = f2[4usize];
    let r0: u64 = 9007190664804446u64.wrapping_mul(x).wrapping_sub(b0);
    let r1: u64 = 9007199254740990u64.wrapping_mul(x).wrapping_sub(b1);
    let r2: u64 = 9007199254740990u64.wrapping_mul(x).wrapping_sub(b2);
    let r3: u64 = 9007199254740990u64.wrapping_mul(x).wrapping_sub(b3);
    let r4: u64 = 562949953421310u64.wrapping_mul(x).wrapping_sub(b4);
    let r00: u64 = r0;
    let r10: u64 = r1;
    let r20: u64 = r2;
    let r30: u64 = r3;
    let r40: u64 = r4;
    let o0: u64 = a0.wrapping_add(r00);
    let o1: u64 = a1.wrapping_add(r10);
    let o2: u64 = a2.wrapping_add(r20);
    let o3: u64 = a3.wrapping_add(r30);
    let o4: u64 = a4.wrapping_add(r40);
    let f0: u64 = o0;
    let f11: u64 = o1;
    let f21: u64 = o2;
    let f3: u64 = o3;
    let f4: u64 = o4;
    out[0usize] = f0;
    out[1usize] = f11;
    out[2usize] = f21;
    out[3usize] = f3;
    out[4usize] = f4
}

#[inline] pub fn fmul(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    let a0: u64 = f1[0usize];
    let a1: u64 = f1[1usize];
    let a2: u64 = f1[2usize];
    let a3: u64 = f1[3usize];
    let a4: u64 = f1[4usize];
    let b0: u64 = f2[0usize];
    let b1: u64 = f2[1usize];
    let b2: u64 = f2[2usize];
    let b3: u64 = f2[3usize];
    let b4: u64 = f2[4usize];
    let r: u64 = 0x1000003D10u64;
    let d0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::mul_wide(a0, b3),
                    crate::fstar::uint128::mul_wide(a1, b2)
                ),
                crate::fstar::uint128::mul_wide(a2, b1)
            ),
            crate::fstar::uint128::mul_wide(a3, b0)
        );
    let c0: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(a4, b4);
    let d1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            d0,
            crate::fstar::uint128::mul_wide(r, crate::fstar::uint128::uint128_to_uint64(c0))
        );
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(c0, 64u32));
    let t3: u64 = crate::fstar::uint128::uint128_to_uint64(d1) & 0xfffffffffffffu64;
    let d2: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d1, 52u32);
    let d3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::add_mod(
                        crate::fstar::uint128::add_mod(d2, crate::fstar::uint128::mul_wide(a0, b4)),
                        crate::fstar::uint128::mul_wide(a1, b3)
                    ),
                    crate::fstar::uint128::mul_wide(a2, b2)
                ),
                crate::fstar::uint128::mul_wide(a3, b1)
            ),
            crate::fstar::uint128::mul_wide(a4, b0)
        );
    let d4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            d3,
            crate::fstar::uint128::mul_wide(r.wrapping_shl(12u32), c1)
        );
    let t4: u64 = crate::fstar::uint128::uint128_to_uint64(d4) & 0xfffffffffffffu64;
    let d5: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d4, 52u32);
    let tx: u64 = t4.wrapping_shr(48u32);
    let t4·: u64 = t4 & 0xffffffffffffu64;
    let c2: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(a0, b0);
    let d6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(
                    crate::fstar::uint128::add_mod(d5, crate::fstar::uint128::mul_wide(a1, b4)),
                    crate::fstar::uint128::mul_wide(a2, b3)
                ),
                crate::fstar::uint128::mul_wide(a3, b2)
            ),
            crate::fstar::uint128::mul_wide(a4, b1)
        );
    let u0: u64 = crate::fstar::uint128::uint128_to_uint64(d6) & 0xfffffffffffffu64;
    let d7: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d6, 52u32);
    let u0·: u64 = tx | u0.wrapping_shl(4u32);
    let c3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c2,
            crate::fstar::uint128::mul_wide(u0·, r.wrapping_shr(4u32))
        );
    let r0: u64 = crate::fstar::uint128::uint128_to_uint64(c3) & 0xfffffffffffffu64;
    let c4: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c3, 52u32);
    let c5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(c4, crate::fstar::uint128::mul_wide(a0, b1)),
            crate::fstar::uint128::mul_wide(a1, b0)
        );
    let d8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(d7, crate::fstar::uint128::mul_wide(a2, b4)),
                crate::fstar::uint128::mul_wide(a3, b3)
            ),
            crate::fstar::uint128::mul_wide(a4, b2)
        );
    let c6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c5,
            crate::fstar::uint128::mul_wide(
                crate::fstar::uint128::uint128_to_uint64(d8) & 0xfffffffffffffu64,
                r
            )
        );
    let d9: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d8, 52u32);
    let r1: u64 = crate::fstar::uint128::uint128_to_uint64(c6) & 0xfffffffffffffu64;
    let c7: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c6, 52u32);
    let c8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(c7, crate::fstar::uint128::mul_wide(a0, b2)),
                crate::fstar::uint128::mul_wide(a1, b1)
            ),
            crate::fstar::uint128::mul_wide(a2, b0)
        );
    let d10: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(d9, crate::fstar::uint128::mul_wide(a3, b4)),
            crate::fstar::uint128::mul_wide(a4, b3)
        );
    let c9: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c8,
            crate::fstar::uint128::mul_wide(r, crate::fstar::uint128::uint128_to_uint64(d10))
        );
    let d11: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(d10, 64u32));
    let r2: u64 = crate::fstar::uint128::uint128_to_uint64(c9) & 0xfffffffffffffu64;
    let c10: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c9, 52u32);
    let c11: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                c10,
                crate::fstar::uint128::mul_wide(r.wrapping_shl(12u32), d11)
            ),
            crate::fstar::uint128::uint64_to_uint128(t3)
        );
    let r3: u64 = crate::fstar::uint128::uint128_to_uint64(c11) & 0xfffffffffffffu64;
    let c12: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(c11, 52u32));
    let r4: u64 = c12.wrapping_add(t4·);
    let f0: u64 = r0;
    let f11: u64 = r1;
    let f21: u64 = r2;
    let f3: u64 = r3;
    let f4: u64 = r4;
    out[0usize] = f0;
    out[1usize] = f11;
    out[2usize] = f21;
    out[3usize] = f3;
    out[4usize] = f4
}

#[inline] pub fn fsqr(out: &mut [u64], f: &mut [u64]) -> ()
{
    let a0: u64 = f[0usize];
    let a1: u64 = f[1usize];
    let a2: u64 = f[2usize];
    let a3: u64 = f[3usize];
    let a4: u64 = f[4usize];
    let r: u64 = 0x1000003D10u64;
    let d0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::mul_wide(a0.wrapping_mul(2u64), a3),
            crate::fstar::uint128::mul_wide(a1.wrapping_mul(2u64), a2)
        );
    let c0: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(a4, a4);
    let d1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            d0,
            crate::fstar::uint128::mul_wide(r, crate::fstar::uint128::uint128_to_uint64(c0))
        );
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(c0, 64u32));
    let t3: u64 = crate::fstar::uint128::uint128_to_uint64(d1) & 0xfffffffffffffu64;
    let d2: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d1, 52u32);
    let a41: u64 = a4.wrapping_mul(2u64);
    let d3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                crate::fstar::uint128::add_mod(d2, crate::fstar::uint128::mul_wide(a0, a41)),
                crate::fstar::uint128::mul_wide(a1.wrapping_mul(2u64), a3)
            ),
            crate::fstar::uint128::mul_wide(a2, a2)
        );
    let d4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            d3,
            crate::fstar::uint128::mul_wide(r.wrapping_shl(12u32), c1)
        );
    let t4: u64 = crate::fstar::uint128::uint128_to_uint64(d4) & 0xfffffffffffffu64;
    let d5: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d4, 52u32);
    let tx: u64 = t4.wrapping_shr(48u32);
    let t4·: u64 = t4 & 0xffffffffffffu64;
    let c2: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(a0, a0);
    let d6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(d5, crate::fstar::uint128::mul_wide(a1, a41)),
            crate::fstar::uint128::mul_wide(a2.wrapping_mul(2u64), a3)
        );
    let u0: u64 = crate::fstar::uint128::uint128_to_uint64(d6) & 0xfffffffffffffu64;
    let d7: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d6, 52u32);
    let u0·: u64 = tx | u0.wrapping_shl(4u32);
    let c3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c2,
            crate::fstar::uint128::mul_wide(u0·, r.wrapping_shr(4u32))
        );
    let r0: u64 = crate::fstar::uint128::uint128_to_uint64(c3) & 0xfffffffffffffu64;
    let c4: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c3, 52u32);
    let a01: u64 = a0.wrapping_mul(2u64);
    let c5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(c4, crate::fstar::uint128::mul_wide(a01, a1));
    let d8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(d7, crate::fstar::uint128::mul_wide(a2, a41)),
            crate::fstar::uint128::mul_wide(a3, a3)
        );
    let c6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c5,
            crate::fstar::uint128::mul_wide(
                crate::fstar::uint128::uint128_to_uint64(d8) & 0xfffffffffffffu64,
                r
            )
        );
    let d9: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(d8, 52u32);
    let r1: u64 = crate::fstar::uint128::uint128_to_uint64(c6) & 0xfffffffffffffu64;
    let c7: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c6, 52u32);
    let c8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(c7, crate::fstar::uint128::mul_wide(a01, a2)),
            crate::fstar::uint128::mul_wide(a1, a1)
        );
    let d10: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(d9, crate::fstar::uint128::mul_wide(a3, a41));
    let c9: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            c8,
            crate::fstar::uint128::mul_wide(r, crate::fstar::uint128::uint128_to_uint64(d10))
        );
    let d11: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(d10, 64u32));
    let r2: u64 = crate::fstar::uint128::uint128_to_uint64(c9) & 0xfffffffffffffu64;
    let c10: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(c9, 52u32);
    let c11: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(
                c10,
                crate::fstar::uint128::mul_wide(r.wrapping_shl(12u32), d11)
            ),
            crate::fstar::uint128::uint64_to_uint128(t3)
        );
    let r3: u64 = crate::fstar::uint128::uint128_to_uint64(c11) & 0xfffffffffffffu64;
    let c12: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(c11, 52u32));
    let r4: u64 = c12.wrapping_add(t4·);
    let f0: u64 = r0;
    let f1: u64 = r1;
    let f2: u64 = r2;
    let f3: u64 = r3;
    let f4: u64 = r4;
    out[0usize] = f0;
    out[1usize] = f1;
    out[2usize] = f2;
    out[3usize] = f3;
    out[4usize] = f4
}

#[inline] pub fn fnormalize_weak(out: &mut [u64], f: &mut [u64]) -> ()
{
    let t0: u64 = f[0usize];
    let t1: u64 = f[1usize];
    let t2: u64 = f[2usize];
    let t3: u64 = f[3usize];
    let t4: u64 = f[4usize];
    let x: u64 = t4.wrapping_shr(48u32);
    let t41: u64 = t4 & 0xffffffffffffu64;
    let x0: u64 = x;
    let t01: u64 = t0;
    let t11: u64 = t1;
    let t21: u64 = t2;
    let t31: u64 = t3;
    let t410: u64 = t41;
    let t02: u64 = t01.wrapping_add(x0.wrapping_mul(0x1000003D1u64));
    let t12: u64 = t11.wrapping_add(t02.wrapping_shr(52u32));
    let t03: u64 = t02 & 0xfffffffffffffu64;
    let t22: u64 = t21.wrapping_add(t12.wrapping_shr(52u32));
    let t13: u64 = t12 & 0xfffffffffffffu64;
    let t32: u64 = t31.wrapping_add(t22.wrapping_shr(52u32));
    let t23: u64 = t22 & 0xfffffffffffffu64;
    let t42: u64 = t410.wrapping_add(t32.wrapping_shr(52u32));
    let t33: u64 = t32 & 0xfffffffffffffu64;
    let f0: u64 = t03;
    let f1: u64 = t13;
    let f2: u64 = t23;
    let f3: u64 = t33;
    let f4: u64 = t42;
    out[0usize] = f0;
    out[1usize] = f1;
    out[2usize] = f2;
    out[3usize] = f3;
    out[4usize] = f4
}

#[inline] pub fn fnormalize(out: &mut [u64], f: &mut [u64]) -> ()
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let x: u64 = f4.wrapping_shr(48u32);
    let t4: u64 = f4 & 0xffffffffffffu64;
    let x0: u64 = x;
    let t0: u64 = f0;
    let t1: u64 = f1;
    let t2: u64 = f2;
    let t3: u64 = f3;
    let t40: u64 = t4;
    let t01: u64 = t0.wrapping_add(x0.wrapping_mul(0x1000003D1u64));
    let t11: u64 = t1.wrapping_add(t01.wrapping_shr(52u32));
    let t02: u64 = t01 & 0xfffffffffffffu64;
    let t21: u64 = t2.wrapping_add(t11.wrapping_shr(52u32));
    let t12: u64 = t11 & 0xfffffffffffffu64;
    let t31: u64 = t3.wrapping_add(t21.wrapping_shr(52u32));
    let t22: u64 = t21 & 0xfffffffffffffu64;
    let t41: u64 = t40.wrapping_add(t31.wrapping_shr(52u32));
    let t32: u64 = t31 & 0xfffffffffffffu64;
    let t00: u64 = t02;
    let t10: u64 = t12;
    let t20: u64 = t22;
    let t30: u64 = t32;
    let t42: u64 = t41;
    let x1: u64 = t42.wrapping_shr(48u32);
    let t410: u64 = t42 & 0xffffffffffffu64;
    let x2: u64 = x1;
    let r0: u64 = t00;
    let r1: u64 = t10;
    let r2: u64 = t20;
    let r3: u64 = t30;
    let r4: u64 = t410;
    let m4: u64 = crate::fstar::uint64::eq_mask(r4, 0xffffffffffffu64);
    let m3: u64 = crate::fstar::uint64::eq_mask(r3, 0xfffffffffffffu64);
    let m2: u64 = crate::fstar::uint64::eq_mask(r2, 0xfffffffffffffu64);
    let m1: u64 = crate::fstar::uint64::eq_mask(r1, 0xfffffffffffffu64);
    let m0: u64 = crate::fstar::uint64::gte_mask(r0, 0xffffefffffc2fu64);
    let is_ge_p_m: u64 = m0 & m1 & m2 & m3 & m4;
    let m_to_one: u64 = is_ge_p_m & 1u64;
    let x10: u64 = m_to_one | x2;
    let t010: u64 = r0.wrapping_add(x10.wrapping_mul(0x1000003D1u64));
    let t110: u64 = r1.wrapping_add(t010.wrapping_shr(52u32));
    let t020: u64 = t010 & 0xfffffffffffffu64;
    let t210: u64 = r2.wrapping_add(t110.wrapping_shr(52u32));
    let t120: u64 = t110 & 0xfffffffffffffu64;
    let t310: u64 = r3.wrapping_add(t210.wrapping_shr(52u32));
    let t220: u64 = t210 & 0xfffffffffffffu64;
    let t411: u64 = r4.wrapping_add(t310.wrapping_shr(52u32));
    let t320: u64 = t310 & 0xfffffffffffffu64;
    let s0: u64 = t020;
    let s1: u64 = t120;
    let s2: u64 = t220;
    let s3: u64 = t320;
    let s4: u64 = t411;
    let t412: u64 = s4 & 0xffffffffffffu64;
    let k0: u64 = s0;
    let k1: u64 = s1;
    let k2: u64 = s2;
    let k3: u64 = s3;
    let k4: u64 = t412;
    let f00: u64 = k0;
    let f10: u64 = k1;
    let f20: u64 = k2;
    let f30: u64 = k3;
    let f40: u64 = k4;
    out[0usize] = f00;
    out[1usize] = f10;
    out[2usize] = f20;
    out[3usize] = f30;
    out[4usize] = f40
}

#[inline] pub fn fnegate_conditional_vartime(f: &mut [u64], is_negate: bool) -> ()
{
    if is_negate
    {
        let a0: u64 = f[0usize];
        let a1: u64 = f[1usize];
        let a2: u64 = f[2usize];
        let a3: u64 = f[3usize];
        let a4: u64 = f[4usize];
        let r0: u64 = 9007190664804446u64.wrapping_sub(a0);
        let r1: u64 = 9007199254740990u64.wrapping_sub(a1);
        let r2: u64 = 9007199254740990u64.wrapping_sub(a2);
        let r3: u64 = 9007199254740990u64.wrapping_sub(a3);
        let r4: u64 = 562949953421310u64.wrapping_sub(a4);
        let f0: u64 = r0;
        let f1: u64 = r1;
        let f2: u64 = r2;
        let f3: u64 = r3;
        let f4: u64 = r4;
        f[0usize] = f0;
        f[1usize] = f1;
        f[2usize] = f2;
        f[3usize] = f3;
        f[4usize] = f4;
        let mut f_copy: [u64; 5] = [0u64; 5usize];
        ((&mut f_copy)[0usize..5usize]).copy_from_slice(&f[0usize..5usize]);
        fnormalize(f, &mut f_copy)
    }
}

#[inline] pub fn fsquare_times_in_place(out: &mut [u64], b: u32) -> ()
{
    for _i in 0u32..b
    {
        let mut x_copy: [u64; 5] = [0u64; 5usize];
        ((&mut x_copy)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
        fsqr(out, &mut x_copy)
    }
}

#[inline] pub fn fsquare_times(out: &mut [u64], a: &mut [u64], b: u32) -> ()
{
    (out[0usize..5usize]).copy_from_slice(&a[0usize..5usize]);
    for _i in 0u32..b
    {
        let mut x_copy: [u64; 5] = [0u64; 5usize];
        ((&mut x_copy)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
        fsqr(out, &mut x_copy)
    }
}

#[inline] pub fn fexp_223_23(out: &mut [u64], x2: &mut [u64], f: &mut [u64]) -> ()
{
    let mut x3: [u64; 5] = [0u64; 5usize];
    let mut x22: [u64; 5] = [0u64; 5usize];
    let mut x44: [u64; 5] = [0u64; 5usize];
    let mut x88: [u64; 5] = [0u64; 5usize];
    fsquare_times(x2, f, 1u32);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&x2[0usize..5usize]);
    fmul(x2, &mut f1_copy, f);
    fsquare_times(&mut x3, x2, 1u32);
    let mut f1_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&(&mut x3)[0usize..5usize]);
    fmul(&mut x3, &mut f1_copy0, f);
    fsquare_times(out, &mut x3, 3u32);
    let mut f1_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy1)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy1, &mut x3);
    fsquare_times_in_place(out, 3u32);
    let mut f1_copy2: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy2)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy2, &mut x3);
    fsquare_times_in_place(out, 2u32);
    let mut f1_copy3: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy3)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy3, x2);
    fsquare_times(&mut x22, out, 11u32);
    let mut f1_copy4: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy4)[0usize..5usize]).copy_from_slice(&(&mut x22)[0usize..5usize]);
    fmul(&mut x22, &mut f1_copy4, out);
    fsquare_times(&mut x44, &mut x22, 22u32);
    let mut f1_copy5: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy5)[0usize..5usize]).copy_from_slice(&(&mut x44)[0usize..5usize]);
    fmul(&mut x44, &mut f1_copy5, &mut x22);
    fsquare_times(&mut x88, &mut x44, 44u32);
    let mut f1_copy6: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy6)[0usize..5usize]).copy_from_slice(&(&mut x88)[0usize..5usize]);
    fmul(&mut x88, &mut f1_copy6, &mut x44);
    fsquare_times(out, &mut x88, 88u32);
    let mut f1_copy7: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy7)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy7, &mut x88);
    fsquare_times_in_place(out, 44u32);
    let mut f1_copy8: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy8)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy8, &mut x44);
    fsquare_times_in_place(out, 3u32);
    let mut f1_copy9: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy9)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy9, &mut x3);
    fsquare_times_in_place(out, 23u32);
    let mut f1_copy10: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy10)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy10, &mut x22)
}

#[inline] pub fn finv(out: &mut [u64], f: &mut [u64]) -> ()
{
    let mut x2: [u64; 5] = [0u64; 5usize];
    fexp_223_23(out, &mut x2, f);
    fsquare_times_in_place(out, 5u32);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy, f);
    fsquare_times_in_place(out, 3u32);
    let mut f1_copy0: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy0)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy0, &mut x2);
    fsquare_times_in_place(out, 2u32);
    let mut f1_copy1: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy1)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy1, f)
}

#[inline] pub fn fsqrt(out: &mut [u64], f: &mut [u64]) -> ()
{
    let mut x2: [u64; 5] = [0u64; 5usize];
    fexp_223_23(out, &mut x2, f);
    fsquare_times_in_place(out, 6u32);
    let mut f1_copy: [u64; 5] = [0u64; 5usize];
    ((&mut f1_copy)[0usize..5usize]).copy_from_slice(&out[0usize..5usize]);
    fmul(out, &mut f1_copy, &mut x2);
    fsquare_times_in_place(out, 2u32)
}
