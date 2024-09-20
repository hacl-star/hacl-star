#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn poly1305_padded_256(
    ctx: &mut [lib::intvector_intrinsics::vec256],
    len: u32,
    text: &[u8]
)
{
    let n: u32 = len.wrapping_div(16u32);
    let r: u32 = len.wrapping_rem(16u32);
    let blocks: (&[u8], &[u8]) = text.split_at(0usize);
    let rem: (&[u8], &[u8]) = blocks.1.split_at(n.wrapping_mul(16u32) as usize);
    let pre: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256]) =
        ctx.split_at_mut(5usize);
    let acc: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256]) =
        pre.0.split_at_mut(0usize);
    let sz_block: u32 = 64u32;
    let len0: u32 = n.wrapping_mul(16u32).wrapping_div(sz_block).wrapping_mul(sz_block);
    let t0: (&[u8], &[u8]) = rem.0.split_at(0usize);
    if len0 > 0u32
    {
        let bs: u32 = 64u32;
        let text0: (&[u8], &[u8]) = t0.1.split_at(0usize);
        crate::mac_poly1305_simd256::load_acc4(acc.1, text0.1);
        let len1: u32 = len0.wrapping_sub(bs);
        let text1: (&[u8], &[u8]) = text0.1.split_at(bs as usize);
        let nb: u32 = len1.wrapping_div(bs);
        for i in 0u32..nb
        {
            let block: (&[u8], &[u8]) = text1.1.split_at(i.wrapping_mul(bs) as usize);
            let mut e: [lib::intvector_intrinsics::vec256; 5] =
                [lib::intvector_intrinsics::vec256_zero; 5usize];
            let lo: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_load64_le(&block.1[0usize..]);
            let hi: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_load64_le(&block.1[32usize..]);
            let mask26: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
            let m0: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_interleave_low128(lo, hi);
            let m1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_interleave_high128(lo, hi);
            let m2: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right(m0, 48u32);
            let m3: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right(m1, 48u32);
            let m4: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_interleave_high64(m0, m1);
            let t01: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_interleave_low64(m0, m1);
            let t3: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_interleave_low64(m2, m3);
            let t2: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(t3, 4u32);
            let o2: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t2, mask26);
            let t1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
            let o1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t1, mask26);
            let o5: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t01, mask26);
            let t31: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(t3, 30u32);
            let o3: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t31, mask26);
            let o4: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(m4, 40u32);
            let o0: lib::intvector_intrinsics::vec256 = o5;
            let o10: lib::intvector_intrinsics::vec256 = o1;
            let o20: lib::intvector_intrinsics::vec256 = o2;
            let o30: lib::intvector_intrinsics::vec256 = o3;
            let o40: lib::intvector_intrinsics::vec256 = o4;
            (&mut e)[0usize] = o0;
            (&mut e)[1usize] = o10;
            (&mut e)[2usize] = o20;
            (&mut e)[3usize] = o30;
            (&mut e)[4usize] = o40;
            let b: u64 = 0x1000000u64;
            let mask: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_load64(b);
            let f4: lib::intvector_intrinsics::vec256 = (&e)[4usize];
            (&mut e)[4usize] = lib::intvector_intrinsics::vec256_or(f4, mask);
            let rn: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
                pre.1.split_at(10usize);
            let rn5: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
                rn.1.split_at(5usize);
            let r0: lib::intvector_intrinsics::vec256 = rn5.0[0usize];
            let r1: lib::intvector_intrinsics::vec256 = rn5.0[1usize];
            let r2: lib::intvector_intrinsics::vec256 = rn5.0[2usize];
            let r3: lib::intvector_intrinsics::vec256 = rn5.0[3usize];
            let r4: lib::intvector_intrinsics::vec256 = rn5.0[4usize];
            let r51: lib::intvector_intrinsics::vec256 = rn5.1[1usize];
            let r52: lib::intvector_intrinsics::vec256 = rn5.1[2usize];
            let r53: lib::intvector_intrinsics::vec256 = rn5.1[3usize];
            let r54: lib::intvector_intrinsics::vec256 = rn5.1[4usize];
            let f10: lib::intvector_intrinsics::vec256 = acc.1[0usize];
            let f11: lib::intvector_intrinsics::vec256 = acc.1[1usize];
            let f12: lib::intvector_intrinsics::vec256 = acc.1[2usize];
            let f13: lib::intvector_intrinsics::vec256 = acc.1[3usize];
            let f14: lib::intvector_intrinsics::vec256 = acc.1[4usize];
            let a0: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_mul64(r0, f10);
            let a1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_mul64(r1, f10);
            let a2: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_mul64(r2, f10);
            let a3: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_mul64(r3, f10);
            let a4: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_mul64(r4, f10);
            let a01: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a0,
                    lib::intvector_intrinsics::vec256_mul64(r54, f11)
                );
            let a11: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a1,
                    lib::intvector_intrinsics::vec256_mul64(r0, f11)
                );
            let a21: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a2,
                    lib::intvector_intrinsics::vec256_mul64(r1, f11)
                );
            let a31: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a3,
                    lib::intvector_intrinsics::vec256_mul64(r2, f11)
                );
            let a41: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a4,
                    lib::intvector_intrinsics::vec256_mul64(r3, f11)
                );
            let a02: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a01,
                    lib::intvector_intrinsics::vec256_mul64(r53, f12)
                );
            let a12: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a11,
                    lib::intvector_intrinsics::vec256_mul64(r54, f12)
                );
            let a22: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a21,
                    lib::intvector_intrinsics::vec256_mul64(r0, f12)
                );
            let a32: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a31,
                    lib::intvector_intrinsics::vec256_mul64(r1, f12)
                );
            let a42: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a41,
                    lib::intvector_intrinsics::vec256_mul64(r2, f12)
                );
            let a03: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a02,
                    lib::intvector_intrinsics::vec256_mul64(r52, f13)
                );
            let a13: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a12,
                    lib::intvector_intrinsics::vec256_mul64(r53, f13)
                );
            let a23: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a22,
                    lib::intvector_intrinsics::vec256_mul64(r54, f13)
                );
            let a33: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a32,
                    lib::intvector_intrinsics::vec256_mul64(r0, f13)
                );
            let a43: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a42,
                    lib::intvector_intrinsics::vec256_mul64(r1, f13)
                );
            let a04: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a03,
                    lib::intvector_intrinsics::vec256_mul64(r51, f14)
                );
            let a14: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a13,
                    lib::intvector_intrinsics::vec256_mul64(r52, f14)
                );
            let a24: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a23,
                    lib::intvector_intrinsics::vec256_mul64(r53, f14)
                );
            let a34: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a33,
                    lib::intvector_intrinsics::vec256_mul64(r54, f14)
                );
            let a44: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(
                    a43,
                    lib::intvector_intrinsics::vec256_mul64(r0, f14)
                );
            let t010: lib::intvector_intrinsics::vec256 = a04;
            let t10: lib::intvector_intrinsics::vec256 = a14;
            let t20: lib::intvector_intrinsics::vec256 = a24;
            let t30: lib::intvector_intrinsics::vec256 = a34;
            let t4: lib::intvector_intrinsics::vec256 = a44;
            let mask260: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
            let z0: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(t010, 26u32);
            let z1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(t30, 26u32);
            let x0: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t010, mask260);
            let x3: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(t30, mask260);
            let x1: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(t10, z0);
            let x4: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(t4, z1);
            let z01: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
            let z11: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
            let t: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
            let z12: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(z11, t);
            let x11: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(x1, mask260);
            let x41: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(x4, mask260);
            let x2: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(t20, z01);
            let x01: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(x0, z12);
            let z02: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
            let z13: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
            let x21: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(x2, mask260);
            let x02: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(x01, mask260);
            let x31: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(x3, z02);
            let x12: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(x11, z13);
            let z03: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
            let x32: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_and(x31, mask260);
            let x42: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(x41, z03);
            let o00: lib::intvector_intrinsics::vec256 = x02;
            let o11: lib::intvector_intrinsics::vec256 = x12;
            let o21: lib::intvector_intrinsics::vec256 = x21;
            let o31: lib::intvector_intrinsics::vec256 = x32;
            let o41: lib::intvector_intrinsics::vec256 = x42;
            acc.1[0usize] = o00;
            acc.1[1usize] = o11;
            acc.1[2usize] = o21;
            acc.1[3usize] = o31;
            acc.1[4usize] = o41;
            let f100: lib::intvector_intrinsics::vec256 = acc.1[0usize];
            let f110: lib::intvector_intrinsics::vec256 = acc.1[1usize];
            let f120: lib::intvector_intrinsics::vec256 = acc.1[2usize];
            let f130: lib::intvector_intrinsics::vec256 = acc.1[3usize];
            let f140: lib::intvector_intrinsics::vec256 = acc.1[4usize];
            let f20: lib::intvector_intrinsics::vec256 = (&e)[0usize];
            let f21: lib::intvector_intrinsics::vec256 = (&e)[1usize];
            let f22: lib::intvector_intrinsics::vec256 = (&e)[2usize];
            let f23: lib::intvector_intrinsics::vec256 = (&e)[3usize];
            let f24: lib::intvector_intrinsics::vec256 = (&e)[4usize];
            let o01: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(f100, f20);
            let o12: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(f110, f21);
            let o22: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(f120, f22);
            let o32: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(f130, f23);
            let o42: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(f140, f24);
            acc.1[0usize] = o01;
            acc.1[1usize] = o12;
            acc.1[2usize] = o22;
            acc.1[3usize] = o32;
            acc.1[4usize] = o42
        };
        crate::mac_poly1305_simd256::fmul_r4_normalize(acc.1, pre.1)
    };
    let len1: u32 = n.wrapping_mul(16u32).wrapping_sub(len0);
    let t1: (&[u8], &[u8]) = t0.1.split_at(len0 as usize);
    let nb: u32 = len1.wrapping_div(16u32);
    let rem1: u32 = len1.wrapping_rem(16u32);
    for i in 0u32..nb
    {
        let block: (&[u8], &[u8]) = t1.1.split_at(i.wrapping_mul(16u32) as usize);
        let mut e: [lib::intvector_intrinsics::vec256; 5] =
            [lib::intvector_intrinsics::vec256_zero; 5usize];
        let u: u64 = lowstar::endianness::load64_le(&block.1[0usize..]);
        let lo: u64 = u;
        let u0: u64 = lowstar::endianness::load64_le(&block.1[8usize..]);
        let hi: u64 = u0;
        let f0: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(lo);
        let f1: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
        let f01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                f0,
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_or(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
                lib::intvector_intrinsics::vec256_shift_left64(
                    lib::intvector_intrinsics::vec256_and(
                        f1,
                        lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
        let f010: lib::intvector_intrinsics::vec256 = f01;
        let f110: lib::intvector_intrinsics::vec256 = f11;
        let f20: lib::intvector_intrinsics::vec256 = f2;
        let f30: lib::intvector_intrinsics::vec256 = f3;
        let f40: lib::intvector_intrinsics::vec256 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 0x1000000u64;
        let mask: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(b);
        let f41: lib::intvector_intrinsics::vec256 = (&e)[4usize];
        (&mut e)[4usize] = lib::intvector_intrinsics::vec256_or(f41, mask);
        let r1: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            pre.1.split_at(0usize);
        let r5: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            r1.1.split_at(5usize);
        let r0: lib::intvector_intrinsics::vec256 = r5.0[0usize];
        let r11: lib::intvector_intrinsics::vec256 = r5.0[1usize];
        let r2: lib::intvector_intrinsics::vec256 = r5.0[2usize];
        let r3: lib::intvector_intrinsics::vec256 = r5.0[3usize];
        let r4: lib::intvector_intrinsics::vec256 = r5.0[4usize];
        let r51: lib::intvector_intrinsics::vec256 = r5.1[1usize];
        let r52: lib::intvector_intrinsics::vec256 = r5.1[2usize];
        let r53: lib::intvector_intrinsics::vec256 = r5.1[3usize];
        let r54: lib::intvector_intrinsics::vec256 = r5.1[4usize];
        let f10: lib::intvector_intrinsics::vec256 = (&e)[0usize];
        let f111: lib::intvector_intrinsics::vec256 = (&e)[1usize];
        let f12: lib::intvector_intrinsics::vec256 = (&e)[2usize];
        let f13: lib::intvector_intrinsics::vec256 = (&e)[3usize];
        let f14: lib::intvector_intrinsics::vec256 = (&e)[4usize];
        let a0: lib::intvector_intrinsics::vec256 = acc.1[0usize];
        let a1: lib::intvector_intrinsics::vec256 = acc.1[1usize];
        let a2: lib::intvector_intrinsics::vec256 = acc.1[2usize];
        let a3: lib::intvector_intrinsics::vec256 = acc.1[3usize];
        let a4: lib::intvector_intrinsics::vec256 = acc.1[4usize];
        let a01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a0, f10);
        let a11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a1, f111);
        let a21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a2, f12);
        let a31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a3, f13);
        let a41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a4, f14);
        let a02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r0, a01);
        let a12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r11, a01);
        let a22: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r2, a01);
        let a32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r3, a01);
        let a42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r4, a01);
        let a03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a02,
                lib::intvector_intrinsics::vec256_mul64(r54, a11)
            );
        let a13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a12,
                lib::intvector_intrinsics::vec256_mul64(r0, a11)
            );
        let a23: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a22,
                lib::intvector_intrinsics::vec256_mul64(r11, a11)
            );
        let a33: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a32,
                lib::intvector_intrinsics::vec256_mul64(r2, a11)
            );
        let a43: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a42,
                lib::intvector_intrinsics::vec256_mul64(r3, a11)
            );
        let a04: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a03,
                lib::intvector_intrinsics::vec256_mul64(r53, a21)
            );
        let a14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a13,
                lib::intvector_intrinsics::vec256_mul64(r54, a21)
            );
        let a24: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a23,
                lib::intvector_intrinsics::vec256_mul64(r0, a21)
            );
        let a34: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a33,
                lib::intvector_intrinsics::vec256_mul64(r11, a21)
            );
        let a44: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a43,
                lib::intvector_intrinsics::vec256_mul64(r2, a21)
            );
        let a05: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a04,
                lib::intvector_intrinsics::vec256_mul64(r52, a31)
            );
        let a15: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a14,
                lib::intvector_intrinsics::vec256_mul64(r53, a31)
            );
        let a25: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a24,
                lib::intvector_intrinsics::vec256_mul64(r54, a31)
            );
        let a35: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a34,
                lib::intvector_intrinsics::vec256_mul64(r0, a31)
            );
        let a45: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a44,
                lib::intvector_intrinsics::vec256_mul64(r11, a31)
            );
        let a06: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a05,
                lib::intvector_intrinsics::vec256_mul64(r51, a41)
            );
        let a16: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a15,
                lib::intvector_intrinsics::vec256_mul64(r52, a41)
            );
        let a26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a25,
                lib::intvector_intrinsics::vec256_mul64(r53, a41)
            );
        let a36: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a35,
                lib::intvector_intrinsics::vec256_mul64(r54, a41)
            );
        let a46: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a45,
                lib::intvector_intrinsics::vec256_mul64(r0, a41)
            );
        let t01: lib::intvector_intrinsics::vec256 = a06;
        let t11: lib::intvector_intrinsics::vec256 = a16;
        let t2: lib::intvector_intrinsics::vec256 = a26;
        let t3: lib::intvector_intrinsics::vec256 = a36;
        let t4: lib::intvector_intrinsics::vec256 = a46;
        let mask26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
        let z0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
        let z1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
        let x0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t01, mask26);
        let x3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t3, mask26);
        let x1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t11, z0);
        let x4: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t4, z1);
        let z01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
        let z11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
        let t: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
        let z12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(z11, t);
        let x11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x1, mask26);
        let x41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x4, mask26);
        let x2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t2, z01);
        let x01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x0, z12);
        let z02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
        let z13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
        let x21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x2, mask26);
        let x02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x01, mask26);
        let x31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x3, z02);
        let x12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x11, z13);
        let z03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
        let x32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x31, mask26);
        let x42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x41, z03);
        let o0: lib::intvector_intrinsics::vec256 = x02;
        let o1: lib::intvector_intrinsics::vec256 = x12;
        let o2: lib::intvector_intrinsics::vec256 = x21;
        let o3: lib::intvector_intrinsics::vec256 = x32;
        let o4: lib::intvector_intrinsics::vec256 = x42;
        acc.1[0usize] = o0;
        acc.1[1usize] = o1;
        acc.1[2usize] = o2;
        acc.1[3usize] = o3;
        acc.1[4usize] = o4
    };
    if rem1 > 0u32
    {
        let last: (&[u8], &[u8]) = t1.1.split_at(nb.wrapping_mul(16u32) as usize);
        let mut e: [lib::intvector_intrinsics::vec256; 5] =
            [lib::intvector_intrinsics::vec256_zero; 5usize];
        let mut tmp: [u8; 16] = [0u8; 16usize];
        ((&mut tmp)[0usize..rem1 as usize]).copy_from_slice(&last.1[0usize..rem1 as usize]);
        let u: u64 = lowstar::endianness::load64_le(&(&tmp)[0usize..]);
        let lo: u64 = u;
        let u0: u64 = lowstar::endianness::load64_le(&(&tmp)[8usize..]);
        let hi: u64 = u0;
        let f0: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(lo);
        let f1: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
        let f01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                f0,
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_or(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
                lib::intvector_intrinsics::vec256_shift_left64(
                    lib::intvector_intrinsics::vec256_and(
                        f1,
                        lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
        let f010: lib::intvector_intrinsics::vec256 = f01;
        let f110: lib::intvector_intrinsics::vec256 = f11;
        let f20: lib::intvector_intrinsics::vec256 = f2;
        let f30: lib::intvector_intrinsics::vec256 = f3;
        let f40: lib::intvector_intrinsics::vec256 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 1u64.wrapping_shl(rem1.wrapping_mul(8u32).wrapping_rem(26u32));
        let mask: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(b);
        let fi: lib::intvector_intrinsics::vec256 =
            (&e)[rem1.wrapping_mul(8u32).wrapping_div(26u32) as usize];
        (&mut e)[rem1.wrapping_mul(8u32).wrapping_div(26u32) as usize] =
            lib::intvector_intrinsics::vec256_or(fi, mask);
        let r1: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            pre.1.split_at(0usize);
        let r5: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            r1.1.split_at(5usize);
        let r0: lib::intvector_intrinsics::vec256 = r5.0[0usize];
        let r11: lib::intvector_intrinsics::vec256 = r5.0[1usize];
        let r2: lib::intvector_intrinsics::vec256 = r5.0[2usize];
        let r3: lib::intvector_intrinsics::vec256 = r5.0[3usize];
        let r4: lib::intvector_intrinsics::vec256 = r5.0[4usize];
        let r51: lib::intvector_intrinsics::vec256 = r5.1[1usize];
        let r52: lib::intvector_intrinsics::vec256 = r5.1[2usize];
        let r53: lib::intvector_intrinsics::vec256 = r5.1[3usize];
        let r54: lib::intvector_intrinsics::vec256 = r5.1[4usize];
        let f10: lib::intvector_intrinsics::vec256 = (&e)[0usize];
        let f111: lib::intvector_intrinsics::vec256 = (&e)[1usize];
        let f12: lib::intvector_intrinsics::vec256 = (&e)[2usize];
        let f13: lib::intvector_intrinsics::vec256 = (&e)[3usize];
        let f14: lib::intvector_intrinsics::vec256 = (&e)[4usize];
        let a0: lib::intvector_intrinsics::vec256 = acc.1[0usize];
        let a1: lib::intvector_intrinsics::vec256 = acc.1[1usize];
        let a2: lib::intvector_intrinsics::vec256 = acc.1[2usize];
        let a3: lib::intvector_intrinsics::vec256 = acc.1[3usize];
        let a4: lib::intvector_intrinsics::vec256 = acc.1[4usize];
        let a01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a0, f10);
        let a11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a1, f111);
        let a21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a2, f12);
        let a31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a3, f13);
        let a41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a4, f14);
        let a02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r0, a01);
        let a12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r11, a01);
        let a22: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r2, a01);
        let a32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r3, a01);
        let a42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r4, a01);
        let a03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a02,
                lib::intvector_intrinsics::vec256_mul64(r54, a11)
            );
        let a13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a12,
                lib::intvector_intrinsics::vec256_mul64(r0, a11)
            );
        let a23: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a22,
                lib::intvector_intrinsics::vec256_mul64(r11, a11)
            );
        let a33: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a32,
                lib::intvector_intrinsics::vec256_mul64(r2, a11)
            );
        let a43: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a42,
                lib::intvector_intrinsics::vec256_mul64(r3, a11)
            );
        let a04: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a03,
                lib::intvector_intrinsics::vec256_mul64(r53, a21)
            );
        let a14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a13,
                lib::intvector_intrinsics::vec256_mul64(r54, a21)
            );
        let a24: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a23,
                lib::intvector_intrinsics::vec256_mul64(r0, a21)
            );
        let a34: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a33,
                lib::intvector_intrinsics::vec256_mul64(r11, a21)
            );
        let a44: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a43,
                lib::intvector_intrinsics::vec256_mul64(r2, a21)
            );
        let a05: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a04,
                lib::intvector_intrinsics::vec256_mul64(r52, a31)
            );
        let a15: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a14,
                lib::intvector_intrinsics::vec256_mul64(r53, a31)
            );
        let a25: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a24,
                lib::intvector_intrinsics::vec256_mul64(r54, a31)
            );
        let a35: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a34,
                lib::intvector_intrinsics::vec256_mul64(r0, a31)
            );
        let a45: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a44,
                lib::intvector_intrinsics::vec256_mul64(r11, a31)
            );
        let a06: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a05,
                lib::intvector_intrinsics::vec256_mul64(r51, a41)
            );
        let a16: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a15,
                lib::intvector_intrinsics::vec256_mul64(r52, a41)
            );
        let a26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a25,
                lib::intvector_intrinsics::vec256_mul64(r53, a41)
            );
        let a36: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a35,
                lib::intvector_intrinsics::vec256_mul64(r54, a41)
            );
        let a46: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a45,
                lib::intvector_intrinsics::vec256_mul64(r0, a41)
            );
        let t01: lib::intvector_intrinsics::vec256 = a06;
        let t11: lib::intvector_intrinsics::vec256 = a16;
        let t2: lib::intvector_intrinsics::vec256 = a26;
        let t3: lib::intvector_intrinsics::vec256 = a36;
        let t4: lib::intvector_intrinsics::vec256 = a46;
        let mask26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
        let z0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
        let z1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
        let x0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t01, mask26);
        let x3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t3, mask26);
        let x1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t11, z0);
        let x4: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t4, z1);
        let z01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
        let z11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
        let t: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
        let z12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(z11, t);
        let x11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x1, mask26);
        let x41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x4, mask26);
        let x2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t2, z01);
        let x01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x0, z12);
        let z02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
        let z13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
        let x21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x2, mask26);
        let x02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x01, mask26);
        let x31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x3, z02);
        let x12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x11, z13);
        let z03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
        let x32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x31, mask26);
        let x42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x41, z03);
        let o0: lib::intvector_intrinsics::vec256 = x02;
        let o1: lib::intvector_intrinsics::vec256 = x12;
        let o2: lib::intvector_intrinsics::vec256 = x21;
        let o3: lib::intvector_intrinsics::vec256 = x32;
        let o4: lib::intvector_intrinsics::vec256 = x42;
        acc.1[0usize] = o0;
        acc.1[1usize] = o1;
        acc.1[2usize] = o2;
        acc.1[3usize] = o3;
        acc.1[4usize] = o4
    };
    let mut tmp: [u8; 16] = [0u8; 16usize];
    ((&mut tmp)[0usize..r as usize]).copy_from_slice(&rem.1[0usize..r as usize]);
    if r > 0u32
    {
        let pre0: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            pre.1.split_at(0usize);
        let
        acc0: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
        =
            acc.1.split_at_mut(0usize);
        let mut e: [lib::intvector_intrinsics::vec256; 5] =
            [lib::intvector_intrinsics::vec256_zero; 5usize];
        let u: u64 = lowstar::endianness::load64_le(&(&tmp)[0usize..]);
        let lo: u64 = u;
        let u0: u64 = lowstar::endianness::load64_le(&(&tmp)[8usize..]);
        let hi: u64 = u0;
        let f0: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(lo);
        let f1: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
        let f01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                f0,
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_or(
                lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
                lib::intvector_intrinsics::vec256_shift_left64(
                    lib::intvector_intrinsics::vec256_and(
                        f1,
                        lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(
                lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
                lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
        let f010: lib::intvector_intrinsics::vec256 = f01;
        let f110: lib::intvector_intrinsics::vec256 = f11;
        let f20: lib::intvector_intrinsics::vec256 = f2;
        let f30: lib::intvector_intrinsics::vec256 = f3;
        let f40: lib::intvector_intrinsics::vec256 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 0x1000000u64;
        let mask: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(b);
        let f41: lib::intvector_intrinsics::vec256 = (&e)[4usize];
        (&mut e)[4usize] = lib::intvector_intrinsics::vec256_or(f41, mask);
        let r1: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            pre0.1.split_at(0usize);
        let r5: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
            r1.1.split_at(5usize);
        let r0: lib::intvector_intrinsics::vec256 = r5.0[0usize];
        let r11: lib::intvector_intrinsics::vec256 = r5.0[1usize];
        let r2: lib::intvector_intrinsics::vec256 = r5.0[2usize];
        let r3: lib::intvector_intrinsics::vec256 = r5.0[3usize];
        let r4: lib::intvector_intrinsics::vec256 = r5.0[4usize];
        let r51: lib::intvector_intrinsics::vec256 = r5.1[1usize];
        let r52: lib::intvector_intrinsics::vec256 = r5.1[2usize];
        let r53: lib::intvector_intrinsics::vec256 = r5.1[3usize];
        let r54: lib::intvector_intrinsics::vec256 = r5.1[4usize];
        let f10: lib::intvector_intrinsics::vec256 = (&e)[0usize];
        let f111: lib::intvector_intrinsics::vec256 = (&e)[1usize];
        let f12: lib::intvector_intrinsics::vec256 = (&e)[2usize];
        let f13: lib::intvector_intrinsics::vec256 = (&e)[3usize];
        let f14: lib::intvector_intrinsics::vec256 = (&e)[4usize];
        let a0: lib::intvector_intrinsics::vec256 = acc0.1[0usize];
        let a1: lib::intvector_intrinsics::vec256 = acc0.1[1usize];
        let a2: lib::intvector_intrinsics::vec256 = acc0.1[2usize];
        let a3: lib::intvector_intrinsics::vec256 = acc0.1[3usize];
        let a4: lib::intvector_intrinsics::vec256 = acc0.1[4usize];
        let a01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a0, f10);
        let a11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a1, f111);
        let a21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a2, f12);
        let a31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a3, f13);
        let a41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(a4, f14);
        let a02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r0, a01);
        let a12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r11, a01);
        let a22: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r2, a01);
        let a32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r3, a01);
        let a42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_mul64(r4, a01);
        let a03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a02,
                lib::intvector_intrinsics::vec256_mul64(r54, a11)
            );
        let a13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a12,
                lib::intvector_intrinsics::vec256_mul64(r0, a11)
            );
        let a23: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a22,
                lib::intvector_intrinsics::vec256_mul64(r11, a11)
            );
        let a33: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a32,
                lib::intvector_intrinsics::vec256_mul64(r2, a11)
            );
        let a43: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a42,
                lib::intvector_intrinsics::vec256_mul64(r3, a11)
            );
        let a04: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a03,
                lib::intvector_intrinsics::vec256_mul64(r53, a21)
            );
        let a14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a13,
                lib::intvector_intrinsics::vec256_mul64(r54, a21)
            );
        let a24: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a23,
                lib::intvector_intrinsics::vec256_mul64(r0, a21)
            );
        let a34: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a33,
                lib::intvector_intrinsics::vec256_mul64(r11, a21)
            );
        let a44: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a43,
                lib::intvector_intrinsics::vec256_mul64(r2, a21)
            );
        let a05: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a04,
                lib::intvector_intrinsics::vec256_mul64(r52, a31)
            );
        let a15: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a14,
                lib::intvector_intrinsics::vec256_mul64(r53, a31)
            );
        let a25: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a24,
                lib::intvector_intrinsics::vec256_mul64(r54, a31)
            );
        let a35: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a34,
                lib::intvector_intrinsics::vec256_mul64(r0, a31)
            );
        let a45: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a44,
                lib::intvector_intrinsics::vec256_mul64(r11, a31)
            );
        let a06: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a05,
                lib::intvector_intrinsics::vec256_mul64(r51, a41)
            );
        let a16: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a15,
                lib::intvector_intrinsics::vec256_mul64(r52, a41)
            );
        let a26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a25,
                lib::intvector_intrinsics::vec256_mul64(r53, a41)
            );
        let a36: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a35,
                lib::intvector_intrinsics::vec256_mul64(r54, a41)
            );
        let a46: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(
                a45,
                lib::intvector_intrinsics::vec256_mul64(r0, a41)
            );
        let t00: lib::intvector_intrinsics::vec256 = a06;
        let t10: lib::intvector_intrinsics::vec256 = a16;
        let t2: lib::intvector_intrinsics::vec256 = a26;
        let t3: lib::intvector_intrinsics::vec256 = a36;
        let t4: lib::intvector_intrinsics::vec256 = a46;
        let mask26: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
        let z0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t00, 26u32);
        let z1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
        let x0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t00, mask26);
        let x3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(t3, mask26);
        let x1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t10, z0);
        let x4: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t4, z1);
        let z01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
        let z11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
        let t: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
        let z12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(z11, t);
        let x11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x1, mask26);
        let x41: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x4, mask26);
        let x2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(t2, z01);
        let x01: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x0, z12);
        let z02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
        let z13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
        let x21: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x2, mask26);
        let x02: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x01, mask26);
        let x31: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x3, z02);
        let x12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x11, z13);
        let z03: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
        let x32: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_and(x31, mask26);
        let x42: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_add64(x41, z03);
        let o0: lib::intvector_intrinsics::vec256 = x02;
        let o1: lib::intvector_intrinsics::vec256 = x12;
        let o2: lib::intvector_intrinsics::vec256 = x21;
        let o3: lib::intvector_intrinsics::vec256 = x32;
        let o4: lib::intvector_intrinsics::vec256 = x42;
        acc0.1[0usize] = o0;
        acc0.1[1usize] = o1;
        acc0.1[2usize] = o2;
        acc0.1[3usize] = o3;
        acc0.1[4usize] = o4
    }
}

#[inline] fn poly1305_do_256(
    k: &[u8],
    aadlen: u32,
    aad: &[u8],
    mlen: u32,
    m: &[u8],
    out: &mut [u8]
)
{
    let mut ctx: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let mut block: [u8; 16] = [0u8; 16usize];
    crate::mac_poly1305_simd256::poly1305_init(&mut ctx, k);
    if aadlen != 0u32
    { crate::aead_chacha20poly1305_simd256::poly1305_padded_256(&mut ctx, aadlen, aad) };
    if mlen != 0u32
    { crate::aead_chacha20poly1305_simd256::poly1305_padded_256(&mut ctx, mlen, m) };
    lowstar::endianness::store64_le(&mut (&mut block)[0usize..], aadlen as u64);
    lowstar::endianness::store64_le(&mut (&mut block)[8usize..], mlen as u64);
    let pre: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256]) =
        ctx.split_at_mut(5usize);
    let acc: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256]) =
        pre.0.split_at_mut(0usize);
    let mut e: [lib::intvector_intrinsics::vec256; 5] =
        [lib::intvector_intrinsics::vec256_zero; 5usize];
    let u: u64 = lowstar::endianness::load64_le(&(&block)[0usize..]);
    let lo: u64 = u;
    let u0: u64 = lowstar::endianness::load64_le(&(&block)[8usize..]);
    let hi: u64 = u0;
    let f0: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(lo);
    let f1: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
    let f01: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_and(
            f0,
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_and(
            lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_or(
            lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
            lib::intvector_intrinsics::vec256_shift_left64(
                lib::intvector_intrinsics::vec256_and(
                    f1,
                    lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                ),
                12u32
            )
        );
    let f3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_and(
            lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
            lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
    let f010: lib::intvector_intrinsics::vec256 = f01;
    let f110: lib::intvector_intrinsics::vec256 = f11;
    let f20: lib::intvector_intrinsics::vec256 = f2;
    let f30: lib::intvector_intrinsics::vec256 = f3;
    let f40: lib::intvector_intrinsics::vec256 = f4;
    (&mut e)[0usize] = f010;
    (&mut e)[1usize] = f110;
    (&mut e)[2usize] = f20;
    (&mut e)[3usize] = f30;
    (&mut e)[4usize] = f40;
    let b: u64 = 0x1000000u64;
    let mask: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(b);
    let f41: lib::intvector_intrinsics::vec256 = (&e)[4usize];
    (&mut e)[4usize] = lib::intvector_intrinsics::vec256_or(f41, mask);
    let r: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
        pre.1.split_at(0usize);
    let r5: (&[lib::intvector_intrinsics::vec256], &[lib::intvector_intrinsics::vec256]) =
        r.1.split_at(5usize);
    let r0: lib::intvector_intrinsics::vec256 = r5.0[0usize];
    let r1: lib::intvector_intrinsics::vec256 = r5.0[1usize];
    let r2: lib::intvector_intrinsics::vec256 = r5.0[2usize];
    let r3: lib::intvector_intrinsics::vec256 = r5.0[3usize];
    let r4: lib::intvector_intrinsics::vec256 = r5.0[4usize];
    let r51: lib::intvector_intrinsics::vec256 = r5.1[1usize];
    let r52: lib::intvector_intrinsics::vec256 = r5.1[2usize];
    let r53: lib::intvector_intrinsics::vec256 = r5.1[3usize];
    let r54: lib::intvector_intrinsics::vec256 = r5.1[4usize];
    let f10: lib::intvector_intrinsics::vec256 = (&e)[0usize];
    let f111: lib::intvector_intrinsics::vec256 = (&e)[1usize];
    let f12: lib::intvector_intrinsics::vec256 = (&e)[2usize];
    let f13: lib::intvector_intrinsics::vec256 = (&e)[3usize];
    let f14: lib::intvector_intrinsics::vec256 = (&e)[4usize];
    let a0: lib::intvector_intrinsics::vec256 = acc.1[0usize];
    let a1: lib::intvector_intrinsics::vec256 = acc.1[1usize];
    let a2: lib::intvector_intrinsics::vec256 = acc.1[2usize];
    let a3: lib::intvector_intrinsics::vec256 = acc.1[3usize];
    let a4: lib::intvector_intrinsics::vec256 = acc.1[4usize];
    let a01: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(a0, f10);
    let a11: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(a1, f111);
    let a21: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(a2, f12);
    let a31: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(a3, f13);
    let a41: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(a4, f14);
    let a02: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_mul64(r0, a01);
    let a12: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_mul64(r1, a01);
    let a22: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_mul64(r2, a01);
    let a32: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_mul64(r3, a01);
    let a42: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_mul64(r4, a01);
    let a03: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a02,
            lib::intvector_intrinsics::vec256_mul64(r54, a11)
        );
    let a13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a12,
            lib::intvector_intrinsics::vec256_mul64(r0, a11)
        );
    let a23: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a22,
            lib::intvector_intrinsics::vec256_mul64(r1, a11)
        );
    let a33: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a32,
            lib::intvector_intrinsics::vec256_mul64(r2, a11)
        );
    let a43: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a42,
            lib::intvector_intrinsics::vec256_mul64(r3, a11)
        );
    let a04: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a03,
            lib::intvector_intrinsics::vec256_mul64(r53, a21)
        );
    let a14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a13,
            lib::intvector_intrinsics::vec256_mul64(r54, a21)
        );
    let a24: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a23,
            lib::intvector_intrinsics::vec256_mul64(r0, a21)
        );
    let a34: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a33,
            lib::intvector_intrinsics::vec256_mul64(r1, a21)
        );
    let a44: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a43,
            lib::intvector_intrinsics::vec256_mul64(r2, a21)
        );
    let a05: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a04,
            lib::intvector_intrinsics::vec256_mul64(r52, a31)
        );
    let a15: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a14,
            lib::intvector_intrinsics::vec256_mul64(r53, a31)
        );
    let a25: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a24,
            lib::intvector_intrinsics::vec256_mul64(r54, a31)
        );
    let a35: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a34,
            lib::intvector_intrinsics::vec256_mul64(r0, a31)
        );
    let a45: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a44,
            lib::intvector_intrinsics::vec256_mul64(r1, a31)
        );
    let a06: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a05,
            lib::intvector_intrinsics::vec256_mul64(r51, a41)
        );
    let a16: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a15,
            lib::intvector_intrinsics::vec256_mul64(r52, a41)
        );
    let a26: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a25,
            lib::intvector_intrinsics::vec256_mul64(r53, a41)
        );
    let a36: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a35,
            lib::intvector_intrinsics::vec256_mul64(r54, a41)
        );
    let a46: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_add64(
            a45,
            lib::intvector_intrinsics::vec256_mul64(r0, a41)
        );
    let t0: lib::intvector_intrinsics::vec256 = a06;
    let t1: lib::intvector_intrinsics::vec256 = a16;
    let t2: lib::intvector_intrinsics::vec256 = a26;
    let t3: lib::intvector_intrinsics::vec256 = a36;
    let t4: lib::intvector_intrinsics::vec256 = a46;
    let mask26: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(t0, 26u32);
    let z1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_and(t0, mask26);
    let x3: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_and(t3, mask26);
    let x1: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t1, z0);
    let x4: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t4, z1);
    let z01: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
    let t: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(z11, t);
    let x11: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_and(x1, mask26);
    let x41: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_and(x4, mask26);
    let x2: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(t2, z01);
    let x01: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(x0, z12);
    let z02: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_and(x2, mask26);
    let x02: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_and(x01, mask26);
    let x31: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(x3, z02);
    let x12: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(x11, z13);
    let z03: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_and(x31, mask26);
    let x42: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_add64(x41, z03);
    let o0: lib::intvector_intrinsics::vec256 = x02;
    let o1: lib::intvector_intrinsics::vec256 = x12;
    let o2: lib::intvector_intrinsics::vec256 = x21;
    let o3: lib::intvector_intrinsics::vec256 = x32;
    let o4: lib::intvector_intrinsics::vec256 = x42;
    acc.1[0usize] = o0;
    acc.1[1usize] = o1;
    acc.1[2usize] = o2;
    acc.1[3usize] = o3;
    acc.1[4usize] = o4;
    crate::mac_poly1305_simd256::poly1305_finish(out, k, &mut ctx)
}

/**
Encrypt a message `input` with key `key`.

The arguments `key`, `nonce`, `data`, and `data_len` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `input` and `output` can point to the same memory.

@param output Pointer to `input_len` bytes of memory where the ciphertext is written to.
@param tag Pointer to 16 bytes of memory where the mac is written to.
@param input Pointer to `input_len` bytes of memory where the message is read from.
@param input_len Length of the message.
@param data Pointer to `data_len` bytes of memory where the associated data is read from.
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
@param nonce Pointer to 12 bytes of memory where the AEAD nonce is read from.
*/
pub fn
encrypt(
    output: &mut [u8],
    tag: &mut [u8],
    input: &[u8],
    input_len: u32,
    data: &[u8],
    data_len: u32,
    key: &[u8],
    nonce: &[u8]
)
{
    crate::chacha20_vec256::chacha20_encrypt_256(input_len, output, input, key, nonce, 1u32);
    let mut tmp: [u8; 64] = [0u8; 64usize];
    let tmp_copy: [u8; 64] = [0u8; 64usize];
    crate::chacha20_vec256::chacha20_encrypt_256(64u32, &mut tmp, &tmp_copy, key, nonce, 0u32);
    let key1: (&[u8], &[u8]) = tmp.split_at(0usize);
    crate::aead_chacha20poly1305_simd256::poly1305_do_256(
        key1.1,
        data_len,
        data,
        input_len,
        output,
        tag
    )
}

/**
Decrypt a ciphertext `input` with key `key`.

The arguments `key`, `nonce`, `data`, and `data_len` are same in encryption/decryption.
Note: Encryption and decryption can be executed in-place, i.e., `input` and `output` can point to the same memory.

If decryption succeeds, the resulting plaintext is stored in `output` and the function returns the success code 0.
If decryption fails, the array `output` remains unchanged and the function returns the error code 1.

@param output Pointer to `input_len` bytes of memory where the message is written to.
@param input Pointer to `input_len` bytes of memory where the ciphertext is read from.
@param input_len Length of the ciphertext.
@param data Pointer to `data_len` bytes of memory where the associated data is read from.
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
@param nonce Pointer to 12 bytes of memory where the AEAD nonce is read from.
@param tag Pointer to 16 bytes of memory where the mac is read from.

@returns 0 on succeess; 1 on failure.
*/
pub fn
decrypt(
    output: &mut [u8],
    input: &[u8],
    input_len: u32,
    data: &[u8],
    data_len: u32,
    key: &[u8],
    nonce: &[u8],
    tag: &[u8]
) ->
    u32
{
    let mut computed_tag: [u8; 16] = [0u8; 16usize];
    let mut tmp: [u8; 64] = [0u8; 64usize];
    let tmp_copy: [u8; 64] = [0u8; 64usize];
    crate::chacha20_vec256::chacha20_encrypt_256(64u32, &mut tmp, &tmp_copy, key, nonce, 0u32);
    let key1: (&[u8], &[u8]) = tmp.split_at(0usize);
    crate::aead_chacha20poly1305_simd256::poly1305_do_256(
        key1.1,
        data_len,
        data,
        input_len,
        input,
        &mut computed_tag
    );
    let mut res: [u8; 1] = [255u8; 1usize];
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u8 = fstar::uint8::eq_mask((&computed_tag)[i as usize], tag[i as usize]);
            (&mut res)[0usize] = uu____0 & (&res)[0usize]
        }
    );
    let z: u8 = (&res)[0usize];
    if z == 255u8
    {
        crate::chacha20_vec256::chacha20_encrypt_256(input_len, output, input, key, nonce, 1u32);
        0u32
    }
    else
    { 1u32 }
}
