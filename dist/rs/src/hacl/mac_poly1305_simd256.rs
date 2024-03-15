#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn load_acc4(acc: &mut [crate::lib::intvector_intrinsics::vec256], b: &mut [u8]) -> ()
{
    let mut e: [crate::lib::intvector_intrinsics::vec256; 5] =
        [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
    let lo: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64_le(&mut b[0usize..]);
    let hi: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64_le(&mut b[32usize..]);
    let mask26: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let m0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(lo, hi);
    let m1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(lo, hi);
    let m2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right(m0, 48u32);
    let m3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right(m1, 48u32);
    let m4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(m0, m1);
    let t0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(m0, m1);
    let t3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(m2, m3);
    let t2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 4u32);
    let o2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t2, mask26);
    let t1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t0, 26u32);
    let o1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t1, mask26);
    let o5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t0, mask26);
    let t31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 30u32);
    let o3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t31, mask26);
    let o4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(m4, 40u32);
    let o0: crate::lib::intvector_intrinsics::vec256 = o5;
    let o10: crate::lib::intvector_intrinsics::vec256 = o1;
    let o20: crate::lib::intvector_intrinsics::vec256 = o2;
    let o30: crate::lib::intvector_intrinsics::vec256 = o3;
    let o40: crate::lib::intvector_intrinsics::vec256 = o4;
    (&mut e)[0usize] = o0;
    (&mut e)[1usize] = o10;
    (&mut e)[2usize] = o20;
    (&mut e)[3usize] = o30;
    (&mut e)[4usize] = o40;
    let b1: u64 = 0x1000000u64;
    let mask: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(b1);
    let f4: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
    (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec256_or(f4, mask);
    let acc0: crate::lib::intvector_intrinsics::vec256 = acc[0usize];
    let acc1: crate::lib::intvector_intrinsics::vec256 = acc[1usize];
    let acc2: crate::lib::intvector_intrinsics::vec256 = acc[2usize];
    let acc3: crate::lib::intvector_intrinsics::vec256 = acc[3usize];
    let acc4: crate::lib::intvector_intrinsics::vec256 = acc[4usize];
    let e0: crate::lib::intvector_intrinsics::vec256 = (&mut e)[0usize];
    let e1: crate::lib::intvector_intrinsics::vec256 = (&mut e)[1usize];
    let e2: crate::lib::intvector_intrinsics::vec256 = (&mut e)[2usize];
    let e3: crate::lib::intvector_intrinsics::vec256 = (&mut e)[3usize];
    let e4: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
    let r0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_zero;
    let r1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_zero;
    let r2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_zero;
    let r3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_zero;
    let r4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_zero;
    let r01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_insert64(
            r0,
            crate::lib::intvector_intrinsics::vec256_extract64(acc0, 0u32),
            0u32
        );
    let r11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_insert64(
            r1,
            crate::lib::intvector_intrinsics::vec256_extract64(acc1, 0u32),
            0u32
        );
    let r21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_insert64(
            r2,
            crate::lib::intvector_intrinsics::vec256_extract64(acc2, 0u32),
            0u32
        );
    let r31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_insert64(
            r3,
            crate::lib::intvector_intrinsics::vec256_extract64(acc3, 0u32),
            0u32
        );
    let r41: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_insert64(
            r4,
            crate::lib::intvector_intrinsics::vec256_extract64(acc4, 0u32),
            0u32
        );
    let f0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(r01, e0);
    let f1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(r11, e1);
    let f2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(r21, e2);
    let f3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(r31, e3);
    let f40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(r41, e4);
    let acc01: crate::lib::intvector_intrinsics::vec256 = f0;
    let acc11: crate::lib::intvector_intrinsics::vec256 = f1;
    let acc21: crate::lib::intvector_intrinsics::vec256 = f2;
    let acc31: crate::lib::intvector_intrinsics::vec256 = f3;
    let acc41: crate::lib::intvector_intrinsics::vec256 = f40;
    acc[0usize] = acc01;
    acc[1usize] = acc11;
    acc[2usize] = acc21;
    acc[3usize] = acc31;
    acc[4usize] = acc41
}

pub fn fmul_r4_normalize(
    out: &mut [crate::lib::intvector_intrinsics::vec256],
    p: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let
    r:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        p.split_at_mut(0usize);
    let
    r_5:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        r.1.split_at_mut(5usize);
    let
    r4:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        r_5.1.split_at_mut(5usize);
    let a0: crate::lib::intvector_intrinsics::vec256 = out[0usize];
    let a1: crate::lib::intvector_intrinsics::vec256 = out[1usize];
    let a2: crate::lib::intvector_intrinsics::vec256 = out[2usize];
    let a3: crate::lib::intvector_intrinsics::vec256 = out[3usize];
    let a4: crate::lib::intvector_intrinsics::vec256 = out[4usize];
    let r10: crate::lib::intvector_intrinsics::vec256 = r_5.0[0usize];
    let r11: crate::lib::intvector_intrinsics::vec256 = r_5.0[1usize];
    let r12: crate::lib::intvector_intrinsics::vec256 = r_5.0[2usize];
    let r13: crate::lib::intvector_intrinsics::vec256 = r_5.0[3usize];
    let r14: crate::lib::intvector_intrinsics::vec256 = r_5.0[4usize];
    let r151: crate::lib::intvector_intrinsics::vec256 = r4.0[1usize];
    let r152: crate::lib::intvector_intrinsics::vec256 = r4.0[2usize];
    let r153: crate::lib::intvector_intrinsics::vec256 = r4.0[3usize];
    let r154: crate::lib::intvector_intrinsics::vec256 = r4.0[4usize];
    let r40: crate::lib::intvector_intrinsics::vec256 = r4.1[0usize];
    let r41: crate::lib::intvector_intrinsics::vec256 = r4.1[1usize];
    let r42: crate::lib::intvector_intrinsics::vec256 = r4.1[2usize];
    let r43: crate::lib::intvector_intrinsics::vec256 = r4.1[3usize];
    let r44: crate::lib::intvector_intrinsics::vec256 = r4.1[4usize];
    let a01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r10, r10);
    let a11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r11, r10);
    let a21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12, r10);
    let a31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r13, r10);
    let a41: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r14, r10);
    let a02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a01,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r11)
        );
    let a12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a11,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r11)
        );
    let a22: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a21,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r11)
        );
    let a32: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a31,
            crate::lib::intvector_intrinsics::vec256_mul64(r12, r11)
        );
    let a42: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a41,
            crate::lib::intvector_intrinsics::vec256_mul64(r13, r11)
        );
    let a03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a02,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r12)
        );
    let a13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a12,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r12)
        );
    let a23: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a22,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r12)
        );
    let a33: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a32,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r12)
        );
    let a43: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a42,
            crate::lib::intvector_intrinsics::vec256_mul64(r12, r12)
        );
    let a04: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a03,
            crate::lib::intvector_intrinsics::vec256_mul64(r152, r13)
        );
    let a14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a13,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r13)
        );
    let a24: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a23,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r13)
        );
    let a34: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a33,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r13)
        );
    let a44: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a43,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r13)
        );
    let a05: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a04,
            crate::lib::intvector_intrinsics::vec256_mul64(r151, r14)
        );
    let a15: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a14,
            crate::lib::intvector_intrinsics::vec256_mul64(r152, r14)
        );
    let a25: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a24,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r14)
        );
    let a35: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a34,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r14)
        );
    let a45: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a44,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r14)
        );
    let t0: crate::lib::intvector_intrinsics::vec256 = a05;
    let t1: crate::lib::intvector_intrinsics::vec256 = a15;
    let t2: crate::lib::intvector_intrinsics::vec256 = a25;
    let t3: crate::lib::intvector_intrinsics::vec256 = a35;
    let t4: crate::lib::intvector_intrinsics::vec256 = a45;
    let mask26: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t0, 26u32);
    let z1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t0, mask26);
    let x3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t3, mask26);
    let x1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t1, z0);
    let x4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t4, z1);
    let z01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
    let t: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(z11, t);
    let x11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x1, mask26);
    let x41: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x4, mask26);
    let x2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t2, z01);
    let x01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x0, z12);
    let z02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x2, mask26);
    let x02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x01, mask26);
    let x31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x3, z02);
    let x12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x11, z13);
    let z03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x31, mask26);
    let x42: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x41, z03);
    let r20: crate::lib::intvector_intrinsics::vec256 = x02;
    let r21: crate::lib::intvector_intrinsics::vec256 = x12;
    let r22: crate::lib::intvector_intrinsics::vec256 = x21;
    let r23: crate::lib::intvector_intrinsics::vec256 = x32;
    let r24: crate::lib::intvector_intrinsics::vec256 = x42;
    let a010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r10, r20);
    let a110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r11, r20);
    let a210: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12, r20);
    let a310: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r13, r20);
    let a410: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r14, r20);
    let a020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a010,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r21)
        );
    let a120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a110,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r21)
        );
    let a220: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a210,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r21)
        );
    let a320: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a310,
            crate::lib::intvector_intrinsics::vec256_mul64(r12, r21)
        );
    let a420: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a410,
            crate::lib::intvector_intrinsics::vec256_mul64(r13, r21)
        );
    let a030: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a020,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r22)
        );
    let a130: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a120,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r22)
        );
    let a230: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a220,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r22)
        );
    let a330: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a320,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r22)
        );
    let a430: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a420,
            crate::lib::intvector_intrinsics::vec256_mul64(r12, r22)
        );
    let a040: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a030,
            crate::lib::intvector_intrinsics::vec256_mul64(r152, r23)
        );
    let a140: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a130,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r23)
        );
    let a240: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a230,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r23)
        );
    let a340: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a330,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r23)
        );
    let a440: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a430,
            crate::lib::intvector_intrinsics::vec256_mul64(r11, r23)
        );
    let a050: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a040,
            crate::lib::intvector_intrinsics::vec256_mul64(r151, r24)
        );
    let a150: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a140,
            crate::lib::intvector_intrinsics::vec256_mul64(r152, r24)
        );
    let a250: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a240,
            crate::lib::intvector_intrinsics::vec256_mul64(r153, r24)
        );
    let a350: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a340,
            crate::lib::intvector_intrinsics::vec256_mul64(r154, r24)
        );
    let a450: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a440,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, r24)
        );
    let t00: crate::lib::intvector_intrinsics::vec256 = a050;
    let t10: crate::lib::intvector_intrinsics::vec256 = a150;
    let t20: crate::lib::intvector_intrinsics::vec256 = a250;
    let t30: crate::lib::intvector_intrinsics::vec256 = a350;
    let t40: crate::lib::intvector_intrinsics::vec256 = a450;
    let mask260: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t00, 26u32);
    let z10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t30, 26u32);
    let x00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t00, mask260);
    let x30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t30, mask260);
    let x10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t10, z00);
    let x40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t40, z10);
    let z010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x10, 26u32);
    let z110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x40, 26u32);
    let t5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_left64(z110, 2u32);
    let z120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(z110, t5);
    let x110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x10, mask260);
    let x410: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x40, mask260);
    let x20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t20, z010);
    let x010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x00, z120);
    let z020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x20, 26u32);
    let z130: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x010, 26u32);
    let x210: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x20, mask260);
    let x020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x010, mask260);
    let x310: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x30, z020);
    let x120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x110, z130);
    let z030: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x310, 26u32);
    let x320: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x310, mask260);
    let x420: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x410, z030);
    let r30: crate::lib::intvector_intrinsics::vec256 = x020;
    let r31: crate::lib::intvector_intrinsics::vec256 = x120;
    let r32: crate::lib::intvector_intrinsics::vec256 = x210;
    let r33: crate::lib::intvector_intrinsics::vec256 = x320;
    let r34: crate::lib::intvector_intrinsics::vec256 = x420;
    let v12120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r20, r10);
    let v34340: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r40, r30);
    let r12340: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v34340, v12120);
    let v12121: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r21, r11);
    let v34341: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r41, r31);
    let r12341: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v34341, v12121);
    let v12122: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r22, r12);
    let v34342: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r42, r32);
    let r12342: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v34342, v12122);
    let v12123: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r23, r13);
    let v34343: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r43, r33);
    let r12343: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v34343, v12123);
    let v12124: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r24, r14);
    let v34344: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(r44, r34);
    let r12344: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v34344, v12124);
    let r123451: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_smul64(r12341, 5u64);
    let r123452: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_smul64(r12342, 5u64);
    let r123453: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_smul64(r12343, 5u64);
    let r123454: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_smul64(r12344, 5u64);
    let a011: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12340, a0);
    let a111: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12341, a0);
    let a211: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12342, a0);
    let a311: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12343, a0);
    let a411: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r12344, a0);
    let a021: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a011,
            crate::lib::intvector_intrinsics::vec256_mul64(r123454, a1)
        );
    let a121: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a111,
            crate::lib::intvector_intrinsics::vec256_mul64(r12340, a1)
        );
    let a221: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a211,
            crate::lib::intvector_intrinsics::vec256_mul64(r12341, a1)
        );
    let a321: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a311,
            crate::lib::intvector_intrinsics::vec256_mul64(r12342, a1)
        );
    let a421: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a411,
            crate::lib::intvector_intrinsics::vec256_mul64(r12343, a1)
        );
    let a031: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a021,
            crate::lib::intvector_intrinsics::vec256_mul64(r123453, a2)
        );
    let a131: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a121,
            crate::lib::intvector_intrinsics::vec256_mul64(r123454, a2)
        );
    let a231: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a221,
            crate::lib::intvector_intrinsics::vec256_mul64(r12340, a2)
        );
    let a331: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a321,
            crate::lib::intvector_intrinsics::vec256_mul64(r12341, a2)
        );
    let a431: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a421,
            crate::lib::intvector_intrinsics::vec256_mul64(r12342, a2)
        );
    let a041: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a031,
            crate::lib::intvector_intrinsics::vec256_mul64(r123452, a3)
        );
    let a141: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a131,
            crate::lib::intvector_intrinsics::vec256_mul64(r123453, a3)
        );
    let a241: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a231,
            crate::lib::intvector_intrinsics::vec256_mul64(r123454, a3)
        );
    let a341: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a331,
            crate::lib::intvector_intrinsics::vec256_mul64(r12340, a3)
        );
    let a441: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a431,
            crate::lib::intvector_intrinsics::vec256_mul64(r12341, a3)
        );
    let a051: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a041,
            crate::lib::intvector_intrinsics::vec256_mul64(r123451, a4)
        );
    let a151: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a141,
            crate::lib::intvector_intrinsics::vec256_mul64(r123452, a4)
        );
    let a251: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a241,
            crate::lib::intvector_intrinsics::vec256_mul64(r123453, a4)
        );
    let a351: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a341,
            crate::lib::intvector_intrinsics::vec256_mul64(r123454, a4)
        );
    let a451: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a441,
            crate::lib::intvector_intrinsics::vec256_mul64(r12340, a4)
        );
    let t01: crate::lib::intvector_intrinsics::vec256 = a051;
    let t11: crate::lib::intvector_intrinsics::vec256 = a151;
    let t21: crate::lib::intvector_intrinsics::vec256 = a251;
    let t31: crate::lib::intvector_intrinsics::vec256 = a351;
    let t41: crate::lib::intvector_intrinsics::vec256 = a451;
    let mask261: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z04: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
    let z14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t31, 26u32);
    let x03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t01, mask261);
    let x33: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t31, mask261);
    let x13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t11, z04);
    let x43: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t41, z14);
    let z011: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x13, 26u32);
    let z111: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x43, 26u32);
    let t6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_left64(z111, 2u32);
    let z121: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(z111, t6);
    let x111: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x13, mask261);
    let x411: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x43, mask261);
    let x22: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t21, z011);
    let x011: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x03, z121);
    let z021: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x22, 26u32);
    let z131: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x011, 26u32);
    let x211: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x22, mask261);
    let x021: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x011, mask261);
    let x311: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x33, z021);
    let x121: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x111, z131);
    let z031: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x311, 26u32);
    let x321: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x311, mask261);
    let x421: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x411, z031);
    let o0: crate::lib::intvector_intrinsics::vec256 = x021;
    let o1: crate::lib::intvector_intrinsics::vec256 = x121;
    let o2: crate::lib::intvector_intrinsics::vec256 = x211;
    let o3: crate::lib::intvector_intrinsics::vec256 = x321;
    let o4: crate::lib::intvector_intrinsics::vec256 = x421;
    let v00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(o0, o0);
    let v10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(o0, v00);
    let v10h: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v10, v10);
    let v20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v10, v10h);
    let v01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(o1, o1);
    let v11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(o1, v01);
    let v11h: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v11, v11);
    let v21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v11, v11h);
    let v02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(o2, o2);
    let v12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(o2, v02);
    let v12h: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v12, v12);
    let v22: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v12, v12h);
    let v03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(o3, o3);
    let v13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(o3, v03);
    let v13h: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v13, v13);
    let v23: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v13, v13h);
    let v04: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(o4, o4);
    let v14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(o4, v04);
    let v14h: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v14, v14);
    let v24: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v14, v14h);
    let l: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            v20,
            crate::lib::intvector_intrinsics::vec256_zero
        );
    let tmp0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l, 26u32);
    let l0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v21, c0);
    let tmp1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l0,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l0, 26u32);
    let l1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v22, c1);
    let tmp2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l1,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l1, 26u32);
    let l2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v23, c2);
    let tmp3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l2,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l2, 26u32);
    let l3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(v24, c3);
    let tmp4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l3,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l3, 26u32);
    let o00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            tmp0,
            crate::lib::intvector_intrinsics::vec256_smul64(c4, 5u64)
        );
    let o10: crate::lib::intvector_intrinsics::vec256 = tmp1;
    let o20: crate::lib::intvector_intrinsics::vec256 = tmp2;
    let o30: crate::lib::intvector_intrinsics::vec256 = tmp3;
    let o40: crate::lib::intvector_intrinsics::vec256 = tmp4;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

pub fn poly1305_init(ctx: &mut [crate::lib::intvector_intrinsics::vec256], key: &mut [u8]) ->
    ()
{
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        ctx.split_at_mut(0usize);
    let
    pre:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        acc.1.split_at_mut(5usize);
    let kr: (&mut [u8], &mut [u8]) = key.split_at_mut(0usize);
    pre.0[0usize] = crate::lib::intvector_intrinsics::vec256_zero;
    pre.0[1usize] = crate::lib::intvector_intrinsics::vec256_zero;
    pre.0[2usize] = crate::lib::intvector_intrinsics::vec256_zero;
    pre.0[3usize] = crate::lib::intvector_intrinsics::vec256_zero;
    pre.0[4usize] = crate::lib::intvector_intrinsics::vec256_zero;
    let u: u64 = crate::lowstar::endianness::load64_le(&mut kr.1[0usize..]);
    let lo: u64 = u;
    let u0: u64 = crate::lowstar::endianness::load64_le(&mut kr.1[8usize..]);
    let hi: u64 = u0;
    let mask0: u64 = 0x0ffffffc0fffffffu64;
    let mask1: u64 = 0x0ffffffc0ffffffcu64;
    let lo1: u64 = lo & mask0;
    let hi1: u64 = hi & mask1;
    let
    r:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        pre.1.split_at_mut(0usize);
    let
    r5:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        r.1.split_at_mut(5usize);
    let
    rn:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        r5.1.split_at_mut(5usize);
    let
    rn_5:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        rn.1.split_at_mut(5usize);
    let r_vec0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(lo1);
    let r_vec1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(hi1);
    let f0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            r_vec0,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            crate::lib::intvector_intrinsics::vec256_shift_right64(r_vec0, 26u32),
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_or(
            crate::lib::intvector_intrinsics::vec256_shift_right64(r_vec0, 52u32),
            crate::lib::intvector_intrinsics::vec256_shift_left64(
                crate::lib::intvector_intrinsics::vec256_and(
                    r_vec1,
                    crate::lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                ),
                12u32
            )
        );
    let f3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            crate::lib::intvector_intrinsics::vec256_shift_right64(r_vec1, 14u32),
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let f4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(r_vec1, 40u32);
    let f00: crate::lib::intvector_intrinsics::vec256 = f0;
    let f10: crate::lib::intvector_intrinsics::vec256 = f1;
    let f20: crate::lib::intvector_intrinsics::vec256 = f2;
    let f30: crate::lib::intvector_intrinsics::vec256 = f3;
    let f40: crate::lib::intvector_intrinsics::vec256 = f4;
    r5.0[0usize] = f00;
    r5.0[1usize] = f10;
    r5.0[2usize] = f20;
    r5.0[3usize] = f30;
    r5.0[4usize] = f40;
    let f200: crate::lib::intvector_intrinsics::vec256 = r5.0[0usize];
    let f21: crate::lib::intvector_intrinsics::vec256 = r5.0[1usize];
    let f22: crate::lib::intvector_intrinsics::vec256 = r5.0[2usize];
    let f23: crate::lib::intvector_intrinsics::vec256 = r5.0[3usize];
    let f24: crate::lib::intvector_intrinsics::vec256 = r5.0[4usize];
    rn.0[0usize] = crate::lib::intvector_intrinsics::vec256_smul64(f200, 5u64);
    rn.0[1usize] = crate::lib::intvector_intrinsics::vec256_smul64(f21, 5u64);
    rn.0[2usize] = crate::lib::intvector_intrinsics::vec256_smul64(f22, 5u64);
    rn.0[3usize] = crate::lib::intvector_intrinsics::vec256_smul64(f23, 5u64);
    rn.0[4usize] = crate::lib::intvector_intrinsics::vec256_smul64(f24, 5u64);
    let r0: crate::lib::intvector_intrinsics::vec256 = r5.0[0usize];
    let r1: crate::lib::intvector_intrinsics::vec256 = r5.0[1usize];
    let r2: crate::lib::intvector_intrinsics::vec256 = r5.0[2usize];
    let r3: crate::lib::intvector_intrinsics::vec256 = r5.0[3usize];
    let r4: crate::lib::intvector_intrinsics::vec256 = r5.0[4usize];
    let r51: crate::lib::intvector_intrinsics::vec256 = rn.0[1usize];
    let r52: crate::lib::intvector_intrinsics::vec256 = rn.0[2usize];
    let r53: crate::lib::intvector_intrinsics::vec256 = rn.0[3usize];
    let r54: crate::lib::intvector_intrinsics::vec256 = rn.0[4usize];
    let f100: crate::lib::intvector_intrinsics::vec256 = r5.0[0usize];
    let f11: crate::lib::intvector_intrinsics::vec256 = r5.0[1usize];
    let f12: crate::lib::intvector_intrinsics::vec256 = r5.0[2usize];
    let f13: crate::lib::intvector_intrinsics::vec256 = r5.0[3usize];
    let f14: crate::lib::intvector_intrinsics::vec256 = r5.0[4usize];
    let a0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r0, f100);
    let a1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r1, f100);
    let a2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r2, f100);
    let a3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r3, f100);
    let a4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r4, f100);
    let a01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a0,
            crate::lib::intvector_intrinsics::vec256_mul64(r54, f11)
        );
    let a11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a1,
            crate::lib::intvector_intrinsics::vec256_mul64(r0, f11)
        );
    let a21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a2,
            crate::lib::intvector_intrinsics::vec256_mul64(r1, f11)
        );
    let a31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a3,
            crate::lib::intvector_intrinsics::vec256_mul64(r2, f11)
        );
    let a41: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a4,
            crate::lib::intvector_intrinsics::vec256_mul64(r3, f11)
        );
    let a02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a01,
            crate::lib::intvector_intrinsics::vec256_mul64(r53, f12)
        );
    let a12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a11,
            crate::lib::intvector_intrinsics::vec256_mul64(r54, f12)
        );
    let a22: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a21,
            crate::lib::intvector_intrinsics::vec256_mul64(r0, f12)
        );
    let a32: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a31,
            crate::lib::intvector_intrinsics::vec256_mul64(r1, f12)
        );
    let a42: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a41,
            crate::lib::intvector_intrinsics::vec256_mul64(r2, f12)
        );
    let a03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a02,
            crate::lib::intvector_intrinsics::vec256_mul64(r52, f13)
        );
    let a13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a12,
            crate::lib::intvector_intrinsics::vec256_mul64(r53, f13)
        );
    let a23: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a22,
            crate::lib::intvector_intrinsics::vec256_mul64(r54, f13)
        );
    let a33: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a32,
            crate::lib::intvector_intrinsics::vec256_mul64(r0, f13)
        );
    let a43: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a42,
            crate::lib::intvector_intrinsics::vec256_mul64(r1, f13)
        );
    let a04: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a03,
            crate::lib::intvector_intrinsics::vec256_mul64(r51, f14)
        );
    let a14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a13,
            crate::lib::intvector_intrinsics::vec256_mul64(r52, f14)
        );
    let a24: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a23,
            crate::lib::intvector_intrinsics::vec256_mul64(r53, f14)
        );
    let a34: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a33,
            crate::lib::intvector_intrinsics::vec256_mul64(r54, f14)
        );
    let a44: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a43,
            crate::lib::intvector_intrinsics::vec256_mul64(r0, f14)
        );
    let t0: crate::lib::intvector_intrinsics::vec256 = a04;
    let t1: crate::lib::intvector_intrinsics::vec256 = a14;
    let t2: crate::lib::intvector_intrinsics::vec256 = a24;
    let t3: crate::lib::intvector_intrinsics::vec256 = a34;
    let t4: crate::lib::intvector_intrinsics::vec256 = a44;
    let mask26: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t0, 26u32);
    let z1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t0, mask26);
    let x3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t3, mask26);
    let x1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t1, z0);
    let x4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t4, z1);
    let z01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
    let t: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(z11, t);
    let x11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x1, mask26);
    let x41: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x4, mask26);
    let x2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t2, z01);
    let x01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x0, z12);
    let z02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x2, mask26);
    let x02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x01, mask26);
    let x31: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x3, z02);
    let x12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x11, z13);
    let z03: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x31, mask26);
    let x42: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x41, z03);
    let o0: crate::lib::intvector_intrinsics::vec256 = x02;
    let o1: crate::lib::intvector_intrinsics::vec256 = x12;
    let o2: crate::lib::intvector_intrinsics::vec256 = x21;
    let o3: crate::lib::intvector_intrinsics::vec256 = x32;
    let o4: crate::lib::intvector_intrinsics::vec256 = x42;
    rn_5.0[0usize] = o0;
    rn_5.0[1usize] = o1;
    rn_5.0[2usize] = o2;
    rn_5.0[3usize] = o3;
    rn_5.0[4usize] = o4;
    let f201: crate::lib::intvector_intrinsics::vec256 = rn_5.0[0usize];
    let f210: crate::lib::intvector_intrinsics::vec256 = rn_5.0[1usize];
    let f220: crate::lib::intvector_intrinsics::vec256 = rn_5.0[2usize];
    let f230: crate::lib::intvector_intrinsics::vec256 = rn_5.0[3usize];
    let f240: crate::lib::intvector_intrinsics::vec256 = rn_5.0[4usize];
    rn_5.1[0usize] = crate::lib::intvector_intrinsics::vec256_smul64(f201, 5u64);
    rn_5.1[1usize] = crate::lib::intvector_intrinsics::vec256_smul64(f210, 5u64);
    rn_5.1[2usize] = crate::lib::intvector_intrinsics::vec256_smul64(f220, 5u64);
    rn_5.1[3usize] = crate::lib::intvector_intrinsics::vec256_smul64(f230, 5u64);
    rn_5.1[4usize] = crate::lib::intvector_intrinsics::vec256_smul64(f240, 5u64);
    let r00: crate::lib::intvector_intrinsics::vec256 = rn_5.0[0usize];
    let r10: crate::lib::intvector_intrinsics::vec256 = rn_5.0[1usize];
    let r20: crate::lib::intvector_intrinsics::vec256 = rn_5.0[2usize];
    let r30: crate::lib::intvector_intrinsics::vec256 = rn_5.0[3usize];
    let r40: crate::lib::intvector_intrinsics::vec256 = rn_5.0[4usize];
    let r510: crate::lib::intvector_intrinsics::vec256 = rn_5.1[1usize];
    let r520: crate::lib::intvector_intrinsics::vec256 = rn_5.1[2usize];
    let r530: crate::lib::intvector_intrinsics::vec256 = rn_5.1[3usize];
    let r540: crate::lib::intvector_intrinsics::vec256 = rn_5.1[4usize];
    let f101: crate::lib::intvector_intrinsics::vec256 = rn_5.0[0usize];
    let f110: crate::lib::intvector_intrinsics::vec256 = rn_5.0[1usize];
    let f120: crate::lib::intvector_intrinsics::vec256 = rn_5.0[2usize];
    let f130: crate::lib::intvector_intrinsics::vec256 = rn_5.0[3usize];
    let f140: crate::lib::intvector_intrinsics::vec256 = rn_5.0[4usize];
    let a00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r00, f101);
    let a10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r10, f101);
    let a20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r20, f101);
    let a30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r30, f101);
    let a40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_mul64(r40, f101);
    let a010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a00,
            crate::lib::intvector_intrinsics::vec256_mul64(r540, f110)
        );
    let a110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a10,
            crate::lib::intvector_intrinsics::vec256_mul64(r00, f110)
        );
    let a210: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a20,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, f110)
        );
    let a310: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a30,
            crate::lib::intvector_intrinsics::vec256_mul64(r20, f110)
        );
    let a410: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a40,
            crate::lib::intvector_intrinsics::vec256_mul64(r30, f110)
        );
    let a020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a010,
            crate::lib::intvector_intrinsics::vec256_mul64(r530, f120)
        );
    let a120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a110,
            crate::lib::intvector_intrinsics::vec256_mul64(r540, f120)
        );
    let a220: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a210,
            crate::lib::intvector_intrinsics::vec256_mul64(r00, f120)
        );
    let a320: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a310,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, f120)
        );
    let a420: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a410,
            crate::lib::intvector_intrinsics::vec256_mul64(r20, f120)
        );
    let a030: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a020,
            crate::lib::intvector_intrinsics::vec256_mul64(r520, f130)
        );
    let a130: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a120,
            crate::lib::intvector_intrinsics::vec256_mul64(r530, f130)
        );
    let a230: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a220,
            crate::lib::intvector_intrinsics::vec256_mul64(r540, f130)
        );
    let a330: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a320,
            crate::lib::intvector_intrinsics::vec256_mul64(r00, f130)
        );
    let a430: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a420,
            crate::lib::intvector_intrinsics::vec256_mul64(r10, f130)
        );
    let a040: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a030,
            crate::lib::intvector_intrinsics::vec256_mul64(r510, f140)
        );
    let a140: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a130,
            crate::lib::intvector_intrinsics::vec256_mul64(r520, f140)
        );
    let a240: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a230,
            crate::lib::intvector_intrinsics::vec256_mul64(r530, f140)
        );
    let a340: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a330,
            crate::lib::intvector_intrinsics::vec256_mul64(r540, f140)
        );
    let a440: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            a430,
            crate::lib::intvector_intrinsics::vec256_mul64(r00, f140)
        );
    let t00: crate::lib::intvector_intrinsics::vec256 = a040;
    let t10: crate::lib::intvector_intrinsics::vec256 = a140;
    let t20: crate::lib::intvector_intrinsics::vec256 = a240;
    let t30: crate::lib::intvector_intrinsics::vec256 = a340;
    let t40: crate::lib::intvector_intrinsics::vec256 = a440;
    let mask260: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let z00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t00, 26u32);
    let z10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(t30, 26u32);
    let x00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t00, mask260);
    let x30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(t30, mask260);
    let x10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t10, z00);
    let x40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t40, z10);
    let z010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x10, 26u32);
    let z110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x40, 26u32);
    let t5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_left64(z110, 2u32);
    let z120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(z110, t5);
    let x110: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x10, mask260);
    let x410: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x40, mask260);
    let x20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(t20, z010);
    let x010: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x00, z120);
    let z020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x20, 26u32);
    let z130: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x010, 26u32);
    let x210: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x20, mask260);
    let x020: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x010, mask260);
    let x310: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x30, z020);
    let x120: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x110, z130);
    let z030: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(x310, 26u32);
    let x320: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(x310, mask260);
    let x420: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(x410, z030);
    let o00: crate::lib::intvector_intrinsics::vec256 = x020;
    let o10: crate::lib::intvector_intrinsics::vec256 = x120;
    let o20: crate::lib::intvector_intrinsics::vec256 = x210;
    let o30: crate::lib::intvector_intrinsics::vec256 = x320;
    let o40: crate::lib::intvector_intrinsics::vec256 = x420;
    rn_5.0[0usize] = o00;
    rn_5.0[1usize] = o10;
    rn_5.0[2usize] = o20;
    rn_5.0[3usize] = o30;
    rn_5.0[4usize] = o40;
    let f202: crate::lib::intvector_intrinsics::vec256 = rn_5.0[0usize];
    let f211: crate::lib::intvector_intrinsics::vec256 = rn_5.0[1usize];
    let f221: crate::lib::intvector_intrinsics::vec256 = rn_5.0[2usize];
    let f231: crate::lib::intvector_intrinsics::vec256 = rn_5.0[3usize];
    let f241: crate::lib::intvector_intrinsics::vec256 = rn_5.0[4usize];
    rn_5.1[0usize] = crate::lib::intvector_intrinsics::vec256_smul64(f202, 5u64);
    rn_5.1[1usize] = crate::lib::intvector_intrinsics::vec256_smul64(f211, 5u64);
    rn_5.1[2usize] = crate::lib::intvector_intrinsics::vec256_smul64(f221, 5u64);
    rn_5.1[3usize] = crate::lib::intvector_intrinsics::vec256_smul64(f231, 5u64);
    rn_5.1[4usize] = crate::lib::intvector_intrinsics::vec256_smul64(f241, 5u64)
}

fn poly1305_update(
    ctx: &mut [crate::lib::intvector_intrinsics::vec256],
    len: u32,
    text: &mut [u8]
) ->
    ()
{
    let
    pre:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        ctx.split_at_mut(5usize);
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        pre.0.split_at_mut(0usize);
    let sz_block: u32 = 64u32;
    let len0: u32 = len.wrapping_div(sz_block).wrapping_mul(sz_block);
    let t0: (&mut [u8], &mut [u8]) = text.split_at_mut(0usize);
    if len0 > 0u32
    {
        let bs: u32 = 64u32;
        let text0: (&mut [u8], &mut [u8]) = t0.1.split_at_mut(0usize);
        load_acc4(acc.1, text0.1);
        let len1: u32 = len0.wrapping_sub(bs);
        let text1: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(bs as usize);
        let nb: u32 = len1.wrapping_div(bs);
        for i in 0u32..nb
        {
            let block: (&mut [u8], &mut [u8]) = text1.1.split_at_mut(i.wrapping_mul(bs) as usize);
            let mut e: [crate::lib::intvector_intrinsics::vec256; 5] =
                [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
            let lo: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64_le(&mut block.1[0usize..]);
            let hi: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64_le(&mut block.1[32usize..]);
            let mask26: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
            let m0: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_interleave_low128(lo, hi);
            let m1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_interleave_high128(lo, hi);
            let m2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right(m0, 48u32);
            let m3: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right(m1, 48u32);
            let m4: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_interleave_high64(m0, m1);
            let t01: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_interleave_low64(m0, m1);
            let t3: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_interleave_low64(m2, m3);
            let t2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 4u32);
            let o2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t2, mask26);
            let t1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
            let o1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t1, mask26);
            let o5: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t01, mask26);
            let t31: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 30u32);
            let o3: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t31, mask26);
            let o4: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(m4, 40u32);
            let o0: crate::lib::intvector_intrinsics::vec256 = o5;
            let o10: crate::lib::intvector_intrinsics::vec256 = o1;
            let o20: crate::lib::intvector_intrinsics::vec256 = o2;
            let o30: crate::lib::intvector_intrinsics::vec256 = o3;
            let o40: crate::lib::intvector_intrinsics::vec256 = o4;
            (&mut e)[0usize] = o0;
            (&mut e)[1usize] = o10;
            (&mut e)[2usize] = o20;
            (&mut e)[3usize] = o30;
            (&mut e)[4usize] = o40;
            let b: u64 = 0x1000000u64;
            let mask: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64(b);
            let f4: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
            (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec256_or(f4, mask);
            let
            rn:
            (&mut [crate::lib::intvector_intrinsics::vec256],
            &mut [crate::lib::intvector_intrinsics::vec256])
            =
                pre.1.split_at_mut(10usize);
            let
            rn5:
            (&mut [crate::lib::intvector_intrinsics::vec256],
            &mut [crate::lib::intvector_intrinsics::vec256])
            =
                rn.1.split_at_mut(5usize);
            let r0: crate::lib::intvector_intrinsics::vec256 = rn5.0[0usize];
            let r1: crate::lib::intvector_intrinsics::vec256 = rn5.0[1usize];
            let r2: crate::lib::intvector_intrinsics::vec256 = rn5.0[2usize];
            let r3: crate::lib::intvector_intrinsics::vec256 = rn5.0[3usize];
            let r4: crate::lib::intvector_intrinsics::vec256 = rn5.0[4usize];
            let r51: crate::lib::intvector_intrinsics::vec256 = rn5.1[1usize];
            let r52: crate::lib::intvector_intrinsics::vec256 = rn5.1[2usize];
            let r53: crate::lib::intvector_intrinsics::vec256 = rn5.1[3usize];
            let r54: crate::lib::intvector_intrinsics::vec256 = rn5.1[4usize];
            let f10: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
            let f11: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
            let f12: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
            let f13: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
            let f14: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
            let a0: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_mul64(r0, f10);
            let a1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_mul64(r1, f10);
            let a2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_mul64(r2, f10);
            let a3: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_mul64(r3, f10);
            let a4: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_mul64(r4, f10);
            let a01: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a0,
                    crate::lib::intvector_intrinsics::vec256_mul64(r54, f11)
                );
            let a11: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a1,
                    crate::lib::intvector_intrinsics::vec256_mul64(r0, f11)
                );
            let a21: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a2,
                    crate::lib::intvector_intrinsics::vec256_mul64(r1, f11)
                );
            let a31: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a3,
                    crate::lib::intvector_intrinsics::vec256_mul64(r2, f11)
                );
            let a41: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a4,
                    crate::lib::intvector_intrinsics::vec256_mul64(r3, f11)
                );
            let a02: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a01,
                    crate::lib::intvector_intrinsics::vec256_mul64(r53, f12)
                );
            let a12: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a11,
                    crate::lib::intvector_intrinsics::vec256_mul64(r54, f12)
                );
            let a22: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a21,
                    crate::lib::intvector_intrinsics::vec256_mul64(r0, f12)
                );
            let a32: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a31,
                    crate::lib::intvector_intrinsics::vec256_mul64(r1, f12)
                );
            let a42: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a41,
                    crate::lib::intvector_intrinsics::vec256_mul64(r2, f12)
                );
            let a03: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a02,
                    crate::lib::intvector_intrinsics::vec256_mul64(r52, f13)
                );
            let a13: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a12,
                    crate::lib::intvector_intrinsics::vec256_mul64(r53, f13)
                );
            let a23: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a22,
                    crate::lib::intvector_intrinsics::vec256_mul64(r54, f13)
                );
            let a33: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a32,
                    crate::lib::intvector_intrinsics::vec256_mul64(r0, f13)
                );
            let a43: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a42,
                    crate::lib::intvector_intrinsics::vec256_mul64(r1, f13)
                );
            let a04: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a03,
                    crate::lib::intvector_intrinsics::vec256_mul64(r51, f14)
                );
            let a14: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a13,
                    crate::lib::intvector_intrinsics::vec256_mul64(r52, f14)
                );
            let a24: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a23,
                    crate::lib::intvector_intrinsics::vec256_mul64(r53, f14)
                );
            let a34: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a33,
                    crate::lib::intvector_intrinsics::vec256_mul64(r54, f14)
                );
            let a44: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    a43,
                    crate::lib::intvector_intrinsics::vec256_mul64(r0, f14)
                );
            let t010: crate::lib::intvector_intrinsics::vec256 = a04;
            let t10: crate::lib::intvector_intrinsics::vec256 = a14;
            let t20: crate::lib::intvector_intrinsics::vec256 = a24;
            let t30: crate::lib::intvector_intrinsics::vec256 = a34;
            let t4: crate::lib::intvector_intrinsics::vec256 = a44;
            let mask260: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
            let z0: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(t010, 26u32);
            let z1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(t30, 26u32);
            let x0: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t010, mask260);
            let x3: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(t30, mask260);
            let x1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(t10, z0);
            let x4: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(t4, z1);
            let z01: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
            let z11: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
            let t: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
            let z12: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(z11, t);
            let x11: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(x1, mask260);
            let x41: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(x4, mask260);
            let x2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(t20, z01);
            let x01: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(x0, z12);
            let z02: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
            let z13: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
            let x21: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(x2, mask260);
            let x02: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(x01, mask260);
            let x31: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(x3, z02);
            let x12: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(x11, z13);
            let z03: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
            let x32: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_and(x31, mask260);
            let x42: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(x41, z03);
            let o00: crate::lib::intvector_intrinsics::vec256 = x02;
            let o11: crate::lib::intvector_intrinsics::vec256 = x12;
            let o21: crate::lib::intvector_intrinsics::vec256 = x21;
            let o31: crate::lib::intvector_intrinsics::vec256 = x32;
            let o41: crate::lib::intvector_intrinsics::vec256 = x42;
            acc.1[0usize] = o00;
            acc.1[1usize] = o11;
            acc.1[2usize] = o21;
            acc.1[3usize] = o31;
            acc.1[4usize] = o41;
            let f100: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
            let f110: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
            let f120: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
            let f130: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
            let f140: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
            let f20: crate::lib::intvector_intrinsics::vec256 = (&mut e)[0usize];
            let f21: crate::lib::intvector_intrinsics::vec256 = (&mut e)[1usize];
            let f22: crate::lib::intvector_intrinsics::vec256 = (&mut e)[2usize];
            let f23: crate::lib::intvector_intrinsics::vec256 = (&mut e)[3usize];
            let f24: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
            let o01: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(f100, f20);
            let o12: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(f110, f21);
            let o22: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(f120, f22);
            let o32: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(f130, f23);
            let o42: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(f140, f24);
            acc.1[0usize] = o01;
            acc.1[1usize] = o12;
            acc.1[2usize] = o22;
            acc.1[3usize] = o32;
            acc.1[4usize] = o42
        };
        fmul_r4_normalize(acc.1, pre.1)
    };
    let len1: u32 = len.wrapping_sub(len0);
    let t1: (&mut [u8], &mut [u8]) = t0.1.split_at_mut(len0 as usize);
    let nb: u32 = len1.wrapping_div(16u32);
    let rem: u32 = len1.wrapping_rem(16u32);
    for i in 0u32..nb
    {
        let block: (&mut [u8], &mut [u8]) = t1.1.split_at_mut(i.wrapping_mul(16u32) as usize);
        let mut e: [crate::lib::intvector_intrinsics::vec256; 5] =
            [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
        let u: u64 = crate::lowstar::endianness::load64_le(&mut block.1[0usize..]);
        let lo: u64 = u;
        let u0: u64 = crate::lowstar::endianness::load64_le(&mut block.1[8usize..]);
        let hi: u64 = u0;
        let f0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(lo);
        let f1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(hi);
        let f01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                f0,
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_or(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
                crate::lib::intvector_intrinsics::vec256_shift_left64(
                    crate::lib::intvector_intrinsics::vec256_and(
                        f1,
                        crate::lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
        let f010: crate::lib::intvector_intrinsics::vec256 = f01;
        let f110: crate::lib::intvector_intrinsics::vec256 = f11;
        let f20: crate::lib::intvector_intrinsics::vec256 = f2;
        let f30: crate::lib::intvector_intrinsics::vec256 = f3;
        let f40: crate::lib::intvector_intrinsics::vec256 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 0x1000000u64;
        let mask: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(b);
        let f41: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
        (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec256_or(f41, mask);
        let
        r:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            pre.1.split_at_mut(0usize);
        let
        r5:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            r.1.split_at_mut(5usize);
        let r0: crate::lib::intvector_intrinsics::vec256 = r5.0[0usize];
        let r1: crate::lib::intvector_intrinsics::vec256 = r5.0[1usize];
        let r2: crate::lib::intvector_intrinsics::vec256 = r5.0[2usize];
        let r3: crate::lib::intvector_intrinsics::vec256 = r5.0[3usize];
        let r4: crate::lib::intvector_intrinsics::vec256 = r5.0[4usize];
        let r51: crate::lib::intvector_intrinsics::vec256 = r5.1[1usize];
        let r52: crate::lib::intvector_intrinsics::vec256 = r5.1[2usize];
        let r53: crate::lib::intvector_intrinsics::vec256 = r5.1[3usize];
        let r54: crate::lib::intvector_intrinsics::vec256 = r5.1[4usize];
        let f10: crate::lib::intvector_intrinsics::vec256 = (&mut e)[0usize];
        let f111: crate::lib::intvector_intrinsics::vec256 = (&mut e)[1usize];
        let f12: crate::lib::intvector_intrinsics::vec256 = (&mut e)[2usize];
        let f13: crate::lib::intvector_intrinsics::vec256 = (&mut e)[3usize];
        let f14: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
        let a0: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
        let a1: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
        let a2: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
        let a3: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
        let a4: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
        let a01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a0, f10);
        let a11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a1, f111);
        let a21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a2, f12);
        let a31: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a3, f13);
        let a41: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a4, f14);
        let a02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r0, a01);
        let a12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r1, a01);
        let a22: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r2, a01);
        let a32: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r3, a01);
        let a42: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r4, a01);
        let a03: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a02,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a11)
            );
        let a13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a12,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a11)
            );
        let a23: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a22,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a11)
            );
        let a33: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a32,
                crate::lib::intvector_intrinsics::vec256_mul64(r2, a11)
            );
        let a43: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a42,
                crate::lib::intvector_intrinsics::vec256_mul64(r3, a11)
            );
        let a04: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a03,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a21)
            );
        let a14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a13,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a21)
            );
        let a24: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a23,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a21)
            );
        let a34: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a33,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a21)
            );
        let a44: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a43,
                crate::lib::intvector_intrinsics::vec256_mul64(r2, a21)
            );
        let a05: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a04,
                crate::lib::intvector_intrinsics::vec256_mul64(r52, a31)
            );
        let a15: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a14,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a31)
            );
        let a25: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a24,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a31)
            );
        let a35: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a34,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a31)
            );
        let a45: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a44,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a31)
            );
        let a06: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a05,
                crate::lib::intvector_intrinsics::vec256_mul64(r51, a41)
            );
        let a16: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a15,
                crate::lib::intvector_intrinsics::vec256_mul64(r52, a41)
            );
        let a26: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a25,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a41)
            );
        let a36: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a35,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a41)
            );
        let a46: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a45,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a41)
            );
        let t01: crate::lib::intvector_intrinsics::vec256 = a06;
        let t11: crate::lib::intvector_intrinsics::vec256 = a16;
        let t2: crate::lib::intvector_intrinsics::vec256 = a26;
        let t3: crate::lib::intvector_intrinsics::vec256 = a36;
        let t4: crate::lib::intvector_intrinsics::vec256 = a46;
        let mask26: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
        let z0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
        let z1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
        let x0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(t01, mask26);
        let x3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(t3, mask26);
        let x1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t11, z0);
        let x4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t4, z1);
        let z01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
        let z11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
        let t: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
        let z12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(z11, t);
        let x11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x1, mask26);
        let x41: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x4, mask26);
        let x2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t2, z01);
        let x01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x0, z12);
        let z02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
        let z13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
        let x21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x2, mask26);
        let x02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x01, mask26);
        let x31: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x3, z02);
        let x12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x11, z13);
        let z03: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
        let x32: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x31, mask26);
        let x42: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x41, z03);
        let o0: crate::lib::intvector_intrinsics::vec256 = x02;
        let o1: crate::lib::intvector_intrinsics::vec256 = x12;
        let o2: crate::lib::intvector_intrinsics::vec256 = x21;
        let o3: crate::lib::intvector_intrinsics::vec256 = x32;
        let o4: crate::lib::intvector_intrinsics::vec256 = x42;
        acc.1[0usize] = o0;
        acc.1[1usize] = o1;
        acc.1[2usize] = o2;
        acc.1[3usize] = o3;
        acc.1[4usize] = o4
    };
    if rem > 0u32
    {
        let last: (&mut [u8], &mut [u8]) = t1.1.split_at_mut(nb.wrapping_mul(16u32) as usize);
        let mut e: [crate::lib::intvector_intrinsics::vec256; 5] =
            [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
        let mut tmp: [u8; 16] = [0u8; 16usize];
        ((&mut tmp)[0usize..rem as usize]).copy_from_slice(&last.1[0usize..rem as usize]);
        let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[0usize..]);
        let lo: u64 = u;
        let u0: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[8usize..]);
        let hi: u64 = u0;
        let f0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(lo);
        let f1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(hi);
        let f01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                f0,
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f0, 26u32),
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_or(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f0, 52u32),
                crate::lib::intvector_intrinsics::vec256_shift_left64(
                    crate::lib::intvector_intrinsics::vec256_and(
                        f1,
                        crate::lib::intvector_intrinsics::vec256_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(
                crate::lib::intvector_intrinsics::vec256_shift_right64(f1, 14u32),
                crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
            );
        let f4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(f1, 40u32);
        let f010: crate::lib::intvector_intrinsics::vec256 = f01;
        let f110: crate::lib::intvector_intrinsics::vec256 = f11;
        let f20: crate::lib::intvector_intrinsics::vec256 = f2;
        let f30: crate::lib::intvector_intrinsics::vec256 = f3;
        let f40: crate::lib::intvector_intrinsics::vec256 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 1u64.wrapping_shl(rem.wrapping_mul(8u32).wrapping_rem(26u32));
        let mask: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(b);
        let fi: crate::lib::intvector_intrinsics::vec256 =
            (&mut e)[rem.wrapping_mul(8u32).wrapping_div(26u32) as usize];
        (&mut e)[rem.wrapping_mul(8u32).wrapping_div(26u32) as usize] =
            crate::lib::intvector_intrinsics::vec256_or(fi, mask);
        let
        r:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            pre.1.split_at_mut(0usize);
        let
        r5:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            r.1.split_at_mut(5usize);
        let r0: crate::lib::intvector_intrinsics::vec256 = r5.0[0usize];
        let r1: crate::lib::intvector_intrinsics::vec256 = r5.0[1usize];
        let r2: crate::lib::intvector_intrinsics::vec256 = r5.0[2usize];
        let r3: crate::lib::intvector_intrinsics::vec256 = r5.0[3usize];
        let r4: crate::lib::intvector_intrinsics::vec256 = r5.0[4usize];
        let r51: crate::lib::intvector_intrinsics::vec256 = r5.1[1usize];
        let r52: crate::lib::intvector_intrinsics::vec256 = r5.1[2usize];
        let r53: crate::lib::intvector_intrinsics::vec256 = r5.1[3usize];
        let r54: crate::lib::intvector_intrinsics::vec256 = r5.1[4usize];
        let f10: crate::lib::intvector_intrinsics::vec256 = (&mut e)[0usize];
        let f111: crate::lib::intvector_intrinsics::vec256 = (&mut e)[1usize];
        let f12: crate::lib::intvector_intrinsics::vec256 = (&mut e)[2usize];
        let f13: crate::lib::intvector_intrinsics::vec256 = (&mut e)[3usize];
        let f14: crate::lib::intvector_intrinsics::vec256 = (&mut e)[4usize];
        let a0: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
        let a1: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
        let a2: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
        let a3: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
        let a4: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
        let a01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a0, f10);
        let a11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a1, f111);
        let a21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a2, f12);
        let a31: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a3, f13);
        let a41: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(a4, f14);
        let a02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r0, a01);
        let a12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r1, a01);
        let a22: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r2, a01);
        let a32: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r3, a01);
        let a42: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_mul64(r4, a01);
        let a03: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a02,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a11)
            );
        let a13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a12,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a11)
            );
        let a23: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a22,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a11)
            );
        let a33: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a32,
                crate::lib::intvector_intrinsics::vec256_mul64(r2, a11)
            );
        let a43: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a42,
                crate::lib::intvector_intrinsics::vec256_mul64(r3, a11)
            );
        let a04: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a03,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a21)
            );
        let a14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a13,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a21)
            );
        let a24: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a23,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a21)
            );
        let a34: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a33,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a21)
            );
        let a44: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a43,
                crate::lib::intvector_intrinsics::vec256_mul64(r2, a21)
            );
        let a05: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a04,
                crate::lib::intvector_intrinsics::vec256_mul64(r52, a31)
            );
        let a15: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a14,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a31)
            );
        let a25: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a24,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a31)
            );
        let a35: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a34,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a31)
            );
        let a45: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a44,
                crate::lib::intvector_intrinsics::vec256_mul64(r1, a31)
            );
        let a06: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a05,
                crate::lib::intvector_intrinsics::vec256_mul64(r51, a41)
            );
        let a16: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a15,
                crate::lib::intvector_intrinsics::vec256_mul64(r52, a41)
            );
        let a26: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a25,
                crate::lib::intvector_intrinsics::vec256_mul64(r53, a41)
            );
        let a36: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a35,
                crate::lib::intvector_intrinsics::vec256_mul64(r54, a41)
            );
        let a46: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                a45,
                crate::lib::intvector_intrinsics::vec256_mul64(r0, a41)
            );
        let t01: crate::lib::intvector_intrinsics::vec256 = a06;
        let t11: crate::lib::intvector_intrinsics::vec256 = a16;
        let t2: crate::lib::intvector_intrinsics::vec256 = a26;
        let t3: crate::lib::intvector_intrinsics::vec256 = a36;
        let t4: crate::lib::intvector_intrinsics::vec256 = a46;
        let mask26: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
        let z0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(t01, 26u32);
        let z1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(t3, 26u32);
        let x0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(t01, mask26);
        let x3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(t3, mask26);
        let x1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t11, z0);
        let x4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t4, z1);
        let z01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x1, 26u32);
        let z11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x4, 26u32);
        let t: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_left64(z11, 2u32);
        let z12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(z11, t);
        let x11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x1, mask26);
        let x41: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x4, mask26);
        let x2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(t2, z01);
        let x01: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x0, z12);
        let z02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x2, 26u32);
        let z13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x01, 26u32);
        let x21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x2, mask26);
        let x02: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x01, mask26);
        let x31: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x3, z02);
        let x12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x11, z13);
        let z03: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_shift_right64(x31, 26u32);
        let x32: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_and(x31, mask26);
        let x42: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(x41, z03);
        let o0: crate::lib::intvector_intrinsics::vec256 = x02;
        let o1: crate::lib::intvector_intrinsics::vec256 = x12;
        let o2: crate::lib::intvector_intrinsics::vec256 = x21;
        let o3: crate::lib::intvector_intrinsics::vec256 = x32;
        let o4: crate::lib::intvector_intrinsics::vec256 = x42;
        acc.1[0usize] = o0;
        acc.1[1usize] = o1;
        acc.1[2usize] = o2;
        acc.1[3usize] = o3;
        acc.1[4usize] = o4
    }
}

pub fn poly1305_finish(
    tag: &mut [u8],
    key: &mut [u8],
    ctx: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec256],
    &mut [crate::lib::intvector_intrinsics::vec256])
    =
        ctx.split_at_mut(0usize);
    let ks: (&mut [u8], &mut [u8]) = key.split_at_mut(16usize);
    let f0: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
    let f1: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
    let f2: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
    let f3: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
    let f4: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
    let l: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            f0,
            crate::lib::intvector_intrinsics::vec256_zero
        );
    let tmp0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l, 26u32);
    let l0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f1, c0);
    let tmp1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l0,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l0, 26u32);
    let l1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f2, c1);
    let tmp2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l1,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l1, 26u32);
    let l2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f3, c2);
    let tmp3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l2,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l2, 26u32);
    let l3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f4, c3);
    let tmp4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l3,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l3, 26u32);
    let f01: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            tmp0,
            crate::lib::intvector_intrinsics::vec256_smul64(c4, 5u64)
        );
    let f11: crate::lib::intvector_intrinsics::vec256 = tmp1;
    let f21: crate::lib::intvector_intrinsics::vec256 = tmp2;
    let f31: crate::lib::intvector_intrinsics::vec256 = tmp3;
    let f41: crate::lib::intvector_intrinsics::vec256 = tmp4;
    let l4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            f01,
            crate::lib::intvector_intrinsics::vec256_zero
        );
    let tmp00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l4,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c00: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l4, 26u32);
    let l5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f11, c00);
    let tmp10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l5,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l5, 26u32);
    let l6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f21, c10);
    let tmp20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l6,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l6, 26u32);
    let l7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f31, c20);
    let tmp30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l7,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l7, 26u32);
    let l8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(f41, c30);
    let tmp40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            l8,
            crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64)
        );
    let c40: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_shift_right64(l8, 26u32);
    let f02: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_add64(
            tmp00,
            crate::lib::intvector_intrinsics::vec256_smul64(c40, 5u64)
        );
    let f12: crate::lib::intvector_intrinsics::vec256 = tmp10;
    let f22: crate::lib::intvector_intrinsics::vec256 = tmp20;
    let f32: crate::lib::intvector_intrinsics::vec256 = tmp30;
    let f42: crate::lib::intvector_intrinsics::vec256 = tmp40;
    let mh: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3ffffffu64);
    let ml: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load64(0x3fffffbu64);
    let mask: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_eq64(f42, mh);
    let mask1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            mask,
            crate::lib::intvector_intrinsics::vec256_eq64(f32, mh)
        );
    let mask2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            mask1,
            crate::lib::intvector_intrinsics::vec256_eq64(f22, mh)
        );
    let mask3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            mask2,
            crate::lib::intvector_intrinsics::vec256_eq64(f12, mh)
        );
    let mask4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(
            mask3,
            crate::lib::intvector_intrinsics::vec256_lognot(
                crate::lib::intvector_intrinsics::vec256_gt64(ml, f02)
            )
        );
    let ph: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(mask4, mh);
    let pl: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_and(mask4, ml);
    let o0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_sub64(f02, pl);
    let o1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_sub64(f12, ph);
    let o2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_sub64(f22, ph);
    let o3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_sub64(f32, ph);
    let o4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_sub64(f42, ph);
    let f010: crate::lib::intvector_intrinsics::vec256 = o0;
    let f110: crate::lib::intvector_intrinsics::vec256 = o1;
    let f210: crate::lib::intvector_intrinsics::vec256 = o2;
    let f310: crate::lib::intvector_intrinsics::vec256 = o3;
    let f410: crate::lib::intvector_intrinsics::vec256 = o4;
    acc.1[0usize] = f010;
    acc.1[1usize] = f110;
    acc.1[2usize] = f210;
    acc.1[3usize] = f310;
    acc.1[4usize] = f410;
    let f00: crate::lib::intvector_intrinsics::vec256 = acc.1[0usize];
    let f10: crate::lib::intvector_intrinsics::vec256 = acc.1[1usize];
    let f20: crate::lib::intvector_intrinsics::vec256 = acc.1[2usize];
    let f30: crate::lib::intvector_intrinsics::vec256 = acc.1[3usize];
    let f40: crate::lib::intvector_intrinsics::vec256 = acc.1[4usize];
    let f011: u64 = crate::lib::intvector_intrinsics::vec256_extract64(f00, 0u32);
    let f111: u64 = crate::lib::intvector_intrinsics::vec256_extract64(f10, 0u32);
    let f211: u64 = crate::lib::intvector_intrinsics::vec256_extract64(f20, 0u32);
    let f311: u64 = crate::lib::intvector_intrinsics::vec256_extract64(f30, 0u32);
    let f411: u64 = crate::lib::intvector_intrinsics::vec256_extract64(f40, 0u32);
    let lo: u64 = f011 | f111.wrapping_shl(26u32) | f211.wrapping_shl(52u32);
    let hi: u64 = f211.wrapping_shr(12u32) | f311.wrapping_shl(14u32) | f411.wrapping_shl(40u32);
    let f100: u64 = lo;
    let f112: u64 = hi;
    let u: u64 = crate::lowstar::endianness::load64_le(&mut ks.1[0usize..]);
    let lo0: u64 = u;
    let u0: u64 = crate::lowstar::endianness::load64_le(&mut ks.1[8usize..]);
    let hi0: u64 = u0;
    let f200: u64 = lo0;
    let f212: u64 = hi0;
    let r0: u64 = f100.wrapping_add(f200);
    let r1: u64 = f112.wrapping_add(f212);
    let c: u64 = (r0 ^ (r0 ^ f200 | r0.wrapping_sub(f200) ^ f200)).wrapping_shr(63u32);
    let r11: u64 = r1.wrapping_add(c);
    let f300: u64 = r0;
    let f312: u64 = r11;
    crate::lowstar::endianness::store64_le(&mut tag[0usize..], f300);
    crate::lowstar::endianness::store64_le(&mut tag[8usize..], f312)
}

pub struct state_t
{
    pub block_state: Vec<crate::lib::intvector_intrinsics::vec256>,
    pub buf: Vec<u8>,
    pub total_len: u64,
    pub p_key: Vec<u8>
}

pub fn malloc(key: &mut [u8]) -> Vec<state_t>
{
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    let mut r1: Vec<crate::lib::intvector_intrinsics::vec256> =
        vec![crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let block_state: &mut [crate::lib::intvector_intrinsics::vec256] = &mut r1;
    poly1305_init(block_state, key);
    let mut k·: Vec<u8> = vec![0u8; 32usize];
    ((&mut k·)[0usize..32usize]).copy_from_slice(&key[0usize..32usize]);
    let k·0: &mut [u8] = &mut k·;
    let mut s: state_t =
        state_t
        {
            block_state: block_state.to_vec(),
            buf: buf,
            total_len: 0u32 as u64,
            p_key: k·0.to_vec()
        };
    let mut p: Vec<state_t> =
        {
            let mut tmp: Vec<state_t> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset(state: &mut [state_t], key: &mut [u8]) -> ()
{
    let block_state: &mut [crate::lib::intvector_intrinsics::vec256] =
        &mut (state[0usize]).block_state;
    let k·: &mut [u8] = &mut (state[0usize]).p_key;
    poly1305_init(block_state, key);
    (k·[0usize..32usize]).copy_from_slice(&key[0usize..32usize]);
    let k·1: &mut [u8] = k·;
    (state[0usize]).total_len = 0u32 as u64;
    (state[0usize]).p_key = k·1.to_vec()
}

pub fn update(state: &mut [state_t], chunk: &mut [u8], chunk_len: u32) ->
    crate::hacl::streaming_types::error_code
{
    let block_state: &mut [crate::lib::intvector_intrinsics::vec256] =
        &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 0xffffffffu64.wrapping_sub(total_len)
    { crate::hacl::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
            { 64u32 }
            else
            { total_len.wrapping_rem(64u32 as u64) as u32 };
        if chunk_len <= 64u32.wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let k·1: &mut [u8] = &mut (state[0usize]).p_key;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2;
            (state[0usize]).p_key = k·1.to_vec()
        }
        else
        if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let k·1: &mut [u8] = &mut (state[0usize]).p_key;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz1 == 0u32) { poly1305_update(block_state, 64u32, buf) };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(64u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            poly1305_update(block_state, data1_len, data2.0);
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).p_key = k·1.to_vec()
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let k·1: &mut [u8] = &mut (state[0usize]).p_key;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            {
                (state[0usize]).total_len = total_len2;
                (state[0usize]).p_key = k·1.to_vec()
            };
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let k·10: &mut [u8] = &mut (state[0usize]).p_key;
            let sz10: u32 =
                if total_len10.wrapping_rem(64u32 as u64) == 0u64 && total_len10 > 0u64
                { 64u32 }
                else
                { total_len10.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz10 == 0u32) { poly1305_update(block_state, 64u32, buf0) };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) == 0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk2.1.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            poly1305_update(block_state, data1_len, data2.0);
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64);
            (state[0usize]).p_key = k·10.to_vec()
        };
        crate::hacl::streaming_types::error_code::Success
    }
}

pub fn digest(state: &mut [state_t], output: &mut [u8]) -> ()
{
    let block_state: &mut [crate::lib::intvector_intrinsics::vec256] =
        &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let k·: &mut [u8] = &mut (state[0usize]).p_key;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut r1: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let tmp_block_state: &mut [crate::lib::intvector_intrinsics::vec256] = &mut r1;
    (tmp_block_state[0usize..25usize]).copy_from_slice(&block_state[0usize..25usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(16u32) == 0u32 && r > 0u32 { 16u32 } else { r.wrapping_rem(16u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    let ite0: u32 =
        if r.wrapping_rem(16u32) == 0u32 && r > 0u32 { 16u32 } else { r.wrapping_rem(16u32) };
    poly1305_update(tmp_block_state, r.wrapping_sub(ite0), buf_last.0);
    let ite1: u32 =
        if r.wrapping_rem(16u32) == 0u32 && r > 0u32 { 16u32 } else { r.wrapping_rem(16u32) };
    poly1305_update(tmp_block_state, ite1, buf_last.1);
    let mut tmp: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    ((&mut tmp)[0usize..25usize]).copy_from_slice(&tmp_block_state[0usize..25usize]);
    poly1305_finish(output, k·, &mut tmp)
}

pub fn mac(output: &mut [u8], input: &mut [u8], input_len: u32, key: &mut [u8]) -> ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    poly1305_init(&mut ctx, key);
    poly1305_update(&mut ctx, input_len, input);
    poly1305_finish(output, key, &mut ctx)
}
