#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn load_acc2(acc: &mut [crate::lib::intvector_intrinsics::vec128], b: &mut [u8]) -> ()
{
    let mut e: [crate::lib::intvector_intrinsics::vec128; 5] =
        [crate::lib::intvector_intrinsics::vec128_zero; 5usize];
    let b1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64_le(&mut b[0usize..]);
    let b2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64_le(&mut b[16usize..]);
    let lo: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(b1, b2);
    let hi: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_high64(b1, b2);
    let f0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            lo,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            crate::lib::intvector_intrinsics::vec128_shift_right64(lo, 26u32),
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_or(
            crate::lib::intvector_intrinsics::vec128_shift_right64(lo, 52u32),
            crate::lib::intvector_intrinsics::vec128_shift_left64(
                crate::lib::intvector_intrinsics::vec128_and(
                    hi,
                    crate::lib::intvector_intrinsics::vec128_load64(0x3fffu64)
                ),
                12u32
            )
        );
    let f3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            crate::lib::intvector_intrinsics::vec128_shift_right64(hi, 14u32),
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(hi, 40u32);
    let f00: crate::lib::intvector_intrinsics::vec128 = f0;
    let f10: crate::lib::intvector_intrinsics::vec128 = f1;
    let f20: crate::lib::intvector_intrinsics::vec128 = f2;
    let f30: crate::lib::intvector_intrinsics::vec128 = f3;
    let f40: crate::lib::intvector_intrinsics::vec128 = f4;
    (&mut e)[0usize] = f00;
    (&mut e)[1usize] = f10;
    (&mut e)[2usize] = f20;
    (&mut e)[3usize] = f30;
    (&mut e)[4usize] = f40;
    let b10: u64 = 0x1000000u64;
    let mask: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(b10);
    let f41: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
    (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec128_or(f41, mask);
    let acc0: crate::lib::intvector_intrinsics::vec128 = acc[0usize];
    let acc1: crate::lib::intvector_intrinsics::vec128 = acc[1usize];
    let acc2: crate::lib::intvector_intrinsics::vec128 = acc[2usize];
    let acc3: crate::lib::intvector_intrinsics::vec128 = acc[3usize];
    let acc4: crate::lib::intvector_intrinsics::vec128 = acc[4usize];
    let e0: crate::lib::intvector_intrinsics::vec128 = (&mut e)[0usize];
    let e1: crate::lib::intvector_intrinsics::vec128 = (&mut e)[1usize];
    let e2: crate::lib::intvector_intrinsics::vec128 = (&mut e)[2usize];
    let e3: crate::lib::intvector_intrinsics::vec128 = (&mut e)[3usize];
    let e4: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
    let f01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_insert64(acc0, 0u64, 1u32);
    let f11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_insert64(acc1, 0u64, 1u32);
    let f21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_insert64(acc2, 0u64, 1u32);
    let f31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_insert64(acc3, 0u64, 1u32);
    let f42: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_insert64(acc4, 0u64, 1u32);
    let f010: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f01, e0);
    let f110: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f11, e1);
    let f210: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f21, e2);
    let f310: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f31, e3);
    let f410: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f42, e4);
    let acc01: crate::lib::intvector_intrinsics::vec128 = f010;
    let acc11: crate::lib::intvector_intrinsics::vec128 = f110;
    let acc21: crate::lib::intvector_intrinsics::vec128 = f210;
    let acc31: crate::lib::intvector_intrinsics::vec128 = f310;
    let acc41: crate::lib::intvector_intrinsics::vec128 = f410;
    acc[0usize] = acc01;
    acc[1usize] = acc11;
    acc[2usize] = acc21;
    acc[3usize] = acc31;
    acc[4usize] = acc41
}

pub fn fmul_r2_normalize(
    out: &mut [crate::lib::intvector_intrinsics::vec128],
    p: &mut [crate::lib::intvector_intrinsics::vec128]
) ->
    ()
{
    let
    r:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        p.split_at_mut(0usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r.1.split_at_mut(10usize);
    let a0: crate::lib::intvector_intrinsics::vec128 = out[0usize];
    let a1: crate::lib::intvector_intrinsics::vec128 = out[1usize];
    let a2: crate::lib::intvector_intrinsics::vec128 = out[2usize];
    let a3: crate::lib::intvector_intrinsics::vec128 = out[3usize];
    let a4: crate::lib::intvector_intrinsics::vec128 = out[4usize];
    let r10: crate::lib::intvector_intrinsics::vec128 = r2.0[0usize];
    let r11: crate::lib::intvector_intrinsics::vec128 = r2.0[1usize];
    let r12: crate::lib::intvector_intrinsics::vec128 = r2.0[2usize];
    let r13: crate::lib::intvector_intrinsics::vec128 = r2.0[3usize];
    let r14: crate::lib::intvector_intrinsics::vec128 = r2.0[4usize];
    let r20: crate::lib::intvector_intrinsics::vec128 = r2.1[0usize];
    let r21: crate::lib::intvector_intrinsics::vec128 = r2.1[1usize];
    let r22: crate::lib::intvector_intrinsics::vec128 = r2.1[2usize];
    let r23: crate::lib::intvector_intrinsics::vec128 = r2.1[3usize];
    let r24: crate::lib::intvector_intrinsics::vec128 = r2.1[4usize];
    let r201: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(r20, r10);
    let r211: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(r21, r11);
    let r221: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(r22, r12);
    let r231: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(r23, r13);
    let r241: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_interleave_low64(r24, r14);
    let r251: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_smul64(r211, 5u64);
    let r252: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_smul64(r221, 5u64);
    let r253: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_smul64(r231, 5u64);
    let r254: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_smul64(r241, 5u64);
    let a01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r201, a0);
    let a11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r211, a0);
    let a21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r221, a0);
    let a31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r231, a0);
    let a41: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r241, a0);
    let a02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a01,
            crate::lib::intvector_intrinsics::vec128_mul64(r254, a1)
        );
    let a12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a11,
            crate::lib::intvector_intrinsics::vec128_mul64(r201, a1)
        );
    let a22: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a21,
            crate::lib::intvector_intrinsics::vec128_mul64(r211, a1)
        );
    let a32: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a31,
            crate::lib::intvector_intrinsics::vec128_mul64(r221, a1)
        );
    let a42: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a41,
            crate::lib::intvector_intrinsics::vec128_mul64(r231, a1)
        );
    let a03: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a02,
            crate::lib::intvector_intrinsics::vec128_mul64(r253, a2)
        );
    let a13: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a12,
            crate::lib::intvector_intrinsics::vec128_mul64(r254, a2)
        );
    let a23: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a22,
            crate::lib::intvector_intrinsics::vec128_mul64(r201, a2)
        );
    let a33: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a32,
            crate::lib::intvector_intrinsics::vec128_mul64(r211, a2)
        );
    let a43: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a42,
            crate::lib::intvector_intrinsics::vec128_mul64(r221, a2)
        );
    let a04: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a03,
            crate::lib::intvector_intrinsics::vec128_mul64(r252, a3)
        );
    let a14: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a13,
            crate::lib::intvector_intrinsics::vec128_mul64(r253, a3)
        );
    let a24: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a23,
            crate::lib::intvector_intrinsics::vec128_mul64(r254, a3)
        );
    let a34: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a33,
            crate::lib::intvector_intrinsics::vec128_mul64(r201, a3)
        );
    let a44: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a43,
            crate::lib::intvector_intrinsics::vec128_mul64(r211, a3)
        );
    let a05: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a04,
            crate::lib::intvector_intrinsics::vec128_mul64(r251, a4)
        );
    let a15: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a14,
            crate::lib::intvector_intrinsics::vec128_mul64(r252, a4)
        );
    let a25: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a24,
            crate::lib::intvector_intrinsics::vec128_mul64(r253, a4)
        );
    let a35: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a34,
            crate::lib::intvector_intrinsics::vec128_mul64(r254, a4)
        );
    let a45: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a44,
            crate::lib::intvector_intrinsics::vec128_mul64(r201, a4)
        );
    let t0: crate::lib::intvector_intrinsics::vec128 = a05;
    let t1: crate::lib::intvector_intrinsics::vec128 = a15;
    let t2: crate::lib::intvector_intrinsics::vec128 = a25;
    let t3: crate::lib::intvector_intrinsics::vec128 = a35;
    let t4: crate::lib::intvector_intrinsics::vec128 = a45;
    let mask26: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
    let z0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(t0, 26u32);
    let z1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(t0, mask26);
    let x3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(t3, mask26);
    let x1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t1, z0);
    let x4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t4, z1);
    let z01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x4, 26u32);
    let t: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(z11, t);
    let x11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x1, mask26);
    let x41: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x4, mask26);
    let x2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t2, z01);
    let x01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x0, z12);
    let z02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x2, mask26);
    let x02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x01, mask26);
    let x31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x3, z02);
    let x12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x11, z13);
    let z03: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x31, mask26);
    let x42: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x41, z03);
    let o0: crate::lib::intvector_intrinsics::vec128 = x02;
    let o1: crate::lib::intvector_intrinsics::vec128 = x12;
    let o2: crate::lib::intvector_intrinsics::vec128 = x21;
    let o3: crate::lib::intvector_intrinsics::vec128 = x32;
    let o4: crate::lib::intvector_intrinsics::vec128 = x42;
    let o01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o0,
            crate::lib::intvector_intrinsics::vec128_interleave_high64(o0, o0)
        );
    let o11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o1,
            crate::lib::intvector_intrinsics::vec128_interleave_high64(o1, o1)
        );
    let o21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o2,
            crate::lib::intvector_intrinsics::vec128_interleave_high64(o2, o2)
        );
    let o31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o3,
            crate::lib::intvector_intrinsics::vec128_interleave_high64(o3, o3)
        );
    let o41: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o4,
            crate::lib::intvector_intrinsics::vec128_interleave_high64(o4, o4)
        );
    let l: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            o01,
            crate::lib::intvector_intrinsics::vec128_zero
        );
    let tmp0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l, 26u32);
    let l0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(o11, c0);
    let tmp1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l0,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l0, 26u32);
    let l1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(o21, c1);
    let tmp2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l1,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l1, 26u32);
    let l2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(o31, c2);
    let tmp3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l2,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l2, 26u32);
    let l3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(o41, c3);
    let tmp4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l3,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l3, 26u32);
    let o00: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            tmp0,
            crate::lib::intvector_intrinsics::vec128_smul64(c4, 5u64)
        );
    let o10: crate::lib::intvector_intrinsics::vec128 = tmp1;
    let o20: crate::lib::intvector_intrinsics::vec128 = tmp2;
    let o30: crate::lib::intvector_intrinsics::vec128 = tmp3;
    let o40: crate::lib::intvector_intrinsics::vec128 = tmp4;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

pub fn poly1305_init(ctx: &mut [crate::lib::intvector_intrinsics::vec128], key: &mut [u8]) ->
    ()
{
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        ctx.split_at_mut(0usize);
    let
    pre:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        acc.1.split_at_mut(5usize);
    let kr: (&mut [u8], &mut [u8]) = key.split_at_mut(0usize);
    pre.0[0usize] = crate::lib::intvector_intrinsics::vec128_zero;
    pre.0[1usize] = crate::lib::intvector_intrinsics::vec128_zero;
    pre.0[2usize] = crate::lib::intvector_intrinsics::vec128_zero;
    pre.0[3usize] = crate::lib::intvector_intrinsics::vec128_zero;
    pre.0[4usize] = crate::lib::intvector_intrinsics::vec128_zero;
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
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        pre.1.split_at_mut(0usize);
    let
    r5:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r.1.split_at_mut(5usize);
    let
    rn:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r5.1.split_at_mut(5usize);
    let
    rn_5:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        rn.1.split_at_mut(5usize);
    let r_vec0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(lo1);
    let r_vec1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(hi1);
    let f0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            r_vec0,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            crate::lib::intvector_intrinsics::vec128_shift_right64(r_vec0, 26u32),
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_or(
            crate::lib::intvector_intrinsics::vec128_shift_right64(r_vec0, 52u32),
            crate::lib::intvector_intrinsics::vec128_shift_left64(
                crate::lib::intvector_intrinsics::vec128_and(
                    r_vec1,
                    crate::lib::intvector_intrinsics::vec128_load64(0x3fffu64)
                ),
                12u32
            )
        );
    let f3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            crate::lib::intvector_intrinsics::vec128_shift_right64(r_vec1, 14u32),
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let f4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(r_vec1, 40u32);
    let f00: crate::lib::intvector_intrinsics::vec128 = f0;
    let f10: crate::lib::intvector_intrinsics::vec128 = f1;
    let f20: crate::lib::intvector_intrinsics::vec128 = f2;
    let f30: crate::lib::intvector_intrinsics::vec128 = f3;
    let f40: crate::lib::intvector_intrinsics::vec128 = f4;
    r5.0[0usize] = f00;
    r5.0[1usize] = f10;
    r5.0[2usize] = f20;
    r5.0[3usize] = f30;
    r5.0[4usize] = f40;
    let f200: crate::lib::intvector_intrinsics::vec128 = r5.0[0usize];
    let f21: crate::lib::intvector_intrinsics::vec128 = r5.0[1usize];
    let f22: crate::lib::intvector_intrinsics::vec128 = r5.0[2usize];
    let f23: crate::lib::intvector_intrinsics::vec128 = r5.0[3usize];
    let f24: crate::lib::intvector_intrinsics::vec128 = r5.0[4usize];
    rn.0[0usize] = crate::lib::intvector_intrinsics::vec128_smul64(f200, 5u64);
    rn.0[1usize] = crate::lib::intvector_intrinsics::vec128_smul64(f21, 5u64);
    rn.0[2usize] = crate::lib::intvector_intrinsics::vec128_smul64(f22, 5u64);
    rn.0[3usize] = crate::lib::intvector_intrinsics::vec128_smul64(f23, 5u64);
    rn.0[4usize] = crate::lib::intvector_intrinsics::vec128_smul64(f24, 5u64);
    let r0: crate::lib::intvector_intrinsics::vec128 = r5.0[0usize];
    let r1: crate::lib::intvector_intrinsics::vec128 = r5.0[1usize];
    let r2: crate::lib::intvector_intrinsics::vec128 = r5.0[2usize];
    let r3: crate::lib::intvector_intrinsics::vec128 = r5.0[3usize];
    let r4: crate::lib::intvector_intrinsics::vec128 = r5.0[4usize];
    let r51: crate::lib::intvector_intrinsics::vec128 = rn.0[1usize];
    let r52: crate::lib::intvector_intrinsics::vec128 = rn.0[2usize];
    let r53: crate::lib::intvector_intrinsics::vec128 = rn.0[3usize];
    let r54: crate::lib::intvector_intrinsics::vec128 = rn.0[4usize];
    let f100: crate::lib::intvector_intrinsics::vec128 = r5.0[0usize];
    let f11: crate::lib::intvector_intrinsics::vec128 = r5.0[1usize];
    let f12: crate::lib::intvector_intrinsics::vec128 = r5.0[2usize];
    let f13: crate::lib::intvector_intrinsics::vec128 = r5.0[3usize];
    let f14: crate::lib::intvector_intrinsics::vec128 = r5.0[4usize];
    let a0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r0, f100);
    let a1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r1, f100);
    let a2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r2, f100);
    let a3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r3, f100);
    let a4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_mul64(r4, f100);
    let a01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a0,
            crate::lib::intvector_intrinsics::vec128_mul64(r54, f11)
        );
    let a11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a1,
            crate::lib::intvector_intrinsics::vec128_mul64(r0, f11)
        );
    let a21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a2,
            crate::lib::intvector_intrinsics::vec128_mul64(r1, f11)
        );
    let a31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a3,
            crate::lib::intvector_intrinsics::vec128_mul64(r2, f11)
        );
    let a41: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a4,
            crate::lib::intvector_intrinsics::vec128_mul64(r3, f11)
        );
    let a02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a01,
            crate::lib::intvector_intrinsics::vec128_mul64(r53, f12)
        );
    let a12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a11,
            crate::lib::intvector_intrinsics::vec128_mul64(r54, f12)
        );
    let a22: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a21,
            crate::lib::intvector_intrinsics::vec128_mul64(r0, f12)
        );
    let a32: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a31,
            crate::lib::intvector_intrinsics::vec128_mul64(r1, f12)
        );
    let a42: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a41,
            crate::lib::intvector_intrinsics::vec128_mul64(r2, f12)
        );
    let a03: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a02,
            crate::lib::intvector_intrinsics::vec128_mul64(r52, f13)
        );
    let a13: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a12,
            crate::lib::intvector_intrinsics::vec128_mul64(r53, f13)
        );
    let a23: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a22,
            crate::lib::intvector_intrinsics::vec128_mul64(r54, f13)
        );
    let a33: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a32,
            crate::lib::intvector_intrinsics::vec128_mul64(r0, f13)
        );
    let a43: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a42,
            crate::lib::intvector_intrinsics::vec128_mul64(r1, f13)
        );
    let a04: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a03,
            crate::lib::intvector_intrinsics::vec128_mul64(r51, f14)
        );
    let a14: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a13,
            crate::lib::intvector_intrinsics::vec128_mul64(r52, f14)
        );
    let a24: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a23,
            crate::lib::intvector_intrinsics::vec128_mul64(r53, f14)
        );
    let a34: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a33,
            crate::lib::intvector_intrinsics::vec128_mul64(r54, f14)
        );
    let a44: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            a43,
            crate::lib::intvector_intrinsics::vec128_mul64(r0, f14)
        );
    let t0: crate::lib::intvector_intrinsics::vec128 = a04;
    let t1: crate::lib::intvector_intrinsics::vec128 = a14;
    let t2: crate::lib::intvector_intrinsics::vec128 = a24;
    let t3: crate::lib::intvector_intrinsics::vec128 = a34;
    let t4: crate::lib::intvector_intrinsics::vec128 = a44;
    let mask26: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
    let z0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(t0, 26u32);
    let z1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(t0, mask26);
    let x3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(t3, mask26);
    let x1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t1, z0);
    let x4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t4, z1);
    let z01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x4, 26u32);
    let t: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(z11, t);
    let x11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x1, mask26);
    let x41: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x4, mask26);
    let x2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(t2, z01);
    let x01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x0, z12);
    let z02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x2, mask26);
    let x02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x01, mask26);
    let x31: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x3, z02);
    let x12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x11, z13);
    let z03: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(x31, mask26);
    let x42: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(x41, z03);
    let o0: crate::lib::intvector_intrinsics::vec128 = x02;
    let o1: crate::lib::intvector_intrinsics::vec128 = x12;
    let o2: crate::lib::intvector_intrinsics::vec128 = x21;
    let o3: crate::lib::intvector_intrinsics::vec128 = x32;
    let o4: crate::lib::intvector_intrinsics::vec128 = x42;
    rn_5.0[0usize] = o0;
    rn_5.0[1usize] = o1;
    rn_5.0[2usize] = o2;
    rn_5.0[3usize] = o3;
    rn_5.0[4usize] = o4;
    let f201: crate::lib::intvector_intrinsics::vec128 = rn_5.0[0usize];
    let f210: crate::lib::intvector_intrinsics::vec128 = rn_5.0[1usize];
    let f220: crate::lib::intvector_intrinsics::vec128 = rn_5.0[2usize];
    let f230: crate::lib::intvector_intrinsics::vec128 = rn_5.0[3usize];
    let f240: crate::lib::intvector_intrinsics::vec128 = rn_5.0[4usize];
    rn_5.1[0usize] = crate::lib::intvector_intrinsics::vec128_smul64(f201, 5u64);
    rn_5.1[1usize] = crate::lib::intvector_intrinsics::vec128_smul64(f210, 5u64);
    rn_5.1[2usize] = crate::lib::intvector_intrinsics::vec128_smul64(f220, 5u64);
    rn_5.1[3usize] = crate::lib::intvector_intrinsics::vec128_smul64(f230, 5u64);
    rn_5.1[4usize] = crate::lib::intvector_intrinsics::vec128_smul64(f240, 5u64)
}

fn poly1305_update(
    ctx: &mut [crate::lib::intvector_intrinsics::vec128],
    len: u32,
    text: &mut [u8]
) ->
    ()
{
    let
    pre:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        ctx.split_at_mut(5usize);
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        pre.0.split_at_mut(0usize);
    let sz_block: u32 = 32u32;
    let len0: u32 = len.wrapping_div(sz_block).wrapping_mul(sz_block);
    let t0: (&mut [u8], &mut [u8]) = text.split_at_mut(0usize);
    if len0 > 0u32
    {
        let bs: u32 = 32u32;
        let text0: (&mut [u8], &mut [u8]) = t0.1.split_at_mut(0usize);
        load_acc2(acc.1, text0.1);
        let len1: u32 = len0.wrapping_sub(bs);
        let text1: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(bs as usize);
        let nb: u32 = len1.wrapping_div(bs);
        for i in 0u32..nb
        {
            let block: (&mut [u8], &mut [u8]) = text1.1.split_at_mut(i.wrapping_mul(bs) as usize);
            let mut e: [crate::lib::intvector_intrinsics::vec128; 5] =
                [crate::lib::intvector_intrinsics::vec128_zero; 5usize];
            let b1: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load64_le(&mut block.1[0usize..]);
            let b2: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load64_le(&mut block.1[16usize..]);
            let lo: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_interleave_low64(b1, b2);
            let hi: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_interleave_high64(b1, b2);
            let f0: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(
                    lo,
                    crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
                );
            let f1: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(
                    crate::lib::intvector_intrinsics::vec128_shift_right64(lo, 26u32),
                    crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
                );
            let f2: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_or(
                    crate::lib::intvector_intrinsics::vec128_shift_right64(lo, 52u32),
                    crate::lib::intvector_intrinsics::vec128_shift_left64(
                        crate::lib::intvector_intrinsics::vec128_and(
                            hi,
                            crate::lib::intvector_intrinsics::vec128_load64(0x3fffu64)
                        ),
                        12u32
                    )
                );
            let f3: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(
                    crate::lib::intvector_intrinsics::vec128_shift_right64(hi, 14u32),
                    crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
                );
            let f4: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(hi, 40u32);
            let f00: crate::lib::intvector_intrinsics::vec128 = f0;
            let f10: crate::lib::intvector_intrinsics::vec128 = f1;
            let f20: crate::lib::intvector_intrinsics::vec128 = f2;
            let f30: crate::lib::intvector_intrinsics::vec128 = f3;
            let f40: crate::lib::intvector_intrinsics::vec128 = f4;
            (&mut e)[0usize] = f00;
            (&mut e)[1usize] = f10;
            (&mut e)[2usize] = f20;
            (&mut e)[3usize] = f30;
            (&mut e)[4usize] = f40;
            let b: u64 = 0x1000000u64;
            let mask: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load64(b);
            let f41: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
            (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec128_or(f41, mask);
            let
            rn:
            (&mut [crate::lib::intvector_intrinsics::vec128],
            &mut [crate::lib::intvector_intrinsics::vec128])
            =
                pre.1.split_at_mut(10usize);
            let
            rn5:
            (&mut [crate::lib::intvector_intrinsics::vec128],
            &mut [crate::lib::intvector_intrinsics::vec128])
            =
                rn.1.split_at_mut(5usize);
            let r0: crate::lib::intvector_intrinsics::vec128 = rn5.0[0usize];
            let r1: crate::lib::intvector_intrinsics::vec128 = rn5.0[1usize];
            let r2: crate::lib::intvector_intrinsics::vec128 = rn5.0[2usize];
            let r3: crate::lib::intvector_intrinsics::vec128 = rn5.0[3usize];
            let r4: crate::lib::intvector_intrinsics::vec128 = rn5.0[4usize];
            let r51: crate::lib::intvector_intrinsics::vec128 = rn5.1[1usize];
            let r52: crate::lib::intvector_intrinsics::vec128 = rn5.1[2usize];
            let r53: crate::lib::intvector_intrinsics::vec128 = rn5.1[3usize];
            let r54: crate::lib::intvector_intrinsics::vec128 = rn5.1[4usize];
            let f100: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
            let f11: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
            let f12: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
            let f13: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
            let f14: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
            let a0: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_mul64(r0, f100);
            let a1: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_mul64(r1, f100);
            let a2: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_mul64(r2, f100);
            let a3: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_mul64(r3, f100);
            let a4: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_mul64(r4, f100);
            let a01: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a0,
                    crate::lib::intvector_intrinsics::vec128_mul64(r54, f11)
                );
            let a11: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a1,
                    crate::lib::intvector_intrinsics::vec128_mul64(r0, f11)
                );
            let a21: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a2,
                    crate::lib::intvector_intrinsics::vec128_mul64(r1, f11)
                );
            let a31: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a3,
                    crate::lib::intvector_intrinsics::vec128_mul64(r2, f11)
                );
            let a41: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a4,
                    crate::lib::intvector_intrinsics::vec128_mul64(r3, f11)
                );
            let a02: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a01,
                    crate::lib::intvector_intrinsics::vec128_mul64(r53, f12)
                );
            let a12: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a11,
                    crate::lib::intvector_intrinsics::vec128_mul64(r54, f12)
                );
            let a22: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a21,
                    crate::lib::intvector_intrinsics::vec128_mul64(r0, f12)
                );
            let a32: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a31,
                    crate::lib::intvector_intrinsics::vec128_mul64(r1, f12)
                );
            let a42: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a41,
                    crate::lib::intvector_intrinsics::vec128_mul64(r2, f12)
                );
            let a03: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a02,
                    crate::lib::intvector_intrinsics::vec128_mul64(r52, f13)
                );
            let a13: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a12,
                    crate::lib::intvector_intrinsics::vec128_mul64(r53, f13)
                );
            let a23: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a22,
                    crate::lib::intvector_intrinsics::vec128_mul64(r54, f13)
                );
            let a33: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a32,
                    crate::lib::intvector_intrinsics::vec128_mul64(r0, f13)
                );
            let a43: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a42,
                    crate::lib::intvector_intrinsics::vec128_mul64(r1, f13)
                );
            let a04: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a03,
                    crate::lib::intvector_intrinsics::vec128_mul64(r51, f14)
                );
            let a14: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a13,
                    crate::lib::intvector_intrinsics::vec128_mul64(r52, f14)
                );
            let a24: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a23,
                    crate::lib::intvector_intrinsics::vec128_mul64(r53, f14)
                );
            let a34: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a33,
                    crate::lib::intvector_intrinsics::vec128_mul64(r54, f14)
                );
            let a44: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(
                    a43,
                    crate::lib::intvector_intrinsics::vec128_mul64(r0, f14)
                );
            let t01: crate::lib::intvector_intrinsics::vec128 = a04;
            let t1: crate::lib::intvector_intrinsics::vec128 = a14;
            let t2: crate::lib::intvector_intrinsics::vec128 = a24;
            let t3: crate::lib::intvector_intrinsics::vec128 = a34;
            let t4: crate::lib::intvector_intrinsics::vec128 = a44;
            let mask26: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
            let z0: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(t01, 26u32);
            let z1: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(t3, 26u32);
            let x0: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(t01, mask26);
            let x3: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(t3, mask26);
            let x1: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(t1, z0);
            let x4: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(t4, z1);
            let z01: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(x1, 26u32);
            let z11: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(x4, 26u32);
            let t: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_left64(z11, 2u32);
            let z12: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(z11, t);
            let x11: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(x1, mask26);
            let x41: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(x4, mask26);
            let x2: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(t2, z01);
            let x01: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(x0, z12);
            let z02: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(x2, 26u32);
            let z13: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(x01, 26u32);
            let x21: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(x2, mask26);
            let x02: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(x01, mask26);
            let x31: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(x3, z02);
            let x12: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(x11, z13);
            let z03: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_shift_right64(x31, 26u32);
            let x32: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_and(x31, mask26);
            let x42: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(x41, z03);
            let o0: crate::lib::intvector_intrinsics::vec128 = x02;
            let o1: crate::lib::intvector_intrinsics::vec128 = x12;
            let o2: crate::lib::intvector_intrinsics::vec128 = x21;
            let o3: crate::lib::intvector_intrinsics::vec128 = x32;
            let o4: crate::lib::intvector_intrinsics::vec128 = x42;
            acc.1[0usize] = o0;
            acc.1[1usize] = o1;
            acc.1[2usize] = o2;
            acc.1[3usize] = o3;
            acc.1[4usize] = o4;
            let f101: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
            let f110: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
            let f120: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
            let f130: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
            let f140: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
            let f200: crate::lib::intvector_intrinsics::vec128 = (&mut e)[0usize];
            let f21: crate::lib::intvector_intrinsics::vec128 = (&mut e)[1usize];
            let f22: crate::lib::intvector_intrinsics::vec128 = (&mut e)[2usize];
            let f23: crate::lib::intvector_intrinsics::vec128 = (&mut e)[3usize];
            let f24: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
            let o00: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(f101, f200);
            let o10: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(f110, f21);
            let o20: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(f120, f22);
            let o30: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(f130, f23);
            let o40: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_add64(f140, f24);
            acc.1[0usize] = o00;
            acc.1[1usize] = o10;
            acc.1[2usize] = o20;
            acc.1[3usize] = o30;
            acc.1[4usize] = o40
        };
        fmul_r2_normalize(acc.1, pre.1)
    };
    let len1: u32 = len.wrapping_sub(len0);
    let t1: (&mut [u8], &mut [u8]) = t0.1.split_at_mut(len0 as usize);
    let nb: u32 = len1.wrapping_div(16u32);
    let rem: u32 = len1.wrapping_rem(16u32);
    for i in 0u32..nb
    {
        let block: (&mut [u8], &mut [u8]) = t1.1.split_at_mut(i.wrapping_mul(16u32) as usize);
        let mut e: [crate::lib::intvector_intrinsics::vec128; 5] =
            [crate::lib::intvector_intrinsics::vec128_zero; 5usize];
        let u: u64 = crate::lowstar::endianness::load64_le(&mut block.1[0usize..]);
        let lo: u64 = u;
        let u0: u64 = crate::lowstar::endianness::load64_le(&mut block.1[8usize..]);
        let hi: u64 = u0;
        let f0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(lo);
        let f1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(hi);
        let f01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                f0,
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f0, 26u32),
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_or(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f0, 52u32),
                crate::lib::intvector_intrinsics::vec128_shift_left64(
                    crate::lib::intvector_intrinsics::vec128_and(
                        f1,
                        crate::lib::intvector_intrinsics::vec128_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f1, 14u32),
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f4: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(f1, 40u32);
        let f010: crate::lib::intvector_intrinsics::vec128 = f01;
        let f110: crate::lib::intvector_intrinsics::vec128 = f11;
        let f20: crate::lib::intvector_intrinsics::vec128 = f2;
        let f30: crate::lib::intvector_intrinsics::vec128 = f3;
        let f40: crate::lib::intvector_intrinsics::vec128 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 0x1000000u64;
        let mask: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(b);
        let f41: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
        (&mut e)[4usize] = crate::lib::intvector_intrinsics::vec128_or(f41, mask);
        let
        r:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            pre.1.split_at_mut(0usize);
        let
        r5:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r.1.split_at_mut(5usize);
        let r0: crate::lib::intvector_intrinsics::vec128 = r5.0[0usize];
        let r1: crate::lib::intvector_intrinsics::vec128 = r5.0[1usize];
        let r2: crate::lib::intvector_intrinsics::vec128 = r5.0[2usize];
        let r3: crate::lib::intvector_intrinsics::vec128 = r5.0[3usize];
        let r4: crate::lib::intvector_intrinsics::vec128 = r5.0[4usize];
        let r51: crate::lib::intvector_intrinsics::vec128 = r5.1[1usize];
        let r52: crate::lib::intvector_intrinsics::vec128 = r5.1[2usize];
        let r53: crate::lib::intvector_intrinsics::vec128 = r5.1[3usize];
        let r54: crate::lib::intvector_intrinsics::vec128 = r5.1[4usize];
        let f10: crate::lib::intvector_intrinsics::vec128 = (&mut e)[0usize];
        let f111: crate::lib::intvector_intrinsics::vec128 = (&mut e)[1usize];
        let f12: crate::lib::intvector_intrinsics::vec128 = (&mut e)[2usize];
        let f13: crate::lib::intvector_intrinsics::vec128 = (&mut e)[3usize];
        let f14: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
        let a0: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
        let a1: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
        let a2: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
        let a3: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
        let a4: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
        let a01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a0, f10);
        let a11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a1, f111);
        let a21: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a2, f12);
        let a31: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a3, f13);
        let a41: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a4, f14);
        let a02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r0, a01);
        let a12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r1, a01);
        let a22: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r2, a01);
        let a32: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r3, a01);
        let a42: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r4, a01);
        let a03: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a02,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a11)
            );
        let a13: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a12,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a11)
            );
        let a23: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a22,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a11)
            );
        let a33: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a32,
                crate::lib::intvector_intrinsics::vec128_mul64(r2, a11)
            );
        let a43: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a42,
                crate::lib::intvector_intrinsics::vec128_mul64(r3, a11)
            );
        let a04: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a03,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a21)
            );
        let a14: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a13,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a21)
            );
        let a24: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a23,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a21)
            );
        let a34: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a33,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a21)
            );
        let a44: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a43,
                crate::lib::intvector_intrinsics::vec128_mul64(r2, a21)
            );
        let a05: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a04,
                crate::lib::intvector_intrinsics::vec128_mul64(r52, a31)
            );
        let a15: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a14,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a31)
            );
        let a25: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a24,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a31)
            );
        let a35: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a34,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a31)
            );
        let a45: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a44,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a31)
            );
        let a06: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a05,
                crate::lib::intvector_intrinsics::vec128_mul64(r51, a41)
            );
        let a16: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a15,
                crate::lib::intvector_intrinsics::vec128_mul64(r52, a41)
            );
        let a26: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a25,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a41)
            );
        let a36: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a35,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a41)
            );
        let a46: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a45,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a41)
            );
        let t01: crate::lib::intvector_intrinsics::vec128 = a06;
        let t11: crate::lib::intvector_intrinsics::vec128 = a16;
        let t2: crate::lib::intvector_intrinsics::vec128 = a26;
        let t3: crate::lib::intvector_intrinsics::vec128 = a36;
        let t4: crate::lib::intvector_intrinsics::vec128 = a46;
        let mask26: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
        let z0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(t01, 26u32);
        let z1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(t3, 26u32);
        let x0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(t01, mask26);
        let x3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(t3, mask26);
        let x1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t11, z0);
        let x4: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t4, z1);
        let z01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x1, 26u32);
        let z11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x4, 26u32);
        let t: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_left64(z11, 2u32);
        let z12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(z11, t);
        let x11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x1, mask26);
        let x41: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x4, mask26);
        let x2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t2, z01);
        let x01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x0, z12);
        let z02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x2, 26u32);
        let z13: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x01, 26u32);
        let x21: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x2, mask26);
        let x02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x01, mask26);
        let x31: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x3, z02);
        let x12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x11, z13);
        let z03: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x31, 26u32);
        let x32: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x31, mask26);
        let x42: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x41, z03);
        let o0: crate::lib::intvector_intrinsics::vec128 = x02;
        let o1: crate::lib::intvector_intrinsics::vec128 = x12;
        let o2: crate::lib::intvector_intrinsics::vec128 = x21;
        let o3: crate::lib::intvector_intrinsics::vec128 = x32;
        let o4: crate::lib::intvector_intrinsics::vec128 = x42;
        acc.1[0usize] = o0;
        acc.1[1usize] = o1;
        acc.1[2usize] = o2;
        acc.1[3usize] = o3;
        acc.1[4usize] = o4
    };
    if rem > 0u32
    {
        let last: (&mut [u8], &mut [u8]) = t1.1.split_at_mut(nb.wrapping_mul(16u32) as usize);
        let mut e: [crate::lib::intvector_intrinsics::vec128; 5] =
            [crate::lib::intvector_intrinsics::vec128_zero; 5usize];
        let mut tmp: [u8; 16] = [0u8; 16usize];
        ((&mut tmp)[0usize..rem as usize]).copy_from_slice(&last.1[0usize..rem as usize]);
        let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[0usize..]);
        let lo: u64 = u;
        let u0: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[8usize..]);
        let hi: u64 = u0;
        let f0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(lo);
        let f1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(hi);
        let f01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                f0,
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f0, 26u32),
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_or(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f0, 52u32),
                crate::lib::intvector_intrinsics::vec128_shift_left64(
                    crate::lib::intvector_intrinsics::vec128_and(
                        f1,
                        crate::lib::intvector_intrinsics::vec128_load64(0x3fffu64)
                    ),
                    12u32
                )
            );
        let f3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(
                crate::lib::intvector_intrinsics::vec128_shift_right64(f1, 14u32),
                crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
            );
        let f4: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(f1, 40u32);
        let f010: crate::lib::intvector_intrinsics::vec128 = f01;
        let f110: crate::lib::intvector_intrinsics::vec128 = f11;
        let f20: crate::lib::intvector_intrinsics::vec128 = f2;
        let f30: crate::lib::intvector_intrinsics::vec128 = f3;
        let f40: crate::lib::intvector_intrinsics::vec128 = f4;
        (&mut e)[0usize] = f010;
        (&mut e)[1usize] = f110;
        (&mut e)[2usize] = f20;
        (&mut e)[3usize] = f30;
        (&mut e)[4usize] = f40;
        let b: u64 = 1u64.wrapping_shl(rem.wrapping_mul(8u32).wrapping_rem(26u32));
        let mask: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(b);
        let fi: crate::lib::intvector_intrinsics::vec128 =
            (&mut e)[rem.wrapping_mul(8u32).wrapping_div(26u32) as usize];
        (&mut e)[rem.wrapping_mul(8u32).wrapping_div(26u32) as usize] =
            crate::lib::intvector_intrinsics::vec128_or(fi, mask);
        let
        r:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            pre.1.split_at_mut(0usize);
        let
        r5:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r.1.split_at_mut(5usize);
        let r0: crate::lib::intvector_intrinsics::vec128 = r5.0[0usize];
        let r1: crate::lib::intvector_intrinsics::vec128 = r5.0[1usize];
        let r2: crate::lib::intvector_intrinsics::vec128 = r5.0[2usize];
        let r3: crate::lib::intvector_intrinsics::vec128 = r5.0[3usize];
        let r4: crate::lib::intvector_intrinsics::vec128 = r5.0[4usize];
        let r51: crate::lib::intvector_intrinsics::vec128 = r5.1[1usize];
        let r52: crate::lib::intvector_intrinsics::vec128 = r5.1[2usize];
        let r53: crate::lib::intvector_intrinsics::vec128 = r5.1[3usize];
        let r54: crate::lib::intvector_intrinsics::vec128 = r5.1[4usize];
        let f10: crate::lib::intvector_intrinsics::vec128 = (&mut e)[0usize];
        let f111: crate::lib::intvector_intrinsics::vec128 = (&mut e)[1usize];
        let f12: crate::lib::intvector_intrinsics::vec128 = (&mut e)[2usize];
        let f13: crate::lib::intvector_intrinsics::vec128 = (&mut e)[3usize];
        let f14: crate::lib::intvector_intrinsics::vec128 = (&mut e)[4usize];
        let a0: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
        let a1: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
        let a2: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
        let a3: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
        let a4: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
        let a01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a0, f10);
        let a11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a1, f111);
        let a21: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a2, f12);
        let a31: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a3, f13);
        let a41: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(a4, f14);
        let a02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r0, a01);
        let a12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r1, a01);
        let a22: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r2, a01);
        let a32: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r3, a01);
        let a42: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_mul64(r4, a01);
        let a03: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a02,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a11)
            );
        let a13: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a12,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a11)
            );
        let a23: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a22,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a11)
            );
        let a33: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a32,
                crate::lib::intvector_intrinsics::vec128_mul64(r2, a11)
            );
        let a43: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a42,
                crate::lib::intvector_intrinsics::vec128_mul64(r3, a11)
            );
        let a04: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a03,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a21)
            );
        let a14: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a13,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a21)
            );
        let a24: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a23,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a21)
            );
        let a34: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a33,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a21)
            );
        let a44: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a43,
                crate::lib::intvector_intrinsics::vec128_mul64(r2, a21)
            );
        let a05: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a04,
                crate::lib::intvector_intrinsics::vec128_mul64(r52, a31)
            );
        let a15: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a14,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a31)
            );
        let a25: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a24,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a31)
            );
        let a35: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a34,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a31)
            );
        let a45: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a44,
                crate::lib::intvector_intrinsics::vec128_mul64(r1, a31)
            );
        let a06: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a05,
                crate::lib::intvector_intrinsics::vec128_mul64(r51, a41)
            );
        let a16: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a15,
                crate::lib::intvector_intrinsics::vec128_mul64(r52, a41)
            );
        let a26: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a25,
                crate::lib::intvector_intrinsics::vec128_mul64(r53, a41)
            );
        let a36: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a35,
                crate::lib::intvector_intrinsics::vec128_mul64(r54, a41)
            );
        let a46: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(
                a45,
                crate::lib::intvector_intrinsics::vec128_mul64(r0, a41)
            );
        let t01: crate::lib::intvector_intrinsics::vec128 = a06;
        let t11: crate::lib::intvector_intrinsics::vec128 = a16;
        let t2: crate::lib::intvector_intrinsics::vec128 = a26;
        let t3: crate::lib::intvector_intrinsics::vec128 = a36;
        let t4: crate::lib::intvector_intrinsics::vec128 = a46;
        let mask26: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
        let z0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(t01, 26u32);
        let z1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(t3, 26u32);
        let x0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(t01, mask26);
        let x3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(t3, mask26);
        let x1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t11, z0);
        let x4: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t4, z1);
        let z01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x1, 26u32);
        let z11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x4, 26u32);
        let t: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_left64(z11, 2u32);
        let z12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(z11, t);
        let x11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x1, mask26);
        let x41: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x4, mask26);
        let x2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(t2, z01);
        let x01: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x0, z12);
        let z02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x2, 26u32);
        let z13: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x01, 26u32);
        let x21: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x2, mask26);
        let x02: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x01, mask26);
        let x31: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x3, z02);
        let x12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x11, z13);
        let z03: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_shift_right64(x31, 26u32);
        let x32: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_and(x31, mask26);
        let x42: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add64(x41, z03);
        let o0: crate::lib::intvector_intrinsics::vec128 = x02;
        let o1: crate::lib::intvector_intrinsics::vec128 = x12;
        let o2: crate::lib::intvector_intrinsics::vec128 = x21;
        let o3: crate::lib::intvector_intrinsics::vec128 = x32;
        let o4: crate::lib::intvector_intrinsics::vec128 = x42;
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
    ctx: &mut [crate::lib::intvector_intrinsics::vec128]
) ->
    ()
{
    let
    acc:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        ctx.split_at_mut(0usize);
    let ks: (&mut [u8], &mut [u8]) = key.split_at_mut(16usize);
    let f0: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
    let f1: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
    let f2: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
    let f3: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
    let f4: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
    let l: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            f0,
            crate::lib::intvector_intrinsics::vec128_zero
        );
    let tmp0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l, 26u32);
    let l0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f1, c0);
    let tmp1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l0,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l0, 26u32);
    let l1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f2, c1);
    let tmp2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l1,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l1, 26u32);
    let l2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f3, c2);
    let tmp3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l2,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l2, 26u32);
    let l3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f4, c3);
    let tmp4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l3,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l3, 26u32);
    let f01: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            tmp0,
            crate::lib::intvector_intrinsics::vec128_smul64(c4, 5u64)
        );
    let f11: crate::lib::intvector_intrinsics::vec128 = tmp1;
    let f21: crate::lib::intvector_intrinsics::vec128 = tmp2;
    let f31: crate::lib::intvector_intrinsics::vec128 = tmp3;
    let f41: crate::lib::intvector_intrinsics::vec128 = tmp4;
    let l4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            f01,
            crate::lib::intvector_intrinsics::vec128_zero
        );
    let tmp00: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l4,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c00: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l4, 26u32);
    let l5: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f11, c00);
    let tmp10: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l5,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c10: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l5, 26u32);
    let l6: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f21, c10);
    let tmp20: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l6,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c20: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l6, 26u32);
    let l7: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f31, c20);
    let tmp30: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l7,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c30: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l7, 26u32);
    let l8: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(f41, c30);
    let tmp40: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            l8,
            crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64)
        );
    let c40: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_shift_right64(l8, 26u32);
    let f02: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_add64(
            tmp00,
            crate::lib::intvector_intrinsics::vec128_smul64(c40, 5u64)
        );
    let f12: crate::lib::intvector_intrinsics::vec128 = tmp10;
    let f22: crate::lib::intvector_intrinsics::vec128 = tmp20;
    let f32: crate::lib::intvector_intrinsics::vec128 = tmp30;
    let f42: crate::lib::intvector_intrinsics::vec128 = tmp40;
    let mh: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(0x3ffffffu64);
    let ml: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load64(0x3fffffbu64);
    let mask: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_eq64(f42, mh);
    let mask1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            mask,
            crate::lib::intvector_intrinsics::vec128_eq64(f32, mh)
        );
    let mask2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            mask1,
            crate::lib::intvector_intrinsics::vec128_eq64(f22, mh)
        );
    let mask3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            mask2,
            crate::lib::intvector_intrinsics::vec128_eq64(f12, mh)
        );
    let mask4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(
            mask3,
            crate::lib::intvector_intrinsics::vec128_lognot(
                crate::lib::intvector_intrinsics::vec128_gt64(ml, f02)
            )
        );
    let ph: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(mask4, mh);
    let pl: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_and(mask4, ml);
    let o0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_sub64(f02, pl);
    let o1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_sub64(f12, ph);
    let o2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_sub64(f22, ph);
    let o3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_sub64(f32, ph);
    let o4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_sub64(f42, ph);
    let f010: crate::lib::intvector_intrinsics::vec128 = o0;
    let f110: crate::lib::intvector_intrinsics::vec128 = o1;
    let f210: crate::lib::intvector_intrinsics::vec128 = o2;
    let f310: crate::lib::intvector_intrinsics::vec128 = o3;
    let f410: crate::lib::intvector_intrinsics::vec128 = o4;
    acc.1[0usize] = f010;
    acc.1[1usize] = f110;
    acc.1[2usize] = f210;
    acc.1[3usize] = f310;
    acc.1[4usize] = f410;
    let f00: crate::lib::intvector_intrinsics::vec128 = acc.1[0usize];
    let f10: crate::lib::intvector_intrinsics::vec128 = acc.1[1usize];
    let f20: crate::lib::intvector_intrinsics::vec128 = acc.1[2usize];
    let f30: crate::lib::intvector_intrinsics::vec128 = acc.1[3usize];
    let f40: crate::lib::intvector_intrinsics::vec128 = acc.1[4usize];
    let f011: u64 = crate::lib::intvector_intrinsics::vec128_extract64(f00, 0u32);
    let f111: u64 = crate::lib::intvector_intrinsics::vec128_extract64(f10, 0u32);
    let f211: u64 = crate::lib::intvector_intrinsics::vec128_extract64(f20, 0u32);
    let f311: u64 = crate::lib::intvector_intrinsics::vec128_extract64(f30, 0u32);
    let f411: u64 = crate::lib::intvector_intrinsics::vec128_extract64(f40, 0u32);
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
    pub block_state: Vec<crate::lib::intvector_intrinsics::vec128>,
    pub buf: Vec<u8>,
    pub total_len: u64,
    pub p_key: Vec<u8>
}

pub fn malloc(key: &mut [u8]) -> Vec<state_t>
{
    let mut buf: Vec<u8> = vec![0u8; 32usize];
    let mut r1: Vec<crate::lib::intvector_intrinsics::vec128> =
        vec![crate::lib::intvector_intrinsics::vec128_zero; 25usize];
    let block_state: &mut [crate::lib::intvector_intrinsics::vec128] = &mut r1;
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
    let block_state: &mut [crate::lib::intvector_intrinsics::vec128] =
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
    let block_state: &mut [crate::lib::intvector_intrinsics::vec128] =
        &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 0xffffffffu64.wrapping_sub(total_len)
    { crate::hacl::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if total_len.wrapping_rem(32u32 as u64) == 0u64 && total_len > 0u64
            { 32u32 }
            else
            { total_len.wrapping_rem(32u32 as u64) as u32 };
        if chunk_len <= 32u32.wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let k·1: &mut [u8] = &mut (state[0usize]).p_key;
            let sz1: u32 =
                if total_len1.wrapping_rem(32u32 as u64) == 0u64 && total_len1 > 0u64
                { 32u32 }
                else
                { total_len1.wrapping_rem(32u32 as u64) as u32 };
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
                if total_len1.wrapping_rem(32u32 as u64) == 0u64 && total_len1 > 0u64
                { 32u32 }
                else
                { total_len1.wrapping_rem(32u32 as u64) as u32 };
            if ! (sz1 == 0u32) { poly1305_update(block_state, 32u32, buf) };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(32u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 32u32 }
                else
                { (chunk_len as u64).wrapping_rem(32u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(32u32);
            let data1_len: u32 = n_blocks.wrapping_mul(32u32);
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
            let diff: u32 = 32u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let k·1: &mut [u8] = &mut (state[0usize]).p_key;
            let sz1: u32 =
                if total_len1.wrapping_rem(32u32 as u64) == 0u64 && total_len1 > 0u64
                { 32u32 }
                else
                { total_len1.wrapping_rem(32u32 as u64) as u32 };
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
                if total_len10.wrapping_rem(32u32 as u64) == 0u64 && total_len10 > 0u64
                { 32u32 }
                else
                { total_len10.wrapping_rem(32u32 as u64) as u32 };
            if ! (sz10 == 0u32) { poly1305_update(block_state, 32u32, buf0) };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(32u32 as u64) == 0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { 32u32 }
                else
                { (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(32u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(32u32);
            let data1_len: u32 = n_blocks.wrapping_mul(32u32);
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
    let block_state: &mut [crate::lib::intvector_intrinsics::vec128] =
        &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let k·: &mut [u8] = &mut (state[0usize]).p_key;
    let r: u32 =
        if total_len.wrapping_rem(32u32 as u64) == 0u64 && total_len > 0u64
        { 32u32 }
        else
        { total_len.wrapping_rem(32u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut r1: [crate::lib::intvector_intrinsics::vec128; 25] =
        [crate::lib::intvector_intrinsics::vec128_zero; 25usize];
    let tmp_block_state: &mut [crate::lib::intvector_intrinsics::vec128] = &mut r1;
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
    let mut tmp: [crate::lib::intvector_intrinsics::vec128; 25] =
        [crate::lib::intvector_intrinsics::vec128_zero; 25usize];
    ((&mut tmp)[0usize..25usize]).copy_from_slice(&tmp_block_state[0usize..25usize]);
    poly1305_finish(output, k·, &mut tmp)
}

pub fn mac(output: &mut [u8], input: &mut [u8], input_len: u32, key: &mut [u8]) -> ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec128; 25] =
        [crate::lib::intvector_intrinsics::vec128_zero; 25usize];
    poly1305_init(&mut ctx, key);
    poly1305_update(&mut ctx, input_len, input);
    poly1305_finish(output, key, &mut ctx)
}
