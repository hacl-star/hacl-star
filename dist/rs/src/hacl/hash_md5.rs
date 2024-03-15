#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

const _h0: [u32; 4] = [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32];

const _t: [u32; 64] =
    [0xd76aa478u32, 0xe8c7b756u32, 0x242070dbu32, 0xc1bdceeeu32, 0xf57c0fafu32, 0x4787c62au32,
        0xa8304613u32, 0xfd469501u32, 0x698098d8u32, 0x8b44f7afu32, 0xffff5bb1u32, 0x895cd7beu32,
        0x6b901122u32, 0xfd987193u32, 0xa679438eu32, 0x49b40821u32, 0xf61e2562u32, 0xc040b340u32,
        0x265e5a51u32, 0xe9b6c7aau32, 0xd62f105du32, 0x02441453u32, 0xd8a1e681u32, 0xe7d3fbc8u32,
        0x21e1cde6u32, 0xc33707d6u32, 0xf4d50d87u32, 0x455a14edu32, 0xa9e3e905u32, 0xfcefa3f8u32,
        0x676f02d9u32, 0x8d2a4c8au32, 0xfffa3942u32, 0x8771f681u32, 0x6d9d6122u32, 0xfde5380cu32,
        0xa4beea44u32, 0x4bdecfa9u32, 0xf6bb4b60u32, 0xbebfbc70u32, 0x289b7ec6u32, 0xeaa127fau32,
        0xd4ef3085u32, 0x4881d05u32, 0xd9d4d039u32, 0xe6db99e5u32, 0x1fa27cf8u32, 0xc4ac5665u32,
        0xf4292244u32, 0x432aff97u32, 0xab9423a7u32, 0xfc93a039u32, 0x655b59c3u32, 0x8f0ccc92u32,
        0xffeff47du32, 0x85845dd1u32, 0x6fa87e4fu32, 0xfe2ce6e0u32, 0xa3014314u32, 0x4e0811a1u32,
        0xf7537e82u32, 0xbd3af235u32, 0x2ad7d2bbu32, 0xeb86d391u32];

pub fn init(s: &mut [u32]) -> ()
{ for i in 0u32..4u32 { s[i as usize] = (&mut _h0)[i as usize] } }

fn update(abcd: &mut [u32], x: &mut [u8]) -> ()
{
    let aa: u32 = abcd[0usize];
    let bb: u32 = abcd[1usize];
    let cc: u32 = abcd[2usize];
    let dd: u32 = abcd[3usize];
    let va: u32 = abcd[0usize];
    let vb: u32 = abcd[1usize];
    let vc: u32 = abcd[2usize];
    let vd: u32 = abcd[3usize];
    let b: (&mut [u8], &mut [u8]) = x.split_at_mut(0usize);
    let u: u32 = crate::lowstar::endianness::load32_le(b.1);
    let xk: u32 = u;
    let ti: u32 = (&mut _t)[0usize];
    let v: u32 =
        vb.wrapping_add(
            va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(
                7u32
            )
            |
            va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(
                25u32
            )
        );
    abcd[0usize] = v;
    let va0: u32 = abcd[3usize];
    let vb0: u32 = abcd[0usize];
    let vc0: u32 = abcd[1usize];
    let vd0: u32 = abcd[2usize];
    let b0: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
    let u0: u32 = crate::lowstar::endianness::load32_le(b0.1);
    let xk0: u32 = u0;
    let ti0: u32 = (&mut _t)[1usize];
    let v0: u32 =
        vb0.wrapping_add(
            va0.wrapping_add(vb0 & vc0 | ! vb0 & vd0).wrapping_add(xk0).wrapping_add(ti0).wrapping_shl(
                12u32
            )
            |
            va0.wrapping_add(vb0 & vc0 | ! vb0 & vd0).wrapping_add(xk0).wrapping_add(ti0).wrapping_shr(
                20u32
            )
        );
    abcd[3usize] = v0;
    let va1: u32 = abcd[2usize];
    let vb1: u32 = abcd[3usize];
    let vc1: u32 = abcd[0usize];
    let vd1: u32 = abcd[1usize];
    let b1: (&mut [u8], &mut [u8]) = b0.1.split_at_mut(4usize);
    let u1: u32 = crate::lowstar::endianness::load32_le(b1.1);
    let xk1: u32 = u1;
    let ti1: u32 = (&mut _t)[2usize];
    let v1: u32 =
        vb1.wrapping_add(
            va1.wrapping_add(vb1 & vc1 | ! vb1 & vd1).wrapping_add(xk1).wrapping_add(ti1).wrapping_shl(
                17u32
            )
            |
            va1.wrapping_add(vb1 & vc1 | ! vb1 & vd1).wrapping_add(xk1).wrapping_add(ti1).wrapping_shr(
                15u32
            )
        );
    abcd[2usize] = v1;
    let va2: u32 = abcd[1usize];
    let vb2: u32 = abcd[2usize];
    let vc2: u32 = abcd[3usize];
    let vd2: u32 = abcd[0usize];
    let b2: (&mut [u8], &mut [u8]) = b1.1.split_at_mut(4usize);
    let u2: u32 = crate::lowstar::endianness::load32_le(b2.1);
    let xk2: u32 = u2;
    let ti2: u32 = (&mut _t)[3usize];
    let v2: u32 =
        vb2.wrapping_add(
            va2.wrapping_add(vb2 & vc2 | ! vb2 & vd2).wrapping_add(xk2).wrapping_add(ti2).wrapping_shl(
                22u32
            )
            |
            va2.wrapping_add(vb2 & vc2 | ! vb2 & vd2).wrapping_add(xk2).wrapping_add(ti2).wrapping_shr(
                10u32
            )
        );
    abcd[1usize] = v2;
    let va3: u32 = abcd[0usize];
    let vb3: u32 = abcd[1usize];
    let vc3: u32 = abcd[2usize];
    let vd3: u32 = abcd[3usize];
    let b3: (&mut [u8], &mut [u8]) = b2.1.split_at_mut(4usize);
    let u3: u32 = crate::lowstar::endianness::load32_le(b3.1);
    let xk3: u32 = u3;
    let ti3: u32 = (&mut _t)[4usize];
    let v3: u32 =
        vb3.wrapping_add(
            va3.wrapping_add(vb3 & vc3 | ! vb3 & vd3).wrapping_add(xk3).wrapping_add(ti3).wrapping_shl(
                7u32
            )
            |
            va3.wrapping_add(vb3 & vc3 | ! vb3 & vd3).wrapping_add(xk3).wrapping_add(ti3).wrapping_shr(
                25u32
            )
        );
    abcd[0usize] = v3;
    let va4: u32 = abcd[3usize];
    let vb4: u32 = abcd[0usize];
    let vc4: u32 = abcd[1usize];
    let vd4: u32 = abcd[2usize];
    let b4: (&mut [u8], &mut [u8]) = b3.1.split_at_mut(4usize);
    let u4: u32 = crate::lowstar::endianness::load32_le(b4.1);
    let xk4: u32 = u4;
    let ti4: u32 = (&mut _t)[5usize];
    let v4: u32 =
        vb4.wrapping_add(
            va4.wrapping_add(vb4 & vc4 | ! vb4 & vd4).wrapping_add(xk4).wrapping_add(ti4).wrapping_shl(
                12u32
            )
            |
            va4.wrapping_add(vb4 & vc4 | ! vb4 & vd4).wrapping_add(xk4).wrapping_add(ti4).wrapping_shr(
                20u32
            )
        );
    abcd[3usize] = v4;
    let va5: u32 = abcd[2usize];
    let vb5: u32 = abcd[3usize];
    let vc5: u32 = abcd[0usize];
    let vd5: u32 = abcd[1usize];
    let b5: (&mut [u8], &mut [u8]) = b4.1.split_at_mut(4usize);
    let u5: u32 = crate::lowstar::endianness::load32_le(b5.1);
    let xk5: u32 = u5;
    let ti5: u32 = (&mut _t)[6usize];
    let v5: u32 =
        vb5.wrapping_add(
            va5.wrapping_add(vb5 & vc5 | ! vb5 & vd5).wrapping_add(xk5).wrapping_add(ti5).wrapping_shl(
                17u32
            )
            |
            va5.wrapping_add(vb5 & vc5 | ! vb5 & vd5).wrapping_add(xk5).wrapping_add(ti5).wrapping_shr(
                15u32
            )
        );
    abcd[2usize] = v5;
    let va6: u32 = abcd[1usize];
    let vb6: u32 = abcd[2usize];
    let vc6: u32 = abcd[3usize];
    let vd6: u32 = abcd[0usize];
    let b6: (&mut [u8], &mut [u8]) = b5.1.split_at_mut(4usize);
    let u6: u32 = crate::lowstar::endianness::load32_le(b6.1);
    let xk6: u32 = u6;
    let ti6: u32 = (&mut _t)[7usize];
    let v6: u32 =
        vb6.wrapping_add(
            va6.wrapping_add(vb6 & vc6 | ! vb6 & vd6).wrapping_add(xk6).wrapping_add(ti6).wrapping_shl(
                22u32
            )
            |
            va6.wrapping_add(vb6 & vc6 | ! vb6 & vd6).wrapping_add(xk6).wrapping_add(ti6).wrapping_shr(
                10u32
            )
        );
    abcd[1usize] = v6;
    let va7: u32 = abcd[0usize];
    let vb7: u32 = abcd[1usize];
    let vc7: u32 = abcd[2usize];
    let vd7: u32 = abcd[3usize];
    let b7: (&mut [u8], &mut [u8]) = b6.1.split_at_mut(4usize);
    let u7: u32 = crate::lowstar::endianness::load32_le(b7.1);
    let xk7: u32 = u7;
    let ti7: u32 = (&mut _t)[8usize];
    let v7: u32 =
        vb7.wrapping_add(
            va7.wrapping_add(vb7 & vc7 | ! vb7 & vd7).wrapping_add(xk7).wrapping_add(ti7).wrapping_shl(
                7u32
            )
            |
            va7.wrapping_add(vb7 & vc7 | ! vb7 & vd7).wrapping_add(xk7).wrapping_add(ti7).wrapping_shr(
                25u32
            )
        );
    abcd[0usize] = v7;
    let va8: u32 = abcd[3usize];
    let vb8: u32 = abcd[0usize];
    let vc8: u32 = abcd[1usize];
    let vd8: u32 = abcd[2usize];
    let b8: (&mut [u8], &mut [u8]) = b7.1.split_at_mut(4usize);
    let u8: u32 = crate::lowstar::endianness::load32_le(b8.1);
    let xk8: u32 = u8;
    let ti8: u32 = (&mut _t)[9usize];
    let v8: u32 =
        vb8.wrapping_add(
            va8.wrapping_add(vb8 & vc8 | ! vb8 & vd8).wrapping_add(xk8).wrapping_add(ti8).wrapping_shl(
                12u32
            )
            |
            va8.wrapping_add(vb8 & vc8 | ! vb8 & vd8).wrapping_add(xk8).wrapping_add(ti8).wrapping_shr(
                20u32
            )
        );
    abcd[3usize] = v8;
    let va9: u32 = abcd[2usize];
    let vb9: u32 = abcd[3usize];
    let vc9: u32 = abcd[0usize];
    let vd9: u32 = abcd[1usize];
    let b9: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(4usize);
    let u9: u32 = crate::lowstar::endianness::load32_le(b9.1);
    let xk9: u32 = u9;
    let ti9: u32 = (&mut _t)[10usize];
    let v9: u32 =
        vb9.wrapping_add(
            va9.wrapping_add(vb9 & vc9 | ! vb9 & vd9).wrapping_add(xk9).wrapping_add(ti9).wrapping_shl(
                17u32
            )
            |
            va9.wrapping_add(vb9 & vc9 | ! vb9 & vd9).wrapping_add(xk9).wrapping_add(ti9).wrapping_shr(
                15u32
            )
        );
    abcd[2usize] = v9;
    let va10: u32 = abcd[1usize];
    let vb10: u32 = abcd[2usize];
    let vc10: u32 = abcd[3usize];
    let vd10: u32 = abcd[0usize];
    let b10: (&mut [u8], &mut [u8]) = b9.1.split_at_mut(4usize);
    let u10: u32 = crate::lowstar::endianness::load32_le(b10.1);
    let xk10: u32 = u10;
    let ti10: u32 = (&mut _t)[11usize];
    let v10: u32 =
        vb10.wrapping_add(
            va10.wrapping_add(vb10 & vc10 | ! vb10 & vd10).wrapping_add(xk10).wrapping_add(ti10).wrapping_shl(
                22u32
            )
            |
            va10.wrapping_add(vb10 & vc10 | ! vb10 & vd10).wrapping_add(xk10).wrapping_add(ti10).wrapping_shr(
                10u32
            )
        );
    abcd[1usize] = v10;
    let va11: u32 = abcd[0usize];
    let vb11: u32 = abcd[1usize];
    let vc11: u32 = abcd[2usize];
    let vd11: u32 = abcd[3usize];
    let b11: (&mut [u8], &mut [u8]) = b10.1.split_at_mut(4usize);
    let u11: u32 = crate::lowstar::endianness::load32_le(b11.1);
    let xk11: u32 = u11;
    let ti11: u32 = (&mut _t)[12usize];
    let v11: u32 =
        vb11.wrapping_add(
            va11.wrapping_add(vb11 & vc11 | ! vb11 & vd11).wrapping_add(xk11).wrapping_add(ti11).wrapping_shl(
                7u32
            )
            |
            va11.wrapping_add(vb11 & vc11 | ! vb11 & vd11).wrapping_add(xk11).wrapping_add(ti11).wrapping_shr(
                25u32
            )
        );
    abcd[0usize] = v11;
    let va12: u32 = abcd[3usize];
    let vb12: u32 = abcd[0usize];
    let vc12: u32 = abcd[1usize];
    let vd12: u32 = abcd[2usize];
    let b12: (&mut [u8], &mut [u8]) = b11.1.split_at_mut(4usize);
    let u12: u32 = crate::lowstar::endianness::load32_le(b12.1);
    let xk12: u32 = u12;
    let ti12: u32 = (&mut _t)[13usize];
    let v12: u32 =
        vb12.wrapping_add(
            va12.wrapping_add(vb12 & vc12 | ! vb12 & vd12).wrapping_add(xk12).wrapping_add(ti12).wrapping_shl(
                12u32
            )
            |
            va12.wrapping_add(vb12 & vc12 | ! vb12 & vd12).wrapping_add(xk12).wrapping_add(ti12).wrapping_shr(
                20u32
            )
        );
    abcd[3usize] = v12;
    let va13: u32 = abcd[2usize];
    let vb13: u32 = abcd[3usize];
    let vc13: u32 = abcd[0usize];
    let vd13: u32 = abcd[1usize];
    let b13: (&mut [u8], &mut [u8]) = b12.1.split_at_mut(4usize);
    let u13: u32 = crate::lowstar::endianness::load32_le(b13.1);
    let xk13: u32 = u13;
    let ti13: u32 = (&mut _t)[14usize];
    let v13: u32 =
        vb13.wrapping_add(
            va13.wrapping_add(vb13 & vc13 | ! vb13 & vd13).wrapping_add(xk13).wrapping_add(ti13).wrapping_shl(
                17u32
            )
            |
            va13.wrapping_add(vb13 & vc13 | ! vb13 & vd13).wrapping_add(xk13).wrapping_add(ti13).wrapping_shr(
                15u32
            )
        );
    abcd[2usize] = v13;
    let va14: u32 = abcd[1usize];
    let vb14: u32 = abcd[2usize];
    let vc14: u32 = abcd[3usize];
    let vd14: u32 = abcd[0usize];
    let b14: (&mut [u8], &mut [u8]) = b13.1.split_at_mut(4usize);
    let u14: u32 = crate::lowstar::endianness::load32_le(b14.1);
    let xk14: u32 = u14;
    let ti14: u32 = (&mut _t)[15usize];
    let v14: u32 =
        vb14.wrapping_add(
            va14.wrapping_add(vb14 & vc14 | ! vb14 & vd14).wrapping_add(xk14).wrapping_add(ti14).wrapping_shl(
                22u32
            )
            |
            va14.wrapping_add(vb14 & vc14 | ! vb14 & vd14).wrapping_add(xk14).wrapping_add(ti14).wrapping_shr(
                10u32
            )
        );
    abcd[1usize] = v14;
    let va15: u32 = abcd[0usize];
    let vb15: u32 = abcd[1usize];
    let vc15: u32 = abcd[2usize];
    let vd15: u32 = abcd[3usize];
    let b15: (&mut [u8], &mut [u8]) = b1.0.split_at_mut(0usize);
    let u15: u32 = crate::lowstar::endianness::load32_le(b15.1);
    let xk15: u32 = u15;
    let ti15: u32 = (&mut _t)[16usize];
    let v15: u32 =
        vb15.wrapping_add(
            va15.wrapping_add(vb15 & vd15 | vc15 & ! vd15).wrapping_add(xk15).wrapping_add(ti15).wrapping_shl(
                5u32
            )
            |
            va15.wrapping_add(vb15 & vd15 | vc15 & ! vd15).wrapping_add(xk15).wrapping_add(ti15).wrapping_shr(
                27u32
            )
        );
    abcd[0usize] = v15;
    let va16: u32 = abcd[3usize];
    let vb16: u32 = abcd[0usize];
    let vc16: u32 = abcd[1usize];
    let vd16: u32 = abcd[2usize];
    let b16: (&mut [u8], &mut [u8]) = b6.0.split_at_mut(0usize);
    let u16: u32 = crate::lowstar::endianness::load32_le(b16.1);
    let xk16: u32 = u16;
    let ti16: u32 = (&mut _t)[17usize];
    let v16: u32 =
        vb16.wrapping_add(
            va16.wrapping_add(vb16 & vd16 | vc16 & ! vd16).wrapping_add(xk16).wrapping_add(ti16).wrapping_shl(
                9u32
            )
            |
            va16.wrapping_add(vb16 & vd16 | vc16 & ! vd16).wrapping_add(xk16).wrapping_add(ti16).wrapping_shr(
                23u32
            )
        );
    abcd[3usize] = v16;
    let va17: u32 = abcd[2usize];
    let vb17: u32 = abcd[3usize];
    let vc17: u32 = abcd[0usize];
    let vd17: u32 = abcd[1usize];
    let b17: (&mut [u8], &mut [u8]) = b11.0.split_at_mut(0usize);
    let u17: u32 = crate::lowstar::endianness::load32_le(b17.1);
    let xk17: u32 = u17;
    let ti17: u32 = (&mut _t)[18usize];
    let v17: u32 =
        vb17.wrapping_add(
            va17.wrapping_add(vb17 & vd17 | vc17 & ! vd17).wrapping_add(xk17).wrapping_add(ti17).wrapping_shl(
                14u32
            )
            |
            va17.wrapping_add(vb17 & vd17 | vc17 & ! vd17).wrapping_add(xk17).wrapping_add(ti17).wrapping_shr(
                18u32
            )
        );
    abcd[2usize] = v17;
    let va18: u32 = abcd[1usize];
    let vb18: u32 = abcd[2usize];
    let vc18: u32 = abcd[3usize];
    let vd18: u32 = abcd[0usize];
    let b18: (&mut [u8], &mut [u8]) = b0.0.split_at_mut(0usize);
    let u18: u32 = crate::lowstar::endianness::load32_le(b18.1);
    let xk18: u32 = u18;
    let ti18: u32 = (&mut _t)[19usize];
    let v18: u32 =
        vb18.wrapping_add(
            va18.wrapping_add(vb18 & vd18 | vc18 & ! vd18).wrapping_add(xk18).wrapping_add(ti18).wrapping_shl(
                20u32
            )
            |
            va18.wrapping_add(vb18 & vd18 | vc18 & ! vd18).wrapping_add(xk18).wrapping_add(ti18).wrapping_shr(
                12u32
            )
        );
    abcd[1usize] = v18;
    let va19: u32 = abcd[0usize];
    let vb19: u32 = abcd[1usize];
    let vc19: u32 = abcd[2usize];
    let vd19: u32 = abcd[3usize];
    let b19: (&mut [u8], &mut [u8]) = b5.0.split_at_mut(0usize);
    let u19: u32 = crate::lowstar::endianness::load32_le(b19.1);
    let xk19: u32 = u19;
    let ti19: u32 = (&mut _t)[20usize];
    let v19: u32 =
        vb19.wrapping_add(
            va19.wrapping_add(vb19 & vd19 | vc19 & ! vd19).wrapping_add(xk19).wrapping_add(ti19).wrapping_shl(
                5u32
            )
            |
            va19.wrapping_add(vb19 & vd19 | vc19 & ! vd19).wrapping_add(xk19).wrapping_add(ti19).wrapping_shr(
                27u32
            )
        );
    abcd[0usize] = v19;
    let va20: u32 = abcd[3usize];
    let vb20: u32 = abcd[0usize];
    let vc20: u32 = abcd[1usize];
    let vd20: u32 = abcd[2usize];
    let b20: (&mut [u8], &mut [u8]) = b10.0.split_at_mut(0usize);
    let u20: u32 = crate::lowstar::endianness::load32_le(b20.1);
    let xk20: u32 = u20;
    let ti20: u32 = (&mut _t)[21usize];
    let v20: u32 =
        vb20.wrapping_add(
            va20.wrapping_add(vb20 & vd20 | vc20 & ! vd20).wrapping_add(xk20).wrapping_add(ti20).wrapping_shl(
                9u32
            )
            |
            va20.wrapping_add(vb20 & vd20 | vc20 & ! vd20).wrapping_add(xk20).wrapping_add(ti20).wrapping_shr(
                23u32
            )
        );
    abcd[3usize] = v20;
    let va21: u32 = abcd[2usize];
    let vb21: u32 = abcd[3usize];
    let vc21: u32 = abcd[0usize];
    let vd21: u32 = abcd[1usize];
    let b21: (&mut [u8], &mut [u8]) = b14.1.split_at_mut(0usize);
    let u21: u32 = crate::lowstar::endianness::load32_le(b21.1);
    let xk21: u32 = u21;
    let ti21: u32 = (&mut _t)[22usize];
    let v21: u32 =
        vb21.wrapping_add(
            va21.wrapping_add(vb21 & vd21 | vc21 & ! vd21).wrapping_add(xk21).wrapping_add(ti21).wrapping_shl(
                14u32
            )
            |
            va21.wrapping_add(vb21 & vd21 | vc21 & ! vd21).wrapping_add(xk21).wrapping_add(ti21).wrapping_shr(
                18u32
            )
        );
    abcd[2usize] = v21;
    let va22: u32 = abcd[1usize];
    let vb22: u32 = abcd[2usize];
    let vc22: u32 = abcd[3usize];
    let vd22: u32 = abcd[0usize];
    let b22: (&mut [u8], &mut [u8]) = b4.0.split_at_mut(0usize);
    let u22: u32 = crate::lowstar::endianness::load32_le(b22.1);
    let xk22: u32 = u22;
    let ti22: u32 = (&mut _t)[23usize];
    let v22: u32 =
        vb22.wrapping_add(
            va22.wrapping_add(vb22 & vd22 | vc22 & ! vd22).wrapping_add(xk22).wrapping_add(ti22).wrapping_shl(
                20u32
            )
            |
            va22.wrapping_add(vb22 & vd22 | vc22 & ! vd22).wrapping_add(xk22).wrapping_add(ti22).wrapping_shr(
                12u32
            )
        );
    abcd[1usize] = v22;
    let va23: u32 = abcd[0usize];
    let vb23: u32 = abcd[1usize];
    let vc23: u32 = abcd[2usize];
    let vd23: u32 = abcd[3usize];
    let b23: (&mut [u8], &mut [u8]) = b9.0.split_at_mut(0usize);
    let u23: u32 = crate::lowstar::endianness::load32_le(b23.1);
    let xk23: u32 = u23;
    let ti23: u32 = (&mut _t)[24usize];
    let v23: u32 =
        vb23.wrapping_add(
            va23.wrapping_add(vb23 & vd23 | vc23 & ! vd23).wrapping_add(xk23).wrapping_add(ti23).wrapping_shl(
                5u32
            )
            |
            va23.wrapping_add(vb23 & vd23 | vc23 & ! vd23).wrapping_add(xk23).wrapping_add(ti23).wrapping_shr(
                27u32
            )
        );
    abcd[0usize] = v23;
    let va24: u32 = abcd[3usize];
    let vb24: u32 = abcd[0usize];
    let vc24: u32 = abcd[1usize];
    let vd24: u32 = abcd[2usize];
    let b24: (&mut [u8], &mut [u8]) = b14.0.split_at_mut(0usize);
    let u24: u32 = crate::lowstar::endianness::load32_le(b24.1);
    let xk24: u32 = u24;
    let ti24: u32 = (&mut _t)[25usize];
    let v24: u32 =
        vb24.wrapping_add(
            va24.wrapping_add(vb24 & vd24 | vc24 & ! vd24).wrapping_add(xk24).wrapping_add(ti24).wrapping_shl(
                9u32
            )
            |
            va24.wrapping_add(vb24 & vd24 | vc24 & ! vd24).wrapping_add(xk24).wrapping_add(ti24).wrapping_shr(
                23u32
            )
        );
    abcd[3usize] = v24;
    let va25: u32 = abcd[2usize];
    let vb25: u32 = abcd[3usize];
    let vc25: u32 = abcd[0usize];
    let vd25: u32 = abcd[1usize];
    let b25: (&mut [u8], &mut [u8]) = b3.0.split_at_mut(0usize);
    let u25: u32 = crate::lowstar::endianness::load32_le(b25.1);
    let xk25: u32 = u25;
    let ti25: u32 = (&mut _t)[26usize];
    let v25: u32 =
        vb25.wrapping_add(
            va25.wrapping_add(vb25 & vd25 | vc25 & ! vd25).wrapping_add(xk25).wrapping_add(ti25).wrapping_shl(
                14u32
            )
            |
            va25.wrapping_add(vb25 & vd25 | vc25 & ! vd25).wrapping_add(xk25).wrapping_add(ti25).wrapping_shr(
                18u32
            )
        );
    abcd[2usize] = v25;
    let va26: u32 = abcd[1usize];
    let vb26: u32 = abcd[2usize];
    let vc26: u32 = abcd[3usize];
    let vd26: u32 = abcd[0usize];
    let b26: (&mut [u8], &mut [u8]) = b8.0.split_at_mut(0usize);
    let u26: u32 = crate::lowstar::endianness::load32_le(b26.1);
    let xk26: u32 = u26;
    let ti26: u32 = (&mut _t)[27usize];
    let v26: u32 =
        vb26.wrapping_add(
            va26.wrapping_add(vb26 & vd26 | vc26 & ! vd26).wrapping_add(xk26).wrapping_add(ti26).wrapping_shl(
                20u32
            )
            |
            va26.wrapping_add(vb26 & vd26 | vc26 & ! vd26).wrapping_add(xk26).wrapping_add(ti26).wrapping_shr(
                12u32
            )
        );
    abcd[1usize] = v26;
    let va27: u32 = abcd[0usize];
    let vb27: u32 = abcd[1usize];
    let vc27: u32 = abcd[2usize];
    let vd27: u32 = abcd[3usize];
    let b27: (&mut [u8], &mut [u8]) = b13.0.split_at_mut(0usize);
    let u27: u32 = crate::lowstar::endianness::load32_le(b27.1);
    let xk27: u32 = u27;
    let ti27: u32 = (&mut _t)[28usize];
    let v27: u32 =
        vb27.wrapping_add(
            va27.wrapping_add(vb27 & vd27 | vc27 & ! vd27).wrapping_add(xk27).wrapping_add(ti27).wrapping_shl(
                5u32
            )
            |
            va27.wrapping_add(vb27 & vd27 | vc27 & ! vd27).wrapping_add(xk27).wrapping_add(ti27).wrapping_shr(
                27u32
            )
        );
    abcd[0usize] = v27;
    let va28: u32 = abcd[3usize];
    let vb28: u32 = abcd[0usize];
    let vc28: u32 = abcd[1usize];
    let vd28: u32 = abcd[2usize];
    let b28: (&mut [u8], &mut [u8]) = b2.0.split_at_mut(0usize);
    let u28: u32 = crate::lowstar::endianness::load32_le(b28.1);
    let xk28: u32 = u28;
    let ti28: u32 = (&mut _t)[29usize];
    let v28: u32 =
        vb28.wrapping_add(
            va28.wrapping_add(vb28 & vd28 | vc28 & ! vd28).wrapping_add(xk28).wrapping_add(ti28).wrapping_shl(
                9u32
            )
            |
            va28.wrapping_add(vb28 & vd28 | vc28 & ! vd28).wrapping_add(xk28).wrapping_add(ti28).wrapping_shr(
                23u32
            )
        );
    abcd[3usize] = v28;
    let va29: u32 = abcd[2usize];
    let vb29: u32 = abcd[3usize];
    let vc29: u32 = abcd[0usize];
    let vd29: u32 = abcd[1usize];
    let b29: (&mut [u8], &mut [u8]) = b7.0.split_at_mut(0usize);
    let u29: u32 = crate::lowstar::endianness::load32_le(b29.1);
    let xk29: u32 = u29;
    let ti29: u32 = (&mut _t)[30usize];
    let v29: u32 =
        vb29.wrapping_add(
            va29.wrapping_add(vb29 & vd29 | vc29 & ! vd29).wrapping_add(xk29).wrapping_add(ti29).wrapping_shl(
                14u32
            )
            |
            va29.wrapping_add(vb29 & vd29 | vc29 & ! vd29).wrapping_add(xk29).wrapping_add(ti29).wrapping_shr(
                18u32
            )
        );
    abcd[2usize] = v29;
    let va30: u32 = abcd[1usize];
    let vb30: u32 = abcd[2usize];
    let vc30: u32 = abcd[3usize];
    let vd30: u32 = abcd[0usize];
    let b30: (&mut [u8], &mut [u8]) = b12.0.split_at_mut(0usize);
    let u30: u32 = crate::lowstar::endianness::load32_le(b30.1);
    let xk30: u32 = u30;
    let ti30: u32 = (&mut _t)[31usize];
    let v30: u32 =
        vb30.wrapping_add(
            va30.wrapping_add(vb30 & vd30 | vc30 & ! vd30).wrapping_add(xk30).wrapping_add(ti30).wrapping_shl(
                20u32
            )
            |
            va30.wrapping_add(vb30 & vd30 | vc30 & ! vd30).wrapping_add(xk30).wrapping_add(ti30).wrapping_shr(
                12u32
            )
        );
    abcd[1usize] = v30;
    let va31: u32 = abcd[0usize];
    let vb31: u32 = abcd[1usize];
    let vc31: u32 = abcd[2usize];
    let vd31: u32 = abcd[3usize];
    let b31: (&mut [u8], &mut [u8]) = b19.1.split_at_mut(0usize);
    let u31: u32 = crate::lowstar::endianness::load32_le(b31.1);
    let xk31: u32 = u31;
    let ti31: u32 = (&mut _t)[32usize];
    let v31: u32 =
        vb31.wrapping_add(
            va31.wrapping_add(vb31 ^ (vc31 ^ vd31)).wrapping_add(xk31).wrapping_add(ti31).wrapping_shl(
                4u32
            )
            |
            va31.wrapping_add(vb31 ^ (vc31 ^ vd31)).wrapping_add(xk31).wrapping_add(ti31).wrapping_shr(
                28u32
            )
        );
    abcd[0usize] = v31;
    let va32: u32 = abcd[3usize];
    let vb32: u32 = abcd[0usize];
    let vc32: u32 = abcd[1usize];
    let vd32: u32 = abcd[2usize];
    let b32: (&mut [u8], &mut [u8]) = b26.1.split_at_mut(0usize);
    let u32: u32 = crate::lowstar::endianness::load32_le(b32.1);
    let xk32: u32 = u32;
    let ti32: u32 = (&mut _t)[33usize];
    let v32: u32 =
        vb32.wrapping_add(
            va32.wrapping_add(vb32 ^ (vc32 ^ vd32)).wrapping_add(xk32).wrapping_add(ti32).wrapping_shl(
                11u32
            )
            |
            va32.wrapping_add(vb32 ^ (vc32 ^ vd32)).wrapping_add(xk32).wrapping_add(ti32).wrapping_shr(
                21u32
            )
        );
    abcd[3usize] = v32;
    let va33: u32 = abcd[2usize];
    let vb33: u32 = abcd[3usize];
    let vc33: u32 = abcd[0usize];
    let vd33: u32 = abcd[1usize];
    let b33: (&mut [u8], &mut [u8]) = b17.1.split_at_mut(0usize);
    let u33: u32 = crate::lowstar::endianness::load32_le(b33.1);
    let xk33: u32 = u33;
    let ti33: u32 = (&mut _t)[34usize];
    let v33: u32 =
        vb33.wrapping_add(
            va33.wrapping_add(vb33 ^ (vc33 ^ vd33)).wrapping_add(xk33).wrapping_add(ti33).wrapping_shl(
                16u32
            )
            |
            va33.wrapping_add(vb33 ^ (vc33 ^ vd33)).wrapping_add(xk33).wrapping_add(ti33).wrapping_shr(
                16u32
            )
        );
    abcd[2usize] = v33;
    let va34: u32 = abcd[1usize];
    let vb34: u32 = abcd[2usize];
    let vc34: u32 = abcd[3usize];
    let vd34: u32 = abcd[0usize];
    let b34: (&mut [u8], &mut [u8]) = b24.1.split_at_mut(0usize);
    let u34: u32 = crate::lowstar::endianness::load32_le(b34.1);
    let xk34: u32 = u34;
    let ti34: u32 = (&mut _t)[35usize];
    let v34: u32 =
        vb34.wrapping_add(
            va34.wrapping_add(vb34 ^ (vc34 ^ vd34)).wrapping_add(xk34).wrapping_add(ti34).wrapping_shl(
                23u32
            )
            |
            va34.wrapping_add(vb34 ^ (vc34 ^ vd34)).wrapping_add(xk34).wrapping_add(ti34).wrapping_shr(
                9u32
            )
        );
    abcd[1usize] = v34;
    let va35: u32 = abcd[0usize];
    let vb35: u32 = abcd[1usize];
    let vc35: u32 = abcd[2usize];
    let vd35: u32 = abcd[3usize];
    let b35: (&mut [u8], &mut [u8]) = b15.1.split_at_mut(0usize);
    let u35: u32 = crate::lowstar::endianness::load32_le(b35.1);
    let xk35: u32 = u35;
    let ti35: u32 = (&mut _t)[36usize];
    let v35: u32 =
        vb35.wrapping_add(
            va35.wrapping_add(vb35 ^ (vc35 ^ vd35)).wrapping_add(xk35).wrapping_add(ti35).wrapping_shl(
                4u32
            )
            |
            va35.wrapping_add(vb35 ^ (vc35 ^ vd35)).wrapping_add(xk35).wrapping_add(ti35).wrapping_shr(
                28u32
            )
        );
    abcd[0usize] = v35;
    let va36: u32 = abcd[3usize];
    let vb36: u32 = abcd[0usize];
    let vc36: u32 = abcd[1usize];
    let vd36: u32 = abcd[2usize];
    let b36: (&mut [u8], &mut [u8]) = b22.1.split_at_mut(0usize);
    let u36: u32 = crate::lowstar::endianness::load32_le(b36.1);
    let xk36: u32 = u36;
    let ti36: u32 = (&mut _t)[37usize];
    let v36: u32 =
        vb36.wrapping_add(
            va36.wrapping_add(vb36 ^ (vc36 ^ vd36)).wrapping_add(xk36).wrapping_add(ti36).wrapping_shl(
                11u32
            )
            |
            va36.wrapping_add(vb36 ^ (vc36 ^ vd36)).wrapping_add(xk36).wrapping_add(ti36).wrapping_shr(
                21u32
            )
        );
    abcd[3usize] = v36;
    let va37: u32 = abcd[2usize];
    let vb37: u32 = abcd[3usize];
    let vc37: u32 = abcd[0usize];
    let vd37: u32 = abcd[1usize];
    let b37: (&mut [u8], &mut [u8]) = b29.1.split_at_mut(0usize);
    let u37: u32 = crate::lowstar::endianness::load32_le(b37.1);
    let xk37: u32 = u37;
    let ti37: u32 = (&mut _t)[38usize];
    let v37: u32 =
        vb37.wrapping_add(
            va37.wrapping_add(vb37 ^ (vc37 ^ vd37)).wrapping_add(xk37).wrapping_add(ti37).wrapping_shl(
                16u32
            )
            |
            va37.wrapping_add(vb37 ^ (vc37 ^ vd37)).wrapping_add(xk37).wrapping_add(ti37).wrapping_shr(
                16u32
            )
        );
    abcd[2usize] = v37;
    let va38: u32 = abcd[1usize];
    let vb38: u32 = abcd[2usize];
    let vc38: u32 = abcd[3usize];
    let vd38: u32 = abcd[0usize];
    let b38: (&mut [u8], &mut [u8]) = b20.1.split_at_mut(0usize);
    let u38: u32 = crate::lowstar::endianness::load32_le(b38.1);
    let xk38: u32 = u38;
    let ti38: u32 = (&mut _t)[39usize];
    let v38: u32 =
        vb38.wrapping_add(
            va38.wrapping_add(vb38 ^ (vc38 ^ vd38)).wrapping_add(xk38).wrapping_add(ti38).wrapping_shl(
                23u32
            )
            |
            va38.wrapping_add(vb38 ^ (vc38 ^ vd38)).wrapping_add(xk38).wrapping_add(ti38).wrapping_shr(
                9u32
            )
        );
    abcd[1usize] = v38;
    let va39: u32 = abcd[0usize];
    let vb39: u32 = abcd[1usize];
    let vc39: u32 = abcd[2usize];
    let vd39: u32 = abcd[3usize];
    let b39: (&mut [u8], &mut [u8]) = b27.1.split_at_mut(0usize);
    let u39: u32 = crate::lowstar::endianness::load32_le(b39.1);
    let xk39: u32 = u39;
    let ti39: u32 = (&mut _t)[40usize];
    let v39: u32 =
        vb39.wrapping_add(
            va39.wrapping_add(vb39 ^ (vc39 ^ vd39)).wrapping_add(xk39).wrapping_add(ti39).wrapping_shl(
                4u32
            )
            |
            va39.wrapping_add(vb39 ^ (vc39 ^ vd39)).wrapping_add(xk39).wrapping_add(ti39).wrapping_shr(
                28u32
            )
        );
    abcd[0usize] = v39;
    let va40: u32 = abcd[3usize];
    let vb40: u32 = abcd[0usize];
    let vc40: u32 = abcd[1usize];
    let vd40: u32 = abcd[2usize];
    let b40: (&mut [u8], &mut [u8]) = b18.1.split_at_mut(0usize);
    let u40: u32 = crate::lowstar::endianness::load32_le(b40.1);
    let xk40: u32 = u40;
    let ti40: u32 = (&mut _t)[41usize];
    let v40: u32 =
        vb40.wrapping_add(
            va40.wrapping_add(vb40 ^ (vc40 ^ vd40)).wrapping_add(xk40).wrapping_add(ti40).wrapping_shl(
                11u32
            )
            |
            va40.wrapping_add(vb40 ^ (vc40 ^ vd40)).wrapping_add(xk40).wrapping_add(ti40).wrapping_shr(
                21u32
            )
        );
    abcd[3usize] = v40;
    let va41: u32 = abcd[2usize];
    let vb41: u32 = abcd[3usize];
    let vc41: u32 = abcd[0usize];
    let vd41: u32 = abcd[1usize];
    let b41: (&mut [u8], &mut [u8]) = b25.1.split_at_mut(0usize);
    let u41: u32 = crate::lowstar::endianness::load32_le(b41.1);
    let xk41: u32 = u41;
    let ti41: u32 = (&mut _t)[42usize];
    let v41: u32 =
        vb41.wrapping_add(
            va41.wrapping_add(vb41 ^ (vc41 ^ vd41)).wrapping_add(xk41).wrapping_add(ti41).wrapping_shl(
                16u32
            )
            |
            va41.wrapping_add(vb41 ^ (vc41 ^ vd41)).wrapping_add(xk41).wrapping_add(ti41).wrapping_shr(
                16u32
            )
        );
    abcd[2usize] = v41;
    let va42: u32 = abcd[1usize];
    let vb42: u32 = abcd[2usize];
    let vc42: u32 = abcd[3usize];
    let vd42: u32 = abcd[0usize];
    let b42: (&mut [u8], &mut [u8]) = b16.1.split_at_mut(0usize);
    let u42: u32 = crate::lowstar::endianness::load32_le(b42.1);
    let xk42: u32 = u42;
    let ti42: u32 = (&mut _t)[43usize];
    let v42: u32 =
        vb42.wrapping_add(
            va42.wrapping_add(vb42 ^ (vc42 ^ vd42)).wrapping_add(xk42).wrapping_add(ti42).wrapping_shl(
                23u32
            )
            |
            va42.wrapping_add(vb42 ^ (vc42 ^ vd42)).wrapping_add(xk42).wrapping_add(ti42).wrapping_shr(
                9u32
            )
        );
    abcd[1usize] = v42;
    let va43: u32 = abcd[0usize];
    let vb43: u32 = abcd[1usize];
    let vc43: u32 = abcd[2usize];
    let vd43: u32 = abcd[3usize];
    let b43: (&mut [u8], &mut [u8]) = b23.1.split_at_mut(0usize);
    let u43: u32 = crate::lowstar::endianness::load32_le(b43.1);
    let xk43: u32 = u43;
    let ti43: u32 = (&mut _t)[44usize];
    let v43: u32 =
        vb43.wrapping_add(
            va43.wrapping_add(vb43 ^ (vc43 ^ vd43)).wrapping_add(xk43).wrapping_add(ti43).wrapping_shl(
                4u32
            )
            |
            va43.wrapping_add(vb43 ^ (vc43 ^ vd43)).wrapping_add(xk43).wrapping_add(ti43).wrapping_shr(
                28u32
            )
        );
    abcd[0usize] = v43;
    let va44: u32 = abcd[3usize];
    let vb44: u32 = abcd[0usize];
    let vc44: u32 = abcd[1usize];
    let vd44: u32 = abcd[2usize];
    let b44: (&mut [u8], &mut [u8]) = b30.1.split_at_mut(0usize);
    let u44: u32 = crate::lowstar::endianness::load32_le(b44.1);
    let xk44: u32 = u44;
    let ti44: u32 = (&mut _t)[45usize];
    let v44: u32 =
        vb44.wrapping_add(
            va44.wrapping_add(vb44 ^ (vc44 ^ vd44)).wrapping_add(xk44).wrapping_add(ti44).wrapping_shl(
                11u32
            )
            |
            va44.wrapping_add(vb44 ^ (vc44 ^ vd44)).wrapping_add(xk44).wrapping_add(ti44).wrapping_shr(
                21u32
            )
        );
    abcd[3usize] = v44;
    let va45: u32 = abcd[2usize];
    let vb45: u32 = abcd[3usize];
    let vc45: u32 = abcd[0usize];
    let vd45: u32 = abcd[1usize];
    let b45: (&mut [u8], &mut [u8]) = b21.1.split_at_mut(0usize);
    let u45: u32 = crate::lowstar::endianness::load32_le(b45.1);
    let xk45: u32 = u45;
    let ti45: u32 = (&mut _t)[46usize];
    let v45: u32 =
        vb45.wrapping_add(
            va45.wrapping_add(vb45 ^ (vc45 ^ vd45)).wrapping_add(xk45).wrapping_add(ti45).wrapping_shl(
                16u32
            )
            |
            va45.wrapping_add(vb45 ^ (vc45 ^ vd45)).wrapping_add(xk45).wrapping_add(ti45).wrapping_shr(
                16u32
            )
        );
    abcd[2usize] = v45;
    let va46: u32 = abcd[1usize];
    let vb46: u32 = abcd[2usize];
    let vc46: u32 = abcd[3usize];
    let vd46: u32 = abcd[0usize];
    let b46: (&mut [u8], &mut [u8]) = b28.1.split_at_mut(0usize);
    let u46: u32 = crate::lowstar::endianness::load32_le(b46.1);
    let xk46: u32 = u46;
    let ti46: u32 = (&mut _t)[47usize];
    let v46: u32 =
        vb46.wrapping_add(
            va46.wrapping_add(vb46 ^ (vc46 ^ vd46)).wrapping_add(xk46).wrapping_add(ti46).wrapping_shl(
                23u32
            )
            |
            va46.wrapping_add(vb46 ^ (vc46 ^ vd46)).wrapping_add(xk46).wrapping_add(ti46).wrapping_shr(
                9u32
            )
        );
    abcd[1usize] = v46;
    let va47: u32 = abcd[0usize];
    let vb47: u32 = abcd[1usize];
    let vc47: u32 = abcd[2usize];
    let vd47: u32 = abcd[3usize];
    let b47: (&mut [u8], &mut [u8]) = b40.1.split_at_mut(0usize);
    let u47: u32 = crate::lowstar::endianness::load32_le(b47.1);
    let xk47: u32 = u47;
    let ti47: u32 = (&mut _t)[48usize];
    let v47: u32 =
        vb47.wrapping_add(
            va47.wrapping_add(vc47 ^ (vb47 | ! vd47)).wrapping_add(xk47).wrapping_add(ti47).wrapping_shl(
                6u32
            )
            |
            va47.wrapping_add(vc47 ^ (vb47 | ! vd47)).wrapping_add(xk47).wrapping_add(ti47).wrapping_shr(
                26u32
            )
        );
    abcd[0usize] = v47;
    let va48: u32 = abcd[3usize];
    let vb48: u32 = abcd[0usize];
    let vc48: u32 = abcd[1usize];
    let vd48: u32 = abcd[2usize];
    let b48: (&mut [u8], &mut [u8]) = b37.1.split_at_mut(0usize);
    let u48: u32 = crate::lowstar::endianness::load32_le(b48.1);
    let xk48: u32 = u48;
    let ti48: u32 = (&mut _t)[49usize];
    let v48: u32 =
        vb48.wrapping_add(
            va48.wrapping_add(vc48 ^ (vb48 | ! vd48)).wrapping_add(xk48).wrapping_add(ti48).wrapping_shl(
                10u32
            )
            |
            va48.wrapping_add(vc48 ^ (vb48 | ! vd48)).wrapping_add(xk48).wrapping_add(ti48).wrapping_shr(
                22u32
            )
        );
    abcd[3usize] = v48;
    let va49: u32 = abcd[2usize];
    let vb49: u32 = abcd[3usize];
    let vc49: u32 = abcd[0usize];
    let vd49: u32 = abcd[1usize];
    let b49: (&mut [u8], &mut [u8]) = b34.1.split_at_mut(0usize);
    let u49: u32 = crate::lowstar::endianness::load32_le(b49.1);
    let xk49: u32 = u49;
    let ti49: u32 = (&mut _t)[50usize];
    let v49: u32 =
        vb49.wrapping_add(
            va49.wrapping_add(vc49 ^ (vb49 | ! vd49)).wrapping_add(xk49).wrapping_add(ti49).wrapping_shl(
                15u32
            )
            |
            va49.wrapping_add(vc49 ^ (vb49 | ! vd49)).wrapping_add(xk49).wrapping_add(ti49).wrapping_shr(
                17u32
            )
        );
    abcd[2usize] = v49;
    let va50: u32 = abcd[1usize];
    let vb50: u32 = abcd[2usize];
    let vc50: u32 = abcd[3usize];
    let vd50: u32 = abcd[0usize];
    let b50: (&mut [u8], &mut [u8]) = b31.1.split_at_mut(0usize);
    let u50: u32 = crate::lowstar::endianness::load32_le(b50.1);
    let xk50: u32 = u50;
    let ti50: u32 = (&mut _t)[51usize];
    let v50: u32 =
        vb50.wrapping_add(
            va50.wrapping_add(vc50 ^ (vb50 | ! vd50)).wrapping_add(xk50).wrapping_add(ti50).wrapping_shl(
                21u32
            )
            |
            va50.wrapping_add(vc50 ^ (vb50 | ! vd50)).wrapping_add(xk50).wrapping_add(ti50).wrapping_shr(
                11u32
            )
        );
    abcd[1usize] = v50;
    let va51: u32 = abcd[0usize];
    let vb51: u32 = abcd[1usize];
    let vc51: u32 = abcd[2usize];
    let vd51: u32 = abcd[3usize];
    let b51: (&mut [u8], &mut [u8]) = b44.1.split_at_mut(0usize);
    let u51: u32 = crate::lowstar::endianness::load32_le(b51.1);
    let xk51: u32 = u51;
    let ti51: u32 = (&mut _t)[52usize];
    let v51: u32 =
        vb51.wrapping_add(
            va51.wrapping_add(vc51 ^ (vb51 | ! vd51)).wrapping_add(xk51).wrapping_add(ti51).wrapping_shl(
                6u32
            )
            |
            va51.wrapping_add(vc51 ^ (vb51 | ! vd51)).wrapping_add(xk51).wrapping_add(ti51).wrapping_shr(
                26u32
            )
        );
    abcd[0usize] = v51;
    let va52: u32 = abcd[3usize];
    let vb52: u32 = abcd[0usize];
    let vc52: u32 = abcd[1usize];
    let vd52: u32 = abcd[2usize];
    let b52: (&mut [u8], &mut [u8]) = b41.1.split_at_mut(0usize);
    let u52: u32 = crate::lowstar::endianness::load32_le(b52.1);
    let xk52: u32 = u52;
    let ti52: u32 = (&mut _t)[53usize];
    let v52: u32 =
        vb52.wrapping_add(
            va52.wrapping_add(vc52 ^ (vb52 | ! vd52)).wrapping_add(xk52).wrapping_add(ti52).wrapping_shl(
                10u32
            )
            |
            va52.wrapping_add(vc52 ^ (vb52 | ! vd52)).wrapping_add(xk52).wrapping_add(ti52).wrapping_shr(
                22u32
            )
        );
    abcd[3usize] = v52;
    let va53: u32 = abcd[2usize];
    let vb53: u32 = abcd[3usize];
    let vc53: u32 = abcd[0usize];
    let vd53: u32 = abcd[1usize];
    let b53: (&mut [u8], &mut [u8]) = b38.1.split_at_mut(0usize);
    let u53: u32 = crate::lowstar::endianness::load32_le(b53.1);
    let xk53: u32 = u53;
    let ti53: u32 = (&mut _t)[54usize];
    let v53: u32 =
        vb53.wrapping_add(
            va53.wrapping_add(vc53 ^ (vb53 | ! vd53)).wrapping_add(xk53).wrapping_add(ti53).wrapping_shl(
                15u32
            )
            |
            va53.wrapping_add(vc53 ^ (vb53 | ! vd53)).wrapping_add(xk53).wrapping_add(ti53).wrapping_shr(
                17u32
            )
        );
    abcd[2usize] = v53;
    let va54: u32 = abcd[1usize];
    let vb54: u32 = abcd[2usize];
    let vc54: u32 = abcd[3usize];
    let vd54: u32 = abcd[0usize];
    let b54: (&mut [u8], &mut [u8]) = b35.1.split_at_mut(0usize);
    let u54: u32 = crate::lowstar::endianness::load32_le(b54.1);
    let xk54: u32 = u54;
    let ti54: u32 = (&mut _t)[55usize];
    let v54: u32 =
        vb54.wrapping_add(
            va54.wrapping_add(vc54 ^ (vb54 | ! vd54)).wrapping_add(xk54).wrapping_add(ti54).wrapping_shl(
                21u32
            )
            |
            va54.wrapping_add(vc54 ^ (vb54 | ! vd54)).wrapping_add(xk54).wrapping_add(ti54).wrapping_shr(
                11u32
            )
        );
    abcd[1usize] = v54;
    let va55: u32 = abcd[0usize];
    let vb55: u32 = abcd[1usize];
    let vc55: u32 = abcd[2usize];
    let vd55: u32 = abcd[3usize];
    let b55: (&mut [u8], &mut [u8]) = b32.1.split_at_mut(0usize);
    let u55: u32 = crate::lowstar::endianness::load32_le(b55.1);
    let xk55: u32 = u55;
    let ti55: u32 = (&mut _t)[56usize];
    let v55: u32 =
        vb55.wrapping_add(
            va55.wrapping_add(vc55 ^ (vb55 | ! vd55)).wrapping_add(xk55).wrapping_add(ti55).wrapping_shl(
                6u32
            )
            |
            va55.wrapping_add(vc55 ^ (vb55 | ! vd55)).wrapping_add(xk55).wrapping_add(ti55).wrapping_shr(
                26u32
            )
        );
    abcd[0usize] = v55;
    let va56: u32 = abcd[3usize];
    let vb56: u32 = abcd[0usize];
    let vc56: u32 = abcd[1usize];
    let vd56: u32 = abcd[2usize];
    let b56: (&mut [u8], &mut [u8]) = b45.1.split_at_mut(0usize);
    let u56: u32 = crate::lowstar::endianness::load32_le(b56.1);
    let xk56: u32 = u56;
    let ti56: u32 = (&mut _t)[57usize];
    let v56: u32 =
        vb56.wrapping_add(
            va56.wrapping_add(vc56 ^ (vb56 | ! vd56)).wrapping_add(xk56).wrapping_add(ti56).wrapping_shl(
                10u32
            )
            |
            va56.wrapping_add(vc56 ^ (vb56 | ! vd56)).wrapping_add(xk56).wrapping_add(ti56).wrapping_shr(
                22u32
            )
        );
    abcd[3usize] = v56;
    let va57: u32 = abcd[2usize];
    let vb57: u32 = abcd[3usize];
    let vc57: u32 = abcd[0usize];
    let vd57: u32 = abcd[1usize];
    let b57: (&mut [u8], &mut [u8]) = b42.1.split_at_mut(0usize);
    let u57: u32 = crate::lowstar::endianness::load32_le(b57.1);
    let xk57: u32 = u57;
    let ti57: u32 = (&mut _t)[58usize];
    let v57: u32 =
        vb57.wrapping_add(
            va57.wrapping_add(vc57 ^ (vb57 | ! vd57)).wrapping_add(xk57).wrapping_add(ti57).wrapping_shl(
                15u32
            )
            |
            va57.wrapping_add(vc57 ^ (vb57 | ! vd57)).wrapping_add(xk57).wrapping_add(ti57).wrapping_shr(
                17u32
            )
        );
    abcd[2usize] = v57;
    let va58: u32 = abcd[1usize];
    let vb58: u32 = abcd[2usize];
    let vc58: u32 = abcd[3usize];
    let vd58: u32 = abcd[0usize];
    let b58: (&mut [u8], &mut [u8]) = b39.1.split_at_mut(0usize);
    let u58: u32 = crate::lowstar::endianness::load32_le(b58.1);
    let xk58: u32 = u58;
    let ti58: u32 = (&mut _t)[59usize];
    let v58: u32 =
        vb58.wrapping_add(
            va58.wrapping_add(vc58 ^ (vb58 | ! vd58)).wrapping_add(xk58).wrapping_add(ti58).wrapping_shl(
                21u32
            )
            |
            va58.wrapping_add(vc58 ^ (vb58 | ! vd58)).wrapping_add(xk58).wrapping_add(ti58).wrapping_shr(
                11u32
            )
        );
    abcd[1usize] = v58;
    let va59: u32 = abcd[0usize];
    let vb59: u32 = abcd[1usize];
    let vc59: u32 = abcd[2usize];
    let vd59: u32 = abcd[3usize];
    let b59: (&mut [u8], &mut [u8]) = b36.1.split_at_mut(0usize);
    let u59: u32 = crate::lowstar::endianness::load32_le(b59.1);
    let xk59: u32 = u59;
    let ti59: u32 = (&mut _t)[60usize];
    let v59: u32 =
        vb59.wrapping_add(
            va59.wrapping_add(vc59 ^ (vb59 | ! vd59)).wrapping_add(xk59).wrapping_add(ti59).wrapping_shl(
                6u32
            )
            |
            va59.wrapping_add(vc59 ^ (vb59 | ! vd59)).wrapping_add(xk59).wrapping_add(ti59).wrapping_shr(
                26u32
            )
        );
    abcd[0usize] = v59;
    let va60: u32 = abcd[3usize];
    let vb60: u32 = abcd[0usize];
    let vc60: u32 = abcd[1usize];
    let vd60: u32 = abcd[2usize];
    let b60: (&mut [u8], &mut [u8]) = b33.1.split_at_mut(0usize);
    let u60: u32 = crate::lowstar::endianness::load32_le(b60.1);
    let xk60: u32 = u60;
    let ti60: u32 = (&mut _t)[61usize];
    let v60: u32 =
        vb60.wrapping_add(
            va60.wrapping_add(vc60 ^ (vb60 | ! vd60)).wrapping_add(xk60).wrapping_add(ti60).wrapping_shl(
                10u32
            )
            |
            va60.wrapping_add(vc60 ^ (vb60 | ! vd60)).wrapping_add(xk60).wrapping_add(ti60).wrapping_shr(
                22u32
            )
        );
    abcd[3usize] = v60;
    let va61: u32 = abcd[2usize];
    let vb61: u32 = abcd[3usize];
    let vc61: u32 = abcd[0usize];
    let vd61: u32 = abcd[1usize];
    let b61: (&mut [u8], &mut [u8]) = b46.1.split_at_mut(0usize);
    let u61: u32 = crate::lowstar::endianness::load32_le(b61.1);
    let xk61: u32 = u61;
    let ti61: u32 = (&mut _t)[62usize];
    let v61: u32 =
        vb61.wrapping_add(
            va61.wrapping_add(vc61 ^ (vb61 | ! vd61)).wrapping_add(xk61).wrapping_add(ti61).wrapping_shl(
                15u32
            )
            |
            va61.wrapping_add(vc61 ^ (vb61 | ! vd61)).wrapping_add(xk61).wrapping_add(ti61).wrapping_shr(
                17u32
            )
        );
    abcd[2usize] = v61;
    let va62: u32 = abcd[1usize];
    let vb62: u32 = abcd[2usize];
    let vc62: u32 = abcd[3usize];
    let vd62: u32 = abcd[0usize];
    let b62: (&mut [u8], &mut [u8]) = b43.1.split_at_mut(0usize);
    let u62: u32 = crate::lowstar::endianness::load32_le(b62.1);
    let xk62: u32 = u62;
    let ti62: u32 = (&mut _t)[63usize];
    let v62: u32 =
        vb62.wrapping_add(
            va62.wrapping_add(vc62 ^ (vb62 | ! vd62)).wrapping_add(xk62).wrapping_add(ti62).wrapping_shl(
                21u32
            )
            |
            va62.wrapping_add(vc62 ^ (vb62 | ! vd62)).wrapping_add(xk62).wrapping_add(ti62).wrapping_shr(
                11u32
            )
        );
    abcd[1usize] = v62;
    let a: u32 = abcd[0usize];
    let b63: u32 = abcd[1usize];
    let c: u32 = abcd[2usize];
    let d: u32 = abcd[3usize];
    abcd[0usize] = a.wrapping_add(aa);
    abcd[1usize] = b63.wrapping_add(bb);
    abcd[2usize] = c.wrapping_add(cc);
    abcd[3usize] = d.wrapping_add(dd)
}

fn pad(len: u64, dst: &mut [u8]) -> ()
{
    let dst1: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
    dst1.1[0usize] = 0x80u8;
    let dst2: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(1usize);
    for
    i
    in
    0u32..128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
        64u32
    )
    { dst2.1[i as usize] = 0u8 };
    let dst3: (&mut [u8], &mut [u8]) =
        dst2.1.split_at_mut(
            128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
                64u32
            )
            as
            usize
        );
    crate::lowstar::endianness::store64_le(dst3.1, len.wrapping_shl(3u32))
}

pub fn finish(s: &mut [u32], dst: &mut [u8]) -> ()
{
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store32_le(
            &mut dst[i.wrapping_mul(4u32) as usize..],
            (&mut s[0usize..])[i as usize]
        )
    }
}

pub fn update_multi(s: &mut [u32], blocks: &mut [u8], n_blocks: u32) -> ()
{
    for i in 0u32..n_blocks
    {
        let sz: u32 = 64u32;
        let block: (&mut [u8], &mut [u8]) = blocks.split_at_mut(sz.wrapping_mul(i) as usize);
        update(s, block.1)
    }
}

pub fn update_last(s: &mut [u32], prev_len: u64, input: &mut [u8], input_len: u32) -> ()
{
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_len: u32 = blocks_n.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) = blocks.1.split_at_mut(blocks_len as usize);
    update_multi(s, rest.0, blocks_n);
    let total_input_len: u64 = prev_len.wrapping_add(input_len as u64);
    let pad_len: u32 =
        1u32.wrapping_add(
            128u32.wrapping_sub(
                9u32.wrapping_add(total_input_len.wrapping_rem(64u32 as u64) as u32)
            ).wrapping_rem(64u32)
        ).wrapping_add(8u32);
    let tmp_len: u32 = rest_len.wrapping_add(pad_len);
    let mut tmp_twoblocks: [u8; 128] = [0u8; 128usize];
    let tmp: (&mut [u8], &mut [u8]) = (&mut tmp_twoblocks).split_at_mut(0usize);
    let tmp_rest: (&mut [u8], &mut [u8]) = tmp.1.split_at_mut(0usize);
    let tmp_pad: (&mut [u8], &mut [u8]) = tmp_rest.1.split_at_mut(rest_len as usize);
    (tmp_pad.0[0usize..rest_len as usize]).copy_from_slice(&rest.1[0usize..rest_len as usize]);
    pad(total_input_len, tmp_pad.1);
    update_multi(s, tmp.1, tmp_len.wrapping_div(64u32))
}

pub fn hash_oneshot(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{
    let mut s: [u32; 4] = [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32];
    let blocks_n: u32 = input_len.wrapping_div(64u32);
    let blocks_n1: u32 =
        if input_len.wrapping_rem(64u32) == 0u32 && blocks_n > 0u32
        { blocks_n.wrapping_sub(1u32) }
        else
        { blocks_n };
    let blocks_len: u32 = blocks_n1.wrapping_mul(64u32);
    let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
    let rest_len: u32 = input_len.wrapping_sub(blocks_len);
    let rest: (&mut [u8], &mut [u8]) = blocks.1.split_at_mut(blocks_len as usize);
    let blocks_n0: u32 = blocks_n1;
    let blocks_len0: u32 = blocks_len;
    let blocks0: &mut [u8] = rest.0;
    let rest_len0: u32 = rest_len;
    let rest0: &mut [u8] = rest.1;
    update_multi(&mut s, blocks0, blocks_n0);
    update_last(&mut s, blocks_len0 as u64, rest0, rest_len0);
    finish(&mut s, output)
}

pub type state_t = crate::hacl::streaming_types::state_32;

pub fn malloc() -> Vec<crate::hacl::streaming_types::state_32>
{
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    let mut block_state: Vec<u32> = vec![0u32; 4usize];
    init(&mut block_state);
    let mut s: crate::hacl::streaming_types::state_32 =
        crate::hacl::streaming_types::state_32
        { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<crate::hacl::streaming_types::state_32> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_32> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset(state: &mut [crate::hacl::streaming_types::state_32]) -> ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    init(block_state);
    (state[0usize]).total_len = 0u32 as u64
}

pub fn update0(
    state: &mut [crate::hacl::streaming_types::state_32],
    chunk: &mut [u8],
    chunk_len: u32
) ->
    crate::hacl::streaming_types::error_code
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 2305843009213693951u64.wrapping_sub(total_len)
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
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else
        if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz1 == 0u32) { update_multi(block_state, buf, 1u32) };
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
            update_multi(block_state, data2.0, data1_len.wrapping_div(64u32));
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if total_len10.wrapping_rem(64u32 as u64) == 0u64 && total_len10 > 0u64
                { 64u32 }
                else
                { total_len10.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz10 == 0u32) { update_multi(block_state, buf0, 1u32) };
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
            update_multi(block_state, data2.0, data1_len.wrapping_div(64u32));
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::hacl::streaming_types::error_code::Success
    }
}

pub fn digest(state: &mut [crate::hacl::streaming_types::state_32], output: &mut [u8]) -> ()
{
    let block_state: &mut [u32] = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut tmp_block_state: [u32; 4] = [0u32; 4usize];
    ((&mut tmp_block_state)[0usize..4usize]).copy_from_slice(&block_state[0usize..4usize]);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    update_multi(&mut tmp_block_state, buf_last.0, 0u32);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    update_last(&mut tmp_block_state, prev_len_last, buf_last.1, r);
    finish(&mut tmp_block_state, output)
}

pub fn copy(state: &mut [crate::hacl::streaming_types::state_32]) ->
    Vec<crate::hacl::streaming_types::state_32>
{
    let block_state0: &mut [u32] = &mut (state[0usize]).block_state;
    let buf0: &mut [u8] = &mut (state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    ((&mut buf)[0usize..64usize]).copy_from_slice(&buf0[0usize..64usize]);
    let mut block_state: Vec<u32> = vec![0u32; 4usize];
    ((&mut block_state)[0usize..4usize]).copy_from_slice(&block_state0[0usize..4usize]);
    let mut s: crate::hacl::streaming_types::state_32 =
        crate::hacl::streaming_types::state_32
        { block_state: block_state, buf: buf, total_len: total_len0 };
    let mut p: Vec<crate::hacl::streaming_types::state_32> =
        {
            let mut tmp: Vec<crate::hacl::streaming_types::state_32> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn hash(output: &mut [u8], input: &mut [u8], input_len: u32) -> ()
{ hash_oneshot(output, input, input_len) }
