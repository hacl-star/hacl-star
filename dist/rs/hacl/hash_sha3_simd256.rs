#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn absorb_inner_256(
    rateInBytes: u32,
    b: crate::sha2_types::uint8_4p,
    s: &mut [lib::intvector_intrinsics::vec256]
)
{
    lowstar::ignore::ignore::<u32>(rateInBytes);
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b1, snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b0[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b1[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b2[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b3[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec256_load64_le(&b0[32usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec256_load64_le(&b1[32usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec256_load64_le(&b2[32usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec256_load64_le(&b3[32usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec256_load64_le(&b0[64usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec256_load64_le(&b1[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b0[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b1[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b0[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b1[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b0[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b1[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b0[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b1[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b0[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b1[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b2[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b3[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        s[i as usize] =
            lib::intvector_intrinsics::vec256_xor(s[i as usize], (&ws)[i as usize])
    );
    krml::unroll_for!(
        24,
        "i",
        0u32,
        1u32,
        {
            let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                [lib::intvector_intrinsics::vec256_zero; 5usize];
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____0: lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(0u32) as usize];
                    let uu____1: lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(5u32) as usize];
                    let uu____2: lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(10u32) as usize];
                    (&mut _C)[i0 as usize] =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____0,
                            lib::intvector_intrinsics::vec256_xor(
                                uu____1,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____2,
                                    lib::intvector_intrinsics::vec256_xor(
                                        s[i0.wrapping_add(15u32) as usize],
                                        s[i0.wrapping_add(20u32) as usize]
                                    )
                                )
                            )
                        )
                }
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____3: lib::intvector_intrinsics::vec256 =
                        (&_C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                    let uu____4: lib::intvector_intrinsics::vec256 =
                        (&_C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                    let _D: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____3,
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____4, 1u32),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____4,
                                    63u32
                                )
                            )
                        );
                    krml::unroll_for!(
                        5,
                        "i1",
                        0u32,
                        1u32,
                        s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize],
                                _D
                            )
                    )
                }
            );
            let x: lib::intvector_intrinsics::vec256 = s[1usize];
            let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i0 as usize];
                    let r: u32 = (&crate::hash_sha3::keccak_rotc)[i0 as usize];
                    let temp: lib::intvector_intrinsics::vec256 = s[_Y as usize];
                    let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                    s[_Y as usize] =
                        lib::intvector_intrinsics::vec256_or(
                            lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                            lib::intvector_intrinsics::vec256_shift_right64(
                                uu____5,
                                64u32.wrapping_sub(r)
                            )
                        );
                    (&mut current)[0usize] = temp
                }
            );
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____6: lib::intvector_intrinsics::vec256 =
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____7: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_lognot(
                            s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v07: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____6,
                            lib::intvector_intrinsics::vec256_and(
                                uu____7,
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____8: lib::intvector_intrinsics::vec256 =
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____9: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_lognot(
                            s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v17: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____8,
                            lib::intvector_intrinsics::vec256_and(
                                uu____9,
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____10: lib::intvector_intrinsics::vec256 =
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____11: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_lognot(
                            s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v27: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____10,
                            lib::intvector_intrinsics::vec256_and(
                                uu____11,
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____12: lib::intvector_intrinsics::vec256 =
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____13: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_lognot(
                            s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v37: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____12,
                            lib::intvector_intrinsics::vec256_and(
                                uu____13,
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____14: lib::intvector_intrinsics::vec256 =
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____15: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_lognot(
                            s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v4: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_xor(
                            uu____14,
                            lib::intvector_intrinsics::vec256_and(
                                uu____15,
                                s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v07;
                    s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v17;
                    s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v27;
                    s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v37;
                    s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize] = v4
                }
            );
            let c: u64 = (&crate::hash_sha3::keccak_rndc)[i as usize];
            let uu____16: lib::intvector_intrinsics::vec256 = s[0usize];
            s[0usize] =
                lib::intvector_intrinsics::vec256_xor(
                    uu____16,
                    lib::intvector_intrinsics::vec256_load64(c)
                )
        }
    )
}

pub fn shake128(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    outputByteLen: u32,
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 168u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

pub fn shake256(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    outputByteLen: u32,
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut)
              as
              usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

pub fn sha3_224(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 144u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..28u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 28u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

pub fn sha3_256(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..32u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 32u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

pub fn sha3_384(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 104u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..48u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 48u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

pub fn sha3_512(
    output0: &[u8],
    output1: &[u8],
    output2: &[u8],
    output3: &[u8],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let mut rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: output1, snd: crate::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [lib::intvector_intrinsics::vec256; 25] =
        [lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 72u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b00,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref b10,
                    snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 }
                }
            }
            =>
              match b·
              {
                  crate::sha2_types::uint8_4p
                  {
                      fst: ref mut bl0,
                      snd:
                      crate::sha2_types::uint8_3p
                      {
                          fst: ref mut bl1,
                          snd:
                          crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                      }
                  }
                  =>
                    {
                        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        );
                        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
                            &(&b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1
                            as
                            usize]
                        )
                    }
              }
        };
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    match ib
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          match b·
          {
              crate::sha2_types::uint8_4p
              {
                  fst: ref mut bl0,
                  snd:
                  crate::sha2_types::uint8_3p
                  {
                      fst: ref mut bl1,
                      snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                  }
              }
              =>
                {
                    (bl0[0usize..rem as usize]).copy_from_slice(
                        &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl1[0usize..rem as usize]).copy_from_slice(
                        &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl2[0usize..rem as usize]).copy_from_slice(
                        &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    );
                    (bl3[0usize..rem as usize]).copy_from_slice(
                        &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
                    )
                }
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b00,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b10,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b20, snd: ref mut b30 }
            }
        }
        =>
          {
              b00[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b10[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b20[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
              b30[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b10, snd: crate::sha2_types::uint8_2p { fst: ref b20, snd: ref b30 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b00[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b10[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b20[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b30[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b00[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b10[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b20[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b30[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        (&mut s)[i as usize] =
            lib::intvector_intrinsics::vec256_xor((&s)[i as usize], (&ws)[i as usize])
    );
    let b00: [u8; 256] = [0u8; 256usize];
    let b10: [u8; 256] = [0u8; 256usize];
    let b20: [u8; 256] = [0u8; 256usize];
    let b30: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b00,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b10, snd: crate::sha2_types::uint8_2p { fst: &b20, snd: &b30 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b11[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b21[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
              b31[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8
          }
    };
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..64u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
        let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
        let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
        let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
        let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
        let v0·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: lib::intvector_intrinsics::vec256 = v3··7;
        let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
        let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
        let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
        let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
        let v0·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: lib::intvector_intrinsics::vec256 = v3··8;
        let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
        let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
        let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
        let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
        let v0·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: lib::intvector_intrinsics::vec256 = v3··9;
        let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
        let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
        let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
        let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
        let v0·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: lib::intvector_intrinsics::vec256 = v3··10;
        let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
        let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
        let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
        let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
        let v0·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: lib::intvector_intrinsics::vec256 = v3··11;
        let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
        let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
        let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
        let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
        let v0·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: lib::intvector_intrinsics::vec256 = v3··12;
        let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
        let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
        let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
        let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
        let v0·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: lib::intvector_intrinsics::vec256 = v3··13;
        let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
        let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
        let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
        let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
        let v0·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: lib::intvector_intrinsics::vec256 = v3··14;
        (&mut ws32)[0usize] = ws00;
        (&mut ws32)[1usize] = ws40;
        (&mut ws32)[2usize] = ws80;
        (&mut ws32)[3usize] = ws120;
        (&mut ws32)[4usize] = ws160;
        (&mut ws32)[5usize] = ws200;
        (&mut ws32)[6usize] = ws240;
        (&mut ws32)[7usize] = ws280;
        (&mut ws32)[8usize] = ws110;
        (&mut ws32)[9usize] = ws50;
        (&mut ws32)[10usize] = ws90;
        (&mut ws32)[11usize] = ws130;
        (&mut ws32)[12usize] = ws170;
        (&mut ws32)[13usize] = ws211;
        (&mut ws32)[14usize] = ws250;
        (&mut ws32)[15usize] = ws290;
        (&mut ws32)[16usize] = ws210;
        (&mut ws32)[17usize] = ws60;
        (&mut ws32)[18usize] = ws100;
        (&mut ws32)[19usize] = ws140;
        (&mut ws32)[20usize] = ws180;
        (&mut ws32)[21usize] = ws220;
        (&mut ws32)[22usize] = ws260;
        (&mut ws32)[23usize] = ws300;
        (&mut ws32)[24usize] = ws33;
        (&mut ws32)[25usize] = ws70;
        (&mut ws32)[26usize] = ws111;
        (&mut ws32)[27usize] = ws150;
        (&mut ws32)[28usize] = ws190;
        (&mut ws32)[29usize] = ws230;
        (&mut ws32)[30usize] = ws270;
        (&mut ws32)[31usize] = ws310;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws32)[i0 as usize]
            )
        );
        match rb
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b01,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b11,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
                }
            }
            =>
              {
                  (b01[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[0usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b11[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[256usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b21[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[512usize..])[0usize..rateInBytes1 as usize]
                  );
                  (b31[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
                  +
                  rateInBytes1 as usize]).copy_from_slice(
                      &(&(&hbuf)[768usize..])[0usize..rateInBytes1 as usize]
                  )
              }
        };
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            (&s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            (&s)[i1.wrapping_add(15u32) as usize],
                                            (&s)[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    (&s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = (&s)[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = (&s)[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        (&mut s)[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            (&s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            (&s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            (&s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                (&s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = (&s)[0usize];
                (&mut s)[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 64u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    let v07: lib::intvector_intrinsics::vec256 = (&ws32)[0usize];
    let v17: lib::intvector_intrinsics::vec256 = (&ws32)[1usize];
    let v27: lib::intvector_intrinsics::vec256 = (&ws32)[2usize];
    let v37: lib::intvector_intrinsics::vec256 = (&ws32)[3usize];
    let v0·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: lib::intvector_intrinsics::vec256 = v3··7;
    let v08: lib::intvector_intrinsics::vec256 = (&ws32)[4usize];
    let v18: lib::intvector_intrinsics::vec256 = (&ws32)[5usize];
    let v28: lib::intvector_intrinsics::vec256 = (&ws32)[6usize];
    let v38: lib::intvector_intrinsics::vec256 = (&ws32)[7usize];
    let v0·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: lib::intvector_intrinsics::vec256 = v3··8;
    let v09: lib::intvector_intrinsics::vec256 = (&ws32)[8usize];
    let v19: lib::intvector_intrinsics::vec256 = (&ws32)[9usize];
    let v29: lib::intvector_intrinsics::vec256 = (&ws32)[10usize];
    let v39: lib::intvector_intrinsics::vec256 = (&ws32)[11usize];
    let v0·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: lib::intvector_intrinsics::vec256 = v3··9;
    let v010: lib::intvector_intrinsics::vec256 = (&ws32)[12usize];
    let v110: lib::intvector_intrinsics::vec256 = (&ws32)[13usize];
    let v210: lib::intvector_intrinsics::vec256 = (&ws32)[14usize];
    let v310: lib::intvector_intrinsics::vec256 = (&ws32)[15usize];
    let v0·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: lib::intvector_intrinsics::vec256 = v3··10;
    let v011: lib::intvector_intrinsics::vec256 = (&ws32)[16usize];
    let v111: lib::intvector_intrinsics::vec256 = (&ws32)[17usize];
    let v211: lib::intvector_intrinsics::vec256 = (&ws32)[18usize];
    let v311: lib::intvector_intrinsics::vec256 = (&ws32)[19usize];
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: lib::intvector_intrinsics::vec256 = v3··11;
    let v012: lib::intvector_intrinsics::vec256 = (&ws32)[20usize];
    let v112: lib::intvector_intrinsics::vec256 = (&ws32)[21usize];
    let v212: lib::intvector_intrinsics::vec256 = (&ws32)[22usize];
    let v312: lib::intvector_intrinsics::vec256 = (&ws32)[23usize];
    let v0·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: lib::intvector_intrinsics::vec256 = v3··12;
    let v013: lib::intvector_intrinsics::vec256 = (&ws32)[24usize];
    let v113: lib::intvector_intrinsics::vec256 = (&ws32)[25usize];
    let v213: lib::intvector_intrinsics::vec256 = (&ws32)[26usize];
    let v313: lib::intvector_intrinsics::vec256 = (&ws32)[27usize];
    let v0·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: lib::intvector_intrinsics::vec256 = v3··13;
    let v014: lib::intvector_intrinsics::vec256 = (&ws32)[28usize];
    let v114: lib::intvector_intrinsics::vec256 = (&ws32)[29usize];
    let v214: lib::intvector_intrinsics::vec256 = (&ws32)[30usize];
    let v314: lib::intvector_intrinsics::vec256 = (&ws32)[31usize];
    let v0·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: lib::intvector_intrinsics::vec256 = v3··14;
    (&mut ws32)[0usize] = ws00;
    (&mut ws32)[1usize] = ws40;
    (&mut ws32)[2usize] = ws80;
    (&mut ws32)[3usize] = ws120;
    (&mut ws32)[4usize] = ws160;
    (&mut ws32)[5usize] = ws200;
    (&mut ws32)[6usize] = ws240;
    (&mut ws32)[7usize] = ws280;
    (&mut ws32)[8usize] = ws110;
    (&mut ws32)[9usize] = ws50;
    (&mut ws32)[10usize] = ws90;
    (&mut ws32)[11usize] = ws130;
    (&mut ws32)[12usize] = ws170;
    (&mut ws32)[13usize] = ws211;
    (&mut ws32)[14usize] = ws250;
    (&mut ws32)[15usize] = ws290;
    (&mut ws32)[16usize] = ws210;
    (&mut ws32)[17usize] = ws60;
    (&mut ws32)[18usize] = ws100;
    (&mut ws32)[19usize] = ws140;
    (&mut ws32)[20usize] = ws180;
    (&mut ws32)[21usize] = ws220;
    (&mut ws32)[22usize] = ws260;
    (&mut ws32)[23usize] = ws300;
    (&mut ws32)[24usize] = ws33;
    (&mut ws32)[25usize] = ws70;
    (&mut ws32)[26usize] = ws111;
    (&mut ws32)[27usize] = ws150;
    (&mut ws32)[28usize] = ws190;
    (&mut ws32)[29usize] = ws230;
    (&mut ws32)[30usize] = ws270;
    (&mut ws32)[31usize] = ws310;
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&ws32)[i as usize]
        )
    );
    match rb
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              (b01[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
              (b11[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[256usize..])[0usize..remOut as usize]);
              (b21[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[512usize..])[0usize..remOut as usize]);
              (b31[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[768usize..])[0usize..remOut as usize])
          }
    }
}

/**
Allocate quadruple state buffer (200-bytes for each)
*/
pub fn
state_malloc() ->
    Box<[lib::intvector_intrinsics::vec256]>
{
    let buf: Box<[lib::intvector_intrinsics::vec256]> =
        vec![lib::intvector_intrinsics::vec256_zero; 25usize].into_boxed_slice();
    buf
}

/**
Free quadruple state buffer
*/
pub fn
state_free(s: &[lib::intvector_intrinsics::vec256])
{ () }

/**
Absorb number of blocks of 4 input buffers and write the output states

  This function is intended to receive a quadruple hash state and 4 input buffers.
  It processes an inputs of multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block for each buffer are ignored.

  The argument `state` (IN/OUT) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `input0/input1/input2/input3` (IN) point to `inputByteLen` bytes
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]
*/
pub fn
shake128_absorb_nblocks(
    state: &mut [lib::intvector_intrinsics::vec256],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    for i in 0u32..inputByteLen.wrapping_div(168u32)
    {
        let b0: [u8; 256] = [0u8; 256usize];
        let b1: [u8; 256] = [0u8; 256usize];
        let b2: [u8; 256] = [0u8; 256usize];
        let b3: [u8; 256] = [0u8; 256usize];
        let mut b·: crate::sha2_types::uint8_4p =
            crate::sha2_types::uint8_4p
            {
                fst: &b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
            };
        let b00: &[u8] = input0;
        let b10: &[u8] = input1;
        let b20: &[u8] = input2;
        let b30: &[u8] = input3;
        match b·
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut bl0,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut bl1,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
                }
            }
            =>
              {
                  (bl0[0usize..168usize]).copy_from_slice(
                      &(&b00[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
                  );
                  (bl1[0usize..168usize]).copy_from_slice(
                      &(&b10[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
                  );
                  (bl2[0usize..168usize]).copy_from_slice(
                      &(&b20[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
                  );
                  (bl3[0usize..168usize]).copy_from_slice(
                      &(&b30[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
                  )
              }
        };
        absorb_inner_256(168u32, b·, state)
    }
}

/**
Absorb a final partial blocks of 4 input buffers and write the output states

  This function is intended to receive a quadruple hash state and 4 input buffers.
  It processes a sequence of bytes at end of each input buffer that is less
  than 168-bytes (SHAKE128 block size),
  any bytes of full blocks at start of input buffers are ignored.

  The argument `state` (IN/OUT) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `input0/input1/input2/input3` (IN) point to `inputByteLen` bytes
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]

  Note: Full size of input buffers must be passed to `inputByteLen` including
  the number of full-block bytes at start of each input buffer that are ignored
*/
pub fn
shake128_absorb_final(
    state: &mut [lib::intvector_intrinsics::vec256],
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8],
    inputByteLen: u32
)
{
    let b0: [u8; 256] = [0u8; 256usize];
    let b1: [u8; 256] = [0u8; 256usize];
    let b2: [u8; 256] = [0u8; 256usize];
    let b3: [u8; 256] = [0u8; 256usize];
    let mut b·: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b1, snd: crate::sha2_types::uint8_2p { fst: &b2, snd: &b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(168u32);
    let b00: &[u8] = input0;
    let b10: &[u8] = input1;
    let b20: &[u8] = input2;
    let b30: &[u8] = input3;
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut bl0,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut bl1,
                snd: crate::sha2_types::uint8_2p { fst: ref mut bl2, snd: ref mut bl3 }
            }
        }
        =>
          {
              (bl0[0usize..rem as usize]).copy_from_slice(
                  &(&b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
              );
              (bl1[0usize..rem as usize]).copy_from_slice(
                  &(&b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
              );
              (bl2[0usize..rem as usize]).copy_from_slice(
                  &(&b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
              );
              (bl3[0usize..rem as usize]).copy_from_slice(
                  &(&b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
              )
          }
    };
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b01,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b11,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b21, snd: ref mut b31 }
            }
        }
        =>
          {
              b01[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
              b11[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
              b21[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
              b31[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8
          }
    };
    let mut ws: [lib::intvector_intrinsics::vec256; 32] =
        [lib::intvector_intrinsics::vec256_zero; 32usize];
    match b·
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b01,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b11, snd: crate::sha2_types::uint8_2p { fst: ref b21, snd: ref b31 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_le(&b01[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_le(&b11[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_le(&b21[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_le(&b31[0usize..]);
              (&mut ws)[4usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[32usize..]);
              (&mut ws)[5usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[32usize..]);
              (&mut ws)[6usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[32usize..]);
              (&mut ws)[7usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[32usize..]);
              (&mut ws)[8usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[64usize..]);
              (&mut ws)[9usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[64usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[64usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[64usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[96usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[96usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[96usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[96usize..]);
              (&mut ws)[16usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[128usize..]);
              (&mut ws)[17usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[128usize..]);
              (&mut ws)[18usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[128usize..]);
              (&mut ws)[19usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[128usize..]);
              (&mut ws)[20usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[160usize..]);
              (&mut ws)[21usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[160usize..]);
              (&mut ws)[22usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[160usize..]);
              (&mut ws)[23usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[160usize..]);
              (&mut ws)[24usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[192usize..]);
              (&mut ws)[25usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[192usize..]);
              (&mut ws)[26usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[192usize..]);
              (&mut ws)[27usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[192usize..]);
              (&mut ws)[28usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b01[224usize..]);
              (&mut ws)[29usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b11[224usize..]);
              (&mut ws)[30usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b21[224usize..]);
              (&mut ws)[31usize] =
                  lib::intvector_intrinsics::vec256_load64_le(&b31[224usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
    let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
    let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
    let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
    let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
    let v0·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: lib::intvector_intrinsics::vec256 = v3··3;
    let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
    let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
    let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
    let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: lib::intvector_intrinsics::vec256 = v3··4;
    let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
    let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
    let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
    let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
    let v0·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: lib::intvector_intrinsics::vec256 = v3··5;
    let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
    let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
    let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
    let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
    let v0·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: lib::intvector_intrinsics::vec256 = v3··6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    (&mut ws)[16usize] = ws16;
    (&mut ws)[17usize] = ws17;
    (&mut ws)[18usize] = ws18;
    (&mut ws)[19usize] = ws19;
    (&mut ws)[20usize] = ws20;
    (&mut ws)[21usize] = ws21;
    (&mut ws)[22usize] = ws22;
    (&mut ws)[23usize] = ws23;
    (&mut ws)[24usize] = ws24;
    (&mut ws)[25usize] = ws25;
    (&mut ws)[26usize] = ws26;
    (&mut ws)[27usize] = ws27;
    (&mut ws)[28usize] = ws28;
    (&mut ws)[29usize] = ws29;
    (&mut ws)[30usize] = ws30;
    (&mut ws)[31usize] = ws31;
    krml::unroll_for!(
        25,
        "i",
        0u32,
        1u32,
        state[i as usize] =
            lib::intvector_intrinsics::vec256_xor(state[i as usize], (&ws)[i as usize])
    );
    let b01: [u8; 256] = [0u8; 256usize];
    let b11: [u8; 256] = [0u8; 256usize];
    let b21: [u8; 256] = [0u8; 256usize];
    let b31: [u8; 256] = [0u8; 256usize];
    let mut b: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: &b01,
            snd:
            crate::sha2_types::uint8_3p
            { fst: &b11, snd: crate::sha2_types::uint8_2p { fst: &b21, snd: &b31 } }
        };
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b02,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b12,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b22, snd: ref mut b32 }
            }
        }
        =>
          {
              b02[167usize] = 0x80u8;
              b12[167usize] = 0x80u8;
              b22[167usize] = 0x80u8;
              b32[167usize] = 0x80u8
          }
    };
    absorb_inner_256(168u32, b, state)
}

/**
Squeeze a quadruple hash state to 4 output buffers

  This function is intended to receive a quadruple hash state and 4 output buffers.
  It produces 4 outputs, each is multiple of 168-bytes (SHAKE128 block size),
  any additional bytes of final partial block for each buffer are ignored.

  The argument `state` (IN) points to quadruple hash state,
  i.e., Lib_IntVector_Intrinsics_vec256[25]
  The arguments `output0/output1/output2/output3` (OUT) point to `outputByteLen` bytes
  of valid memory for each buffer, i.e., uint8_t[inputByteLen]
*/
pub fn
shake128_squeeze_nblocks(
    state: &mut [lib::intvector_intrinsics::vec256],
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    outputByteLen: u32
)
{
    for i in 0u32..outputByteLen.wrapping_div(168u32)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws: [lib::intvector_intrinsics::vec256; 32] =
            [lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws)[0usize..25usize]).copy_from_slice(&state[0usize..25usize]);
        let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
        let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
        let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
        let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
        let v0·: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
        let v1·: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
        let v2·: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
        let v3·: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
        let v0··: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
        let v1··: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
        let v2··: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
        let v3··: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
        let ws0: lib::intvector_intrinsics::vec256 = v0··;
        let ws1: lib::intvector_intrinsics::vec256 = v2··;
        let ws2: lib::intvector_intrinsics::vec256 = v1··;
        let ws3: lib::intvector_intrinsics::vec256 = v3··;
        let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
        let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
        let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
        let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
        let v0·0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
        let v1·0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
        let v2·0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
        let v3·0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
        let v0··0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
        let v1··0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
        let v2··0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
        let v3··0: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
        let ws4: lib::intvector_intrinsics::vec256 = v0··0;
        let ws5: lib::intvector_intrinsics::vec256 = v2··0;
        let ws6: lib::intvector_intrinsics::vec256 = v1··0;
        let ws7: lib::intvector_intrinsics::vec256 = v3··0;
        let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
        let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
        let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
        let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
        let v0·1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
        let v1·1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
        let v2·1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
        let v3·1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
        let v0··1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
        let v1··1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
        let v2··1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
        let v3··1: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
        let ws8: lib::intvector_intrinsics::vec256 = v0··1;
        let ws9: lib::intvector_intrinsics::vec256 = v2··1;
        let ws10: lib::intvector_intrinsics::vec256 = v1··1;
        let ws11: lib::intvector_intrinsics::vec256 = v3··1;
        let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
        let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
        let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
        let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
        let v0·2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
        let v1·2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
        let v2·2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
        let v3·2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
        let v0··2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
        let v1··2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
        let v2··2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
        let v3··2: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
        let ws12: lib::intvector_intrinsics::vec256 = v0··2;
        let ws13: lib::intvector_intrinsics::vec256 = v2··2;
        let ws14: lib::intvector_intrinsics::vec256 = v1··2;
        let ws15: lib::intvector_intrinsics::vec256 = v3··2;
        let v03: lib::intvector_intrinsics::vec256 = (&ws)[16usize];
        let v13: lib::intvector_intrinsics::vec256 = (&ws)[17usize];
        let v23: lib::intvector_intrinsics::vec256 = (&ws)[18usize];
        let v33: lib::intvector_intrinsics::vec256 = (&ws)[19usize];
        let v0·3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
        let v1·3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
        let v2·3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
        let v3·3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
        let v0··3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
        let v1··3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
        let v2··3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
        let v3··3: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
        let ws16: lib::intvector_intrinsics::vec256 = v0··3;
        let ws17: lib::intvector_intrinsics::vec256 = v2··3;
        let ws18: lib::intvector_intrinsics::vec256 = v1··3;
        let ws19: lib::intvector_intrinsics::vec256 = v3··3;
        let v04: lib::intvector_intrinsics::vec256 = (&ws)[20usize];
        let v14: lib::intvector_intrinsics::vec256 = (&ws)[21usize];
        let v24: lib::intvector_intrinsics::vec256 = (&ws)[22usize];
        let v34: lib::intvector_intrinsics::vec256 = (&ws)[23usize];
        let v0·4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
        let v1·4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
        let v2·4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
        let v3·4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
        let v0··4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
        let v1··4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
        let v2··4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
        let v3··4: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
        let ws20: lib::intvector_intrinsics::vec256 = v0··4;
        let ws21: lib::intvector_intrinsics::vec256 = v2··4;
        let ws22: lib::intvector_intrinsics::vec256 = v1··4;
        let ws23: lib::intvector_intrinsics::vec256 = v3··4;
        let v05: lib::intvector_intrinsics::vec256 = (&ws)[24usize];
        let v15: lib::intvector_intrinsics::vec256 = (&ws)[25usize];
        let v25: lib::intvector_intrinsics::vec256 = (&ws)[26usize];
        let v35: lib::intvector_intrinsics::vec256 = (&ws)[27usize];
        let v0·5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
        let v1·5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
        let v2·5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
        let v3·5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
        let v0··5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
        let v1··5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
        let v2··5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
        let v3··5: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
        let ws24: lib::intvector_intrinsics::vec256 = v0··5;
        let ws25: lib::intvector_intrinsics::vec256 = v2··5;
        let ws26: lib::intvector_intrinsics::vec256 = v1··5;
        let ws27: lib::intvector_intrinsics::vec256 = v3··5;
        let v06: lib::intvector_intrinsics::vec256 = (&ws)[28usize];
        let v16: lib::intvector_intrinsics::vec256 = (&ws)[29usize];
        let v26: lib::intvector_intrinsics::vec256 = (&ws)[30usize];
        let v36: lib::intvector_intrinsics::vec256 = (&ws)[31usize];
        let v0·6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
        let v1·6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
        let v2·6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
        let v3·6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
        let v0··6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
        let v1··6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
        let v2··6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
        let v3··6: lib::intvector_intrinsics::vec256 =
            lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
        let ws28: lib::intvector_intrinsics::vec256 = v0··6;
        let ws29: lib::intvector_intrinsics::vec256 = v2··6;
        let ws30: lib::intvector_intrinsics::vec256 = v1··6;
        let ws31: lib::intvector_intrinsics::vec256 = v3··6;
        (&mut ws)[0usize] = ws0;
        (&mut ws)[1usize] = ws4;
        (&mut ws)[2usize] = ws8;
        (&mut ws)[3usize] = ws12;
        (&mut ws)[4usize] = ws16;
        (&mut ws)[5usize] = ws20;
        (&mut ws)[6usize] = ws24;
        (&mut ws)[7usize] = ws28;
        (&mut ws)[8usize] = ws1;
        (&mut ws)[9usize] = ws5;
        (&mut ws)[10usize] = ws9;
        (&mut ws)[11usize] = ws13;
        (&mut ws)[12usize] = ws17;
        (&mut ws)[13usize] = ws21;
        (&mut ws)[14usize] = ws25;
        (&mut ws)[15usize] = ws29;
        (&mut ws)[16usize] = ws2;
        (&mut ws)[17usize] = ws6;
        (&mut ws)[18usize] = ws10;
        (&mut ws)[19usize] = ws14;
        (&mut ws)[20usize] = ws18;
        (&mut ws)[21usize] = ws22;
        (&mut ws)[22usize] = ws26;
        (&mut ws)[23usize] = ws30;
        (&mut ws)[24usize] = ws3;
        (&mut ws)[25usize] = ws7;
        (&mut ws)[26usize] = ws11;
        (&mut ws)[27usize] = ws15;
        (&mut ws)[28usize] = ws19;
        (&mut ws)[29usize] = ws23;
        (&mut ws)[30usize] = ws27;
        (&mut ws)[31usize] = ws31;
        krml::unroll_for!(
            32,
            "i0",
            0u32,
            1u32,
            lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&ws)[i0 as usize]
            )
        );
        let b0: &mut [u8] = output0;
        let b1: &mut [u8] = output1;
        let b2: &mut [u8] = output2;
        let b3: &mut [u8] = output3;
        (b0[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&(&hbuf)[0usize..])[0usize..168usize]
        );
        (b1[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&(&hbuf)[256usize..])[0usize..168usize]
        );
        (b2[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&(&hbuf)[512usize..])[0usize..168usize]
        );
        (b3[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&(&hbuf)[768usize..])[0usize..168usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [lib::intvector_intrinsics::vec256; 5] =
                    [lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(0u32) as usize];
                        let uu____1: lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(5u32) as usize];
                        let uu____2: lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        lib::intvector_intrinsics::vec256_xor(
                                            state[i1.wrapping_add(15u32) as usize],
                                            state[i1.wrapping_add(20u32) as usize]
                                        )
                                    )
                                )
                            )
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____3: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: lib::intvector_intrinsics::vec256 =
                            (&_C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                lib::intvector_intrinsics::vec256_or(
                                    lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    lib::intvector_intrinsics::vec256_shift_right64(
                                        uu____4,
                                        63u32
                                    )
                                )
                            );
                        krml::unroll_for!(
                            5,
                            "i2",
                            0u32,
                            1u32,
                            state[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize] =
                                lib::intvector_intrinsics::vec256_xor(
                                    state[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: lib::intvector_intrinsics::vec256 = state[1usize];
                let mut current: [lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: lib::intvector_intrinsics::vec256 = state[_Y as usize];
                        let uu____5: lib::intvector_intrinsics::vec256 = (&current)[0usize];
                        state[_Y as usize] =
                            lib::intvector_intrinsics::vec256_or(
                                lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                lib::intvector_intrinsics::vec256_shift_right64(
                                    uu____5,
                                    64u32.wrapping_sub(r)
                                )
                            );
                        (&mut current)[0usize] = temp
                    }
                );
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____6: lib::intvector_intrinsics::vec256 =
                            state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v07: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: lib::intvector_intrinsics::vec256 =
                            state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v17: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: lib::intvector_intrinsics::vec256 =
                            state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v27: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: lib::intvector_intrinsics::vec256 =
                            state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v37: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: lib::intvector_intrinsics::vec256 =
                            state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_lognot(
                                state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v07;
                        state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v17;
                        state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v27;
                        state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v37;
                        state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: lib::intvector_intrinsics::vec256 = state[0usize];
                state[0usize] =
                    lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    }
}
