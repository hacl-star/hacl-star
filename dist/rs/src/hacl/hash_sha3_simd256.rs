#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn absorb_inner_256(
    rateInBytes: u32,
    b: crate::hacl::sha2_types::uint8_4p,
    s: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    crate::lowstar::ignore::ignore::<u32>(rateInBytes);
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b3: &mut [u8] = b.snd.snd.snd;
    let b2: &mut [u8] = b.snd.snd.fst;
    let b1: &mut [u8] = b.snd.fst;
    let b0: &mut [u8] = b.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b0[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b1[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b2[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b3[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(s[i as usize], (&mut ws)[i as usize])
    );
    krml::unroll_for!(
        24,
        "i",
        0u32,
        1u32,
        {
            let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
            krml::unroll_for!(
                5,
                "i0",
                0u32,
                1u32,
                {
                    let uu____0: crate::lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(0u32) as usize];
                    let uu____1: crate::lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(5u32) as usize];
                    let uu____2: crate::lib::intvector_intrinsics::vec256 =
                        s[i0.wrapping_add(10u32) as usize];
                    (&mut _C)[i0 as usize] =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____0,
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____1,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____2,
                                    crate::lib::intvector_intrinsics::vec256_xor(
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
                    let uu____3: crate::lib::intvector_intrinsics::vec256 =
                        (&mut _C)[i0.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                    let uu____4: crate::lib::intvector_intrinsics::vec256 =
                        (&mut _C)[i0.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                    let _D: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____3,
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____4, 1u32),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                            crate::lib::intvector_intrinsics::vec256_xor(
                                s[i0.wrapping_add(5u32.wrapping_mul(i1)) as usize],
                                _D
                            )
                    )
                }
            );
            let x: crate::lib::intvector_intrinsics::vec256 = s[1usize];
            let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
            krml::unroll_for!(
                24,
                "i0",
                0u32,
                1u32,
                {
                    let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i0 as usize];
                    let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i0 as usize];
                    let temp: crate::lib::intvector_intrinsics::vec256 = s[_Y as usize];
                    let uu____5: crate::lib::intvector_intrinsics::vec256 = (&mut current)[0usize];
                    s[_Y as usize] =
                        crate::lib::intvector_intrinsics::vec256_or(
                            crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                            crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                    let uu____6: crate::lib::intvector_intrinsics::vec256 =
                        s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____7: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_lognot(
                            s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v07: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____6,
                            crate::lib::intvector_intrinsics::vec256_and(
                                uu____7,
                                s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____8: crate::lib::intvector_intrinsics::vec256 =
                        s[1u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____9: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_lognot(
                            s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v17: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____8,
                            crate::lib::intvector_intrinsics::vec256_and(
                                uu____9,
                                s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____10: crate::lib::intvector_intrinsics::vec256 =
                        s[2u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____11: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_lognot(
                            s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v27: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____10,
                            crate::lib::intvector_intrinsics::vec256_and(
                                uu____11,
                                s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____12: crate::lib::intvector_intrinsics::vec256 =
                        s[3u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____13: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_lognot(
                            s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v37: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____12,
                            crate::lib::intvector_intrinsics::vec256_and(
                                uu____13,
                                s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                            )
                        );
                    let uu____14: crate::lib::intvector_intrinsics::vec256 =
                        s[4u32.wrapping_add(5u32.wrapping_mul(i0)) as usize];
                    let uu____15: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_lognot(
                            s[0u32.wrapping_add(5u32.wrapping_mul(i0)) as usize]
                        );
                    let v4: crate::lib::intvector_intrinsics::vec256 =
                        crate::lib::intvector_intrinsics::vec256_xor(
                            uu____14,
                            crate::lib::intvector_intrinsics::vec256_and(
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
            let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i as usize];
            let uu____16: crate::lib::intvector_intrinsics::vec256 = s[0usize];
            s[0usize] =
                crate::lib::intvector_intrinsics::vec256_xor(
                    uu____16,
                    crate::lib::intvector_intrinsics::vec256_load64(c)
                )
        }
    )
}

pub fn shake128(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    outputByteLen: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 168u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]);
    (b15[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]);
    (b25[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]);
    (b35[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize])
}

pub fn shake256(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    outputByteLen: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x1Fu8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..outputByteLen.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = outputByteLen.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]);
    (b15[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]);
    (b25[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]);
    (b35[outputByteLen.wrapping_sub(remOut) as usize..outputByteLen.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize])
}

pub fn sha3_224(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 144u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..28u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 28u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    );
    (b15[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]
    );
    (b25[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]
    );
    (b35[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_256(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 136u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..32u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 32u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    );
    (b15[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]
    );
    (b25[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]
    );
    (b35[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_384(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 104u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..48u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 48u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    );
    (b15[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]
    );
    (b25[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]
    );
    (b35[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize]
    )
}

pub fn sha3_512(
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let ib: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: input1, snd: crate::hacl::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: output0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: output1, snd: crate::hacl::sha2_types::uint8_2p { fst: output2, snd: output3 } }
        };
    let mut s: [crate::lib::intvector_intrinsics::vec256; 25] =
        [crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    let rateInBytes1: u32 = 72u32;
    for i in 0u32..inputByteLen.wrapping_div(rateInBytes1)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b30: &mut [u8] = ib.snd.snd.snd;
        let b20: &mut [u8] = ib.snd.snd.fst;
        let b10: &mut [u8] = ib.snd.fst;
        let b00: &mut [u8] = ib.fst;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl1[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl2[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        (bl3[0usize..rateInBytes1 as usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(rateInBytes1) as usize..])[0usize..rateInBytes1 as usize]
        );
        absorb_inner_256(rateInBytes1, b·, &mut s)
    };
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(rateInBytes1);
    let b30: &mut [u8] = ib.snd.snd.snd;
    let b20: &mut [u8] = ib.snd.snd.fst;
    let b10: &mut [u8] = ib.snd.fst;
    let b00: &mut [u8] = ib.fst;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b11[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b21[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    b31[inputByteLen.wrapping_rem(rateInBytes1) as usize] = 0x06u8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(
                (&mut s)[i as usize],
                (&mut ws)[i as usize]
            )
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b14[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b24[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    b34[rateInBytes1.wrapping_sub(1u32) as usize] = 0x80u8;
    absorb_inner_256(rateInBytes1, b, &mut s);
    for i in 0u32..64u32.wrapping_div(rateInBytes1)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
        let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
        let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
        let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
        let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
        let v0·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
        let v1·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
        let v2·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
        let v3·7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
        let v0··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
        let v1··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
        let v2··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
        let v3··7: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
        let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
        let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
        let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
        let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
        let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
        let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
        let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
        let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
        let v0·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
        let v1·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
        let v2·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
        let v3·8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
        let v0··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
        let v1··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
        let v2··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
        let v3··8: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
        let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
        let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
        let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
        let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
        let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
        let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
        let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
        let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
        let v0·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
        let v1·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
        let v2·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
        let v3·9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
        let v0··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
        let v1··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
        let v2··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
        let v3··9: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
        let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
        let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
        let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
        let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
        let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
        let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
        let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
        let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
        let v0·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
        let v1·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
        let v2·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
        let v3·10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
        let v0··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
        let v1··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
        let v2··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
        let v3··10: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
        let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
        let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
        let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
        let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
        let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
        let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
        let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
        let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
        let v0·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
        let v1·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
        let v2·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
        let v3·11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
        let v0··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
        let v1··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
        let v2··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
        let v3··11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
        let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
        let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
        let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
        let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
        let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
        let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
        let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
        let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
        let v0·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
        let v1·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
        let v2·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
        let v3·12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
        let v0··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
        let v1··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
        let v2··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
        let v3··12: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
        let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
        let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
        let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
        let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
        let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
        let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
        let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
        let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
        let v0·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
        let v1·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
        let v2·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
        let v3·13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
        let v0··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
        let v1··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
        let v2··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
        let v3··13: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
        let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
        let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
        let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
        let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
        let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
        let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
        let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
        let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
        let v0·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
        let v1·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
        let v2·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
        let v3·14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
        let v0··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
        let v1··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
        let v2··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
        let v3··14: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
        let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
        let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
        let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
        let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws32)[i0 as usize]
            )
        );
        let b35: &mut [u8] = rb.snd.snd.snd;
        let b25: &mut [u8] = rb.snd.snd.fst;
        let b15: &mut [u8] = rb.snd.fst;
        let b05: &mut [u8] = rb.fst;
        (b05[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..rateInBytes1 as usize]
        );
        (b15[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..rateInBytes1 as usize]
        );
        (b25[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..rateInBytes1 as usize]
        );
        (b35[i.wrapping_mul(rateInBytes1) as usize..i.wrapping_mul(rateInBytes1) as usize
        +
        rateInBytes1 as usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..rateInBytes1 as usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
                                            (&mut s)[i1.wrapping_add(15u32) as usize],
                                            (&mut s)[i1.wrapping_add(20u32) as usize]
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    (&mut s)[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = (&mut s)[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = (&mut s)[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        (&mut s)[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v015: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v115: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v215: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v315: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____15,
                                    (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        (&mut s)[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v015;
                        (&mut s)[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v115;
                        (&mut s)[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v215;
                        (&mut s)[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v315;
                        (&mut s)[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize] = v4
                    }
                );
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = (&mut s)[0usize];
                (&mut s)[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    };
    let remOut: u32 = 64u32.wrapping_rem(rateInBytes1);
    let mut hbuf: [u8; 1024] = [0u8; 1024usize];
    let mut ws32: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    ((&mut ws32)[0usize..25usize]).copy_from_slice(&(&mut s)[0usize..25usize]);
    let v07: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[0usize];
    let v17: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[1usize];
    let v27: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[2usize];
    let v37: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[3usize];
    let v0·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v07, v17);
    let v1·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v07, v17);
    let v2·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v27, v37);
    let v3·7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v27, v37);
    let v0··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·7, v2·7);
    let v1··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·7, v2·7);
    let v2··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·7, v3·7);
    let v3··7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·7, v3·7);
    let ws00: crate::lib::intvector_intrinsics::vec256 = v0··7;
    let ws110: crate::lib::intvector_intrinsics::vec256 = v2··7;
    let ws210: crate::lib::intvector_intrinsics::vec256 = v1··7;
    let ws33: crate::lib::intvector_intrinsics::vec256 = v3··7;
    let v08: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[4usize];
    let v18: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[5usize];
    let v28: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[6usize];
    let v38: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[7usize];
    let v0·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v08, v18);
    let v1·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v08, v18);
    let v2·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v28, v38);
    let v3·8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v28, v38);
    let v0··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·8, v2·8);
    let v1··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·8, v2·8);
    let v2··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·8, v3·8);
    let v3··8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·8, v3·8);
    let ws40: crate::lib::intvector_intrinsics::vec256 = v0··8;
    let ws50: crate::lib::intvector_intrinsics::vec256 = v2··8;
    let ws60: crate::lib::intvector_intrinsics::vec256 = v1··8;
    let ws70: crate::lib::intvector_intrinsics::vec256 = v3··8;
    let v09: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[8usize];
    let v19: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[9usize];
    let v29: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[10usize];
    let v39: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[11usize];
    let v0·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v09, v19);
    let v1·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v09, v19);
    let v2·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v29, v39);
    let v3·9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v29, v39);
    let v0··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·9, v2·9);
    let v1··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·9, v2·9);
    let v2··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·9, v3·9);
    let v3··9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·9, v3·9);
    let ws80: crate::lib::intvector_intrinsics::vec256 = v0··9;
    let ws90: crate::lib::intvector_intrinsics::vec256 = v2··9;
    let ws100: crate::lib::intvector_intrinsics::vec256 = v1··9;
    let ws111: crate::lib::intvector_intrinsics::vec256 = v3··9;
    let v010: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[12usize];
    let v110: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[13usize];
    let v210: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[14usize];
    let v310: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[15usize];
    let v0·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v010, v110);
    let v1·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v010, v110);
    let v2·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v210, v310);
    let v3·10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v210, v310);
    let v0··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v2·10);
    let v1··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v2·10);
    let v2··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v3·10);
    let v3··10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v3·10);
    let ws120: crate::lib::intvector_intrinsics::vec256 = v0··10;
    let ws130: crate::lib::intvector_intrinsics::vec256 = v2··10;
    let ws140: crate::lib::intvector_intrinsics::vec256 = v1··10;
    let ws150: crate::lib::intvector_intrinsics::vec256 = v3··10;
    let v011: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[16usize];
    let v111: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[17usize];
    let v211: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[18usize];
    let v311: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[19usize];
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v011, v111);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v011, v111);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v211, v311);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v211, v311);
    let v0··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·11, v2·11);
    let v1··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·11, v2·11);
    let v2··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·11, v3·11);
    let v3··11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·11, v3·11);
    let ws160: crate::lib::intvector_intrinsics::vec256 = v0··11;
    let ws170: crate::lib::intvector_intrinsics::vec256 = v2··11;
    let ws180: crate::lib::intvector_intrinsics::vec256 = v1··11;
    let ws190: crate::lib::intvector_intrinsics::vec256 = v3··11;
    let v012: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[20usize];
    let v112: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[21usize];
    let v212: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[22usize];
    let v312: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[23usize];
    let v0·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v012, v112);
    let v1·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v012, v112);
    let v2·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v212, v312);
    let v3·12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v212, v312);
    let v0··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v2·12);
    let v1··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v2·12);
    let v2··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v3·12);
    let v3··12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v3·12);
    let ws200: crate::lib::intvector_intrinsics::vec256 = v0··12;
    let ws211: crate::lib::intvector_intrinsics::vec256 = v2··12;
    let ws220: crate::lib::intvector_intrinsics::vec256 = v1··12;
    let ws230: crate::lib::intvector_intrinsics::vec256 = v3··12;
    let v013: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[24usize];
    let v113: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[25usize];
    let v213: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[26usize];
    let v313: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[27usize];
    let v0·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v013, v113);
    let v1·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v013, v113);
    let v2·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v213, v313);
    let v3·13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v213, v313);
    let v0··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·13, v2·13);
    let v1··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·13, v2·13);
    let v2··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·13, v3·13);
    let v3··13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·13, v3·13);
    let ws240: crate::lib::intvector_intrinsics::vec256 = v0··13;
    let ws250: crate::lib::intvector_intrinsics::vec256 = v2··13;
    let ws260: crate::lib::intvector_intrinsics::vec256 = v1··13;
    let ws270: crate::lib::intvector_intrinsics::vec256 = v3··13;
    let v014: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[28usize];
    let v114: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[29usize];
    let v214: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[30usize];
    let v314: crate::lib::intvector_intrinsics::vec256 = (&mut ws32)[31usize];
    let v0·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v014, v114);
    let v1·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v014, v114);
    let v2·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v214, v314);
    let v3·14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v214, v314);
    let v0··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·14, v2·14);
    let v1··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·14, v2·14);
    let v2··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·14, v3·14);
    let v3··14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·14, v3·14);
    let ws280: crate::lib::intvector_intrinsics::vec256 = v0··14;
    let ws290: crate::lib::intvector_intrinsics::vec256 = v2··14;
    let ws300: crate::lib::intvector_intrinsics::vec256 = v1··14;
    let ws310: crate::lib::intvector_intrinsics::vec256 = v3··14;
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
        crate::lib::intvector_intrinsics::vec256_store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            (&mut ws32)[i as usize]
        )
    );
    let b35: &mut [u8] = rb.snd.snd.snd;
    let b25: &mut [u8] = rb.snd.snd.fst;
    let b15: &mut [u8] = rb.snd.fst;
    let b05: &mut [u8] = rb.fst;
    (b05[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[0usize..])[0usize..remOut as usize]
    );
    (b15[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[256usize..])[0usize..remOut as usize]
    );
    (b25[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[512usize..])[0usize..remOut as usize]
    );
    (b35[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize + remOut as usize]).copy_from_slice(
        &(&mut (&mut hbuf)[768usize..])[0usize..remOut as usize]
    )
}

pub fn state_malloc() -> Vec<crate::lib::intvector_intrinsics::vec256>
{
    let mut buf: Vec<crate::lib::intvector_intrinsics::vec256> =
        vec![crate::lib::intvector_intrinsics::vec256_zero; 25usize];
    buf
}

pub fn state_free(s: &mut [crate::lib::intvector_intrinsics::vec256]) -> () { () }

pub fn shake128_absorb_nblocks(
    state: &mut [crate::lib::intvector_intrinsics::vec256],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    for i in 0u32..inputByteLen.wrapping_div(168u32)
    {
        let mut b0: [u8; 256] = [0u8; 256usize];
        let mut b1: [u8; 256] = [0u8; 256usize];
        let mut b2: [u8; 256] = [0u8; 256usize];
        let mut b3: [u8; 256] = [0u8; 256usize];
        let b·: crate::hacl::sha2_types::uint8_4p =
            crate::hacl::sha2_types::uint8_4p
            {
                fst: &mut b0,
                snd:
                crate::hacl::sha2_types::uint8_3p
                {
                    fst: &mut b1,
                    snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 }
                }
            };
        let b00: &mut [u8] = input0;
        let b10: &mut [u8] = input1;
        let b20: &mut [u8] = input2;
        let b30: &mut [u8] = input3;
        let bl3: &mut [u8] = b·.snd.snd.snd;
        let bl2: &mut [u8] = b·.snd.snd.fst;
        let bl1: &mut [u8] = b·.snd.fst;
        let bl0: &mut [u8] = b·.fst;
        (bl0[0usize..168usize]).copy_from_slice(
            &(&mut b00[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
        );
        (bl1[0usize..168usize]).copy_from_slice(
            &(&mut b10[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
        );
        (bl2[0usize..168usize]).copy_from_slice(
            &(&mut b20[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
        );
        (bl3[0usize..168usize]).copy_from_slice(
            &(&mut b30[i.wrapping_mul(168u32) as usize..])[0usize..168usize]
        );
        absorb_inner_256(168u32, b·, state)
    }
}

pub fn shake128_absorb_final(
    state: &mut [crate::lib::intvector_intrinsics::vec256],
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    inputByteLen: u32
) ->
    ()
{
    let mut b0: [u8; 256] = [0u8; 256usize];
    let mut b1: [u8; 256] = [0u8; 256usize];
    let mut b2: [u8; 256] = [0u8; 256usize];
    let mut b3: [u8; 256] = [0u8; 256usize];
    let b·: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b0,
            snd:
            crate::hacl::sha2_types::uint8_3p
            { fst: &mut b1, snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b2, snd: &mut b3 } }
        };
    let rem: u32 = inputByteLen.wrapping_rem(168u32);
    let b00: &mut [u8] = input0;
    let b10: &mut [u8] = input1;
    let b20: &mut [u8] = input2;
    let b30: &mut [u8] = input3;
    let bl3: &mut [u8] = b·.snd.snd.snd;
    let bl2: &mut [u8] = b·.snd.snd.fst;
    let bl1: &mut [u8] = b·.snd.fst;
    let bl0: &mut [u8] = b·.fst;
    (bl0[0usize..rem as usize]).copy_from_slice(
        &(&mut b00[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl1[0usize..rem as usize]).copy_from_slice(
        &(&mut b10[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl2[0usize..rem as usize]).copy_from_slice(
        &(&mut b20[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    (bl3[0usize..rem as usize]).copy_from_slice(
        &(&mut b30[inputByteLen.wrapping_sub(rem) as usize..])[0usize..rem as usize]
    );
    let b31: &mut [u8] = b·.snd.snd.snd;
    let b21: &mut [u8] = b·.snd.snd.fst;
    let b11: &mut [u8] = b·.snd.fst;
    let b01: &mut [u8] = b·.fst;
    b01[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
    b11[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
    b21[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
    b31[inputByteLen.wrapping_rem(168u32) as usize] = 0x1Fu8;
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
        [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
    let b32: &mut [u8] = b·.snd.snd.snd;
    let b22: &mut [u8] = b·.snd.snd.fst;
    let b12: &mut [u8] = b·.snd.fst;
    let b02: &mut [u8] = b·.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[96usize..]);
    (&mut ws)[16usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[128usize..]);
    (&mut ws)[17usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[128usize..]);
    (&mut ws)[18usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[128usize..]);
    (&mut ws)[19usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[128usize..]);
    (&mut ws)[20usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[160usize..]);
    (&mut ws)[21usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[160usize..]);
    (&mut ws)[22usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[160usize..]);
    (&mut ws)[23usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[160usize..]);
    (&mut ws)[24usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[192usize..]);
    (&mut ws)[25usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[192usize..]);
    (&mut ws)[26usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[192usize..]);
    (&mut ws)[27usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[192usize..]);
    (&mut ws)[28usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b02[224usize..]);
    (&mut ws)[29usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b12[224usize..]);
    (&mut ws)[30usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b22[224usize..]);
    (&mut ws)[31usize] = crate::lib::intvector_intrinsics::vec256_load64_le(&mut b32[224usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
    let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
    let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
    let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
    let v0·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
    let v1·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
    let v2·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
    let v3·3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
    let v0··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
    let v1··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
    let v2··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
    let v3··3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
    let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
    let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
    let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
    let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
    let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
    let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
    let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
    let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
    let v0··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
    let v1··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
    let v2··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
    let v3··4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
    let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
    let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
    let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
    let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
    let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
    let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
    let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
    let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
    let v0·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
    let v1·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
    let v2·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
    let v3·5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
    let v0··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
    let v1··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
    let v2··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
    let v3··5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
    let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
    let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
    let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
    let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
    let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
    let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
    let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
    let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
    let v0·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
    let v1·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
    let v2·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
    let v3·6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
    let v0··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
    let v1··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
    let v2··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
    let v3··6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
    let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
    let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
    let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
    let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_xor(state[i as usize], (&mut ws)[i as usize])
    );
    let mut b03: [u8; 256] = [0u8; 256usize];
    let mut b13: [u8; 256] = [0u8; 256usize];
    let mut b23: [u8; 256] = [0u8; 256usize];
    let mut b33: [u8; 256] = [0u8; 256usize];
    let b: crate::hacl::sha2_types::uint8_4p =
        crate::hacl::sha2_types::uint8_4p
        {
            fst: &mut b03,
            snd:
            crate::hacl::sha2_types::uint8_3p
            {
                fst: &mut b13,
                snd: crate::hacl::sha2_types::uint8_2p { fst: &mut b23, snd: &mut b33 }
            }
        };
    let b34: &mut [u8] = b.snd.snd.snd;
    let b24: &mut [u8] = b.snd.snd.fst;
    let b14: &mut [u8] = b.snd.fst;
    let b04: &mut [u8] = b.fst;
    b04[167usize] = 0x80u8;
    b14[167usize] = 0x80u8;
    b24[167usize] = 0x80u8;
    b34[167usize] = 0x80u8;
    absorb_inner_256(168u32, b, state)
}

pub fn shake128_squeeze_nblocks(
    state: &mut [crate::lib::intvector_intrinsics::vec256],
    output0: &mut [u8],
    output1: &mut [u8],
    output2: &mut [u8],
    output3: &mut [u8],
    outputByteLen: u32
) ->
    ()
{
    for i in 0u32..outputByteLen.wrapping_div(168u32)
    {
        let mut hbuf: [u8; 1024] = [0u8; 1024usize];
        let mut ws: [crate::lib::intvector_intrinsics::vec256; 32] =
            [crate::lib::intvector_intrinsics::vec256_zero; 32usize];
        ((&mut ws)[0usize..25usize]).copy_from_slice(&state[0usize..25usize]);
        let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
        let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
        let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
        let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
        let v0·: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
        let v1·: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
        let v2·: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
        let v3·: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
        let v0··: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
        let v1··: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
        let v2··: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
        let v3··: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
        let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
        let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
        let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
        let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
        let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
        let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
        let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
        let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
        let v0·0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
        let v1·0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
        let v2·0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
        let v3·0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
        let v0··0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
        let v1··0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
        let v2··0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
        let v3··0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
        let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
        let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
        let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
        let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
        let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
        let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
        let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
        let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
        let v0·1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
        let v1·1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
        let v2·1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
        let v3·1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
        let v0··1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
        let v1··1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
        let v2··1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
        let v3··1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
        let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
        let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
        let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
        let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
        let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
        let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
        let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
        let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
        let v0·2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
        let v1·2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
        let v2·2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
        let v3·2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
        let v0··2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
        let v1··2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
        let v2··2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
        let v3··2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
        let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
        let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
        let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
        let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
        let v03: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[16usize];
        let v13: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[17usize];
        let v23: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[18usize];
        let v33: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[19usize];
        let v0·3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v03, v13);
        let v1·3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v03, v13);
        let v2·3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v23, v33);
        let v3·3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v23, v33);
        let v0··3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·3, v2·3);
        let v1··3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·3, v2·3);
        let v2··3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·3, v3·3);
        let v3··3: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·3, v3·3);
        let ws16: crate::lib::intvector_intrinsics::vec256 = v0··3;
        let ws17: crate::lib::intvector_intrinsics::vec256 = v2··3;
        let ws18: crate::lib::intvector_intrinsics::vec256 = v1··3;
        let ws19: crate::lib::intvector_intrinsics::vec256 = v3··3;
        let v04: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[20usize];
        let v14: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[21usize];
        let v24: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[22usize];
        let v34: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[23usize];
        let v0·4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v04, v14);
        let v1·4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v04, v14);
        let v2·4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v24, v34);
        let v3·4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v24, v34);
        let v0··4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·4, v2·4);
        let v1··4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·4, v2·4);
        let v2··4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·4, v3·4);
        let v3··4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·4, v3·4);
        let ws20: crate::lib::intvector_intrinsics::vec256 = v0··4;
        let ws21: crate::lib::intvector_intrinsics::vec256 = v2··4;
        let ws22: crate::lib::intvector_intrinsics::vec256 = v1··4;
        let ws23: crate::lib::intvector_intrinsics::vec256 = v3··4;
        let v05: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[24usize];
        let v15: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[25usize];
        let v25: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[26usize];
        let v35: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[27usize];
        let v0·5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v05, v15);
        let v1·5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v05, v15);
        let v2·5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v25, v35);
        let v3·5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v25, v35);
        let v0··5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·5, v2·5);
        let v1··5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·5, v2·5);
        let v2··5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·5, v3·5);
        let v3··5: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·5, v3·5);
        let ws24: crate::lib::intvector_intrinsics::vec256 = v0··5;
        let ws25: crate::lib::intvector_intrinsics::vec256 = v2··5;
        let ws26: crate::lib::intvector_intrinsics::vec256 = v1··5;
        let ws27: crate::lib::intvector_intrinsics::vec256 = v3··5;
        let v06: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[28usize];
        let v16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[29usize];
        let v26: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[30usize];
        let v36: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[31usize];
        let v0·6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v06, v16);
        let v1·6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v06, v16);
        let v2·6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v26, v36);
        let v3·6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v26, v36);
        let v0··6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·6, v2·6);
        let v1··6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·6, v2·6);
        let v2··6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·6, v3·6);
        let v3··6: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·6, v3·6);
        let ws28: crate::lib::intvector_intrinsics::vec256 = v0··6;
        let ws29: crate::lib::intvector_intrinsics::vec256 = v2··6;
        let ws30: crate::lib::intvector_intrinsics::vec256 = v1··6;
        let ws31: crate::lib::intvector_intrinsics::vec256 = v3··6;
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
            crate::lib::intvector_intrinsics::vec256_store64_le(
                &mut (&mut hbuf)[i0.wrapping_mul(32u32) as usize..],
                (&mut ws)[i0 as usize]
            )
        );
        let b0: &mut [u8] = output0;
        let b1: &mut [u8] = output1;
        let b2: &mut [u8] = output2;
        let b3: &mut [u8] = output3;
        (b0[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&mut (&mut hbuf)[0usize..])[0usize..168usize]
        );
        (b1[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&mut (&mut hbuf)[256usize..])[0usize..168usize]
        );
        (b2[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&mut (&mut hbuf)[512usize..])[0usize..168usize]
        );
        (b3[i.wrapping_mul(168u32) as usize..i.wrapping_mul(168u32) as usize + 168usize]).copy_from_slice(
            &(&mut (&mut hbuf)[768usize..])[0usize..168usize]
        );
        krml::unroll_for!(
            24,
            "i0",
            0u32,
            1u32,
            {
                let mut _C: [crate::lib::intvector_intrinsics::vec256; 5] =
                    [crate::lib::intvector_intrinsics::vec256_zero; 5usize];
                krml::unroll_for!(
                    5,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let uu____0: crate::lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(0u32) as usize];
                        let uu____1: crate::lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(5u32) as usize];
                        let uu____2: crate::lib::intvector_intrinsics::vec256 =
                            state[i1.wrapping_add(10u32) as usize];
                        (&mut _C)[i1 as usize] =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____0,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    uu____1,
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        uu____2,
                                        crate::lib::intvector_intrinsics::vec256_xor(
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
                        let uu____3: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(4u32).wrapping_rem(5u32) as usize];
                        let uu____4: crate::lib::intvector_intrinsics::vec256 =
                            (&mut _C)[i1.wrapping_add(1u32).wrapping_rem(5u32) as usize];
                        let _D: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____3,
                                crate::lib::intvector_intrinsics::vec256_or(
                                    crate::lib::intvector_intrinsics::vec256_shift_left64(
                                        uu____4,
                                        1u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    state[i1.wrapping_add(5u32.wrapping_mul(i2)) as usize],
                                    _D
                                )
                        )
                    }
                );
                let x: crate::lib::intvector_intrinsics::vec256 = state[1usize];
                let mut current: [crate::lib::intvector_intrinsics::vec256; 1] = [x; 1usize];
                krml::unroll_for!(
                    24,
                    "i1",
                    0u32,
                    1u32,
                    {
                        let _Y: u32 = (&crate::hacl::hash_sha3::keccak_piln)[i1 as usize];
                        let r: u32 = (&crate::hacl::hash_sha3::keccak_rotc)[i1 as usize];
                        let temp: crate::lib::intvector_intrinsics::vec256 = state[_Y as usize];
                        let uu____5: crate::lib::intvector_intrinsics::vec256 =
                            (&mut current)[0usize];
                        state[_Y as usize] =
                            crate::lib::intvector_intrinsics::vec256_or(
                                crate::lib::intvector_intrinsics::vec256_shift_left64(uu____5, r),
                                crate::lib::intvector_intrinsics::vec256_shift_right64(
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
                        let uu____6: crate::lib::intvector_intrinsics::vec256 =
                            state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____7: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v07: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____6,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____7,
                                    state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____8: crate::lib::intvector_intrinsics::vec256 =
                            state[1u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____9: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v17: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____8,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____9,
                                    state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____10: crate::lib::intvector_intrinsics::vec256 =
                            state[2u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____11: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v27: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____10,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____11,
                                    state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____12: crate::lib::intvector_intrinsics::vec256 =
                            state[3u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____13: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v37: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____12,
                                crate::lib::intvector_intrinsics::vec256_and(
                                    uu____13,
                                    state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                                )
                            );
                        let uu____14: crate::lib::intvector_intrinsics::vec256 =
                            state[4u32.wrapping_add(5u32.wrapping_mul(i1)) as usize];
                        let uu____15: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_lognot(
                                state[0u32.wrapping_add(5u32.wrapping_mul(i1)) as usize]
                            );
                        let v4: crate::lib::intvector_intrinsics::vec256 =
                            crate::lib::intvector_intrinsics::vec256_xor(
                                uu____14,
                                crate::lib::intvector_intrinsics::vec256_and(
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
                let c: u64 = (&crate::hacl::hash_sha3::keccak_rndc)[i0 as usize];
                let uu____16: crate::lib::intvector_intrinsics::vec256 = state[0usize];
                state[0usize] =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        uu____16,
                        crate::lib::intvector_intrinsics::vec256_load64(c)
                    )
            }
        )
    }
}
