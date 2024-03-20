#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn setupBaseS(
    o_pkE: &mut [u8],
    o_ctx: crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s,
    skE: &mut [u8],
    pkR: &mut [u8],
    infolen: u32,
    info: &mut [u8]
) ->
    u32
{
    let mut o_shared: [u8; 32] = [0u8; 32usize];
    let o_pkE1: (&mut [u8], &mut [u8]) = o_pkE.split_at_mut(1usize);
    let res: bool = crate::hacl::p256::ecp256dh_i(o_pkE1.1, skE);
    let res1: u32 = if res { 0u32 } else { 1u32 };
    let res0: u32 =
        if res1 == 0u32
        {
            o_pkE[0usize] = 4u8;
            ();
            let mut o_dh: [u8; 64] = [0u8; 64usize];
            let mut tmp: [u8; 64] = [0u8; 64usize];
            let res0: bool = crate::hacl::p256::ecp256dh_r(&mut tmp, pkR, skE);
            ((&mut o_dh)[0usize..64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize]);
            ();
            let res2: u32 = if res0 { 0u32 } else { 1u32 };
            if res2 == 0u32
            {
                let mut o_kemcontext: [u8; 130] = [0u8; 130usize];
                ((&mut (&mut o_kemcontext)[0usize..])[0usize..65usize]).copy_from_slice(
                    &o_pkE[0usize..65usize]
                );
                ();
                let o_pkRm: (&mut [u8], &mut [u8]) = (&mut o_kemcontext).split_at_mut(65usize);
                let o_pkR: (&mut [u8], &mut [u8]) = o_pkRm.1.split_at_mut(1usize);
                (o_pkR.1[0usize..64usize]).copy_from_slice(&pkR[0usize..64usize]);
                ();
                o_pkRm.1[0usize] = 4u8;
                ();
                let o_dhm: (&mut [u8], &mut [u8]) = (&mut o_dh).split_at_mut(0usize);
                let mut o_eae_prk: [u8; 32] = [0u8; 32usize];
                let mut suite_id_kem: [u8; 5] = [0u8; 5usize];
                let uu____0: (&mut [u8], &mut [u8]) = (&mut suite_id_kem).split_at_mut(0usize);
                uu____0.1[0usize] = 0x4bu8;
                ();
                uu____0.1[1usize] = 0x45u8;
                ();
                uu____0.1[2usize] = 0x4du8;
                ();
                let uu____1: (&mut [u8], &mut [u8]) = uu____0.1.split_at_mut(3usize);
                uu____1.1[0usize] = 0u8;
                ();
                uu____1.1[1usize] = 16u8;
                ();
                let empty: (&mut [u8], &mut [u8]) = uu____1.0.split_at_mut(0usize);
                let mut label_eae_prk: [u8; 7] =
                    [0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8];
                let len: u32 = 51u32;
                let mut tmp0: Vec<u8> = vec![0u8; len as usize];
                let uu____2: (&mut [u8], &mut [u8]) = (&mut tmp0).split_at_mut(0usize);
                uu____2.1[0usize] = 0x48u8;
                ();
                uu____2.1[1usize] = 0x50u8;
                ();
                uu____2.1[2usize] = 0x4bu8;
                ();
                uu____2.1[3usize] = 0x45u8;
                ();
                uu____2.1[4usize] = 0x2du8;
                ();
                uu____2.1[5usize] = 0x76u8;
                ();
                uu____2.1[6usize] = 0x31u8;
                ();
                ((&mut (&mut tmp0)[7usize..])[0usize..5usize]).copy_from_slice(
                    &(&mut suite_id_kem)[0usize..5usize]
                );
                ();
                ((&mut (&mut tmp0)[12usize..])[0usize..7usize]).copy_from_slice(
                    &(&mut label_eae_prk)[0usize..7usize]
                );
                ();
                ((&mut (&mut tmp0)[19usize..])[0usize..32usize]).copy_from_slice(
                    &o_dhm.1[0usize..32usize]
                );
                ();
                crate::hacl::hkdf::extract_sha2_256(&mut o_eae_prk, empty.1, 0u32, &mut tmp0, len);
                ();
                let mut label_shared_secret: [u8; 13] =
                    [0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8, 0x63u8,
                        0x72u8, 0x65u8, 0x74u8];
                let len0: u32 = 157u32;
                let mut tmp1: Vec<u8> = vec![0u8; len0 as usize];
                crate::lowstar::endianness::store16_be(&mut (&mut tmp1)[0usize..], 32u32 as u16);
                ();
                let uu____3: (&mut [u8], &mut [u8]) = (&mut tmp1).split_at_mut(2usize);
                uu____3.1[0usize] = 0x48u8;
                ();
                uu____3.1[1usize] = 0x50u8;
                ();
                uu____3.1[2usize] = 0x4bu8;
                ();
                uu____3.1[3usize] = 0x45u8;
                ();
                uu____3.1[4usize] = 0x2du8;
                ();
                uu____3.1[5usize] = 0x76u8;
                ();
                uu____3.1[6usize] = 0x31u8;
                ();
                ((&mut (&mut tmp1)[9usize..])[0usize..5usize]).copy_from_slice(
                    &(&mut suite_id_kem)[0usize..5usize]
                );
                ();
                ((&mut (&mut tmp1)[14usize..])[0usize..13usize]).copy_from_slice(
                    &(&mut label_shared_secret)[0usize..13usize]
                );
                ();
                ((&mut (&mut tmp1)[27usize..])[0usize..130usize]).copy_from_slice(
                    &(&mut o_kemcontext)[0usize..130usize]
                );
                ();
                crate::hacl::hkdf::expand_sha2_256(
                    &mut o_shared,
                    &mut o_eae_prk,
                    32u32,
                    &mut tmp1,
                    len0,
                    32u32
                );
                ();
                ();
                0u32
            }
            else
            { 1u32 }
        }
        else
        { 1u32 };
    if res0 == 0u32
    {
        let mut o_context: [u8; 65] = [0u8; 65usize];
        let mut o_secret: [u8; 32] = [0u8; 32usize];
        let mut suite_id: [u8; 10] = [0u8; 10usize];
        let uu____4: (&mut [u8], &mut [u8]) = (&mut suite_id).split_at_mut(0usize);
        uu____4.1[0usize] = 0x48u8;
        uu____4.1[1usize] = 0x50u8;
        uu____4.1[2usize] = 0x4bu8;
        uu____4.1[3usize] = 0x45u8;
        let uu____5: (&mut [u8], &mut [u8]) = uu____4.1.split_at_mut(4usize);
        uu____5.1[0usize] = 0u8;
        uu____5.1[1usize] = 16u8;
        let uu____6: (&mut [u8], &mut [u8]) = uu____5.1.split_at_mut(2usize);
        uu____6.1[0usize] = 0u8;
        uu____6.1[1usize] = 1u8;
        let uu____7: (&mut [u8], &mut [u8]) = uu____6.1.split_at_mut(2usize);
        uu____7.1[0usize] = 0u8;
        uu____7.1[1usize] = 3u8;
        let mut label_psk_id_hash: [u8; 11] =
            [0x70u8, 0x73u8, 0x6bu8, 0x5fu8, 0x69u8, 0x64u8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8];
        let mut o_psk_id_hash: [u8; 32] = [0u8; 32usize];
        let empty: (&mut [u8], &mut [u8]) = uu____5.0.split_at_mut(0usize);
        let len: u32 = 28u32;
        let mut tmp: Vec<u8> = vec![0u8; len as usize];
        let uu____8: (&mut [u8], &mut [u8]) = (&mut tmp).split_at_mut(0usize);
        uu____8.1[0usize] = 0x48u8;
        uu____8.1[1usize] = 0x50u8;
        uu____8.1[2usize] = 0x4bu8;
        uu____8.1[3usize] = 0x45u8;
        uu____8.1[4usize] = 0x2du8;
        uu____8.1[5usize] = 0x76u8;
        uu____8.1[6usize] = 0x31u8;
        ((&mut (&mut tmp)[7usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp)[17usize..])[0usize..11usize]).copy_from_slice(
            &(&mut label_psk_id_hash)[0usize..11usize]
        );
        ((&mut (&mut tmp)[28usize..])[0usize..0usize]).copy_from_slice(&empty.1[0usize..0usize]);
        crate::hacl::hkdf::extract_sha2_256(&mut o_psk_id_hash, empty.1, 0u32, &mut tmp, len);
        let mut label_info_hash: [u8; 9] =
            [0x69u8, 0x6eu8, 0x66u8, 0x6fu8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8];
        let mut o_info_hash: [u8; 32] = [0u8; 32usize];
        let len0: u32 = 26u32.wrapping_add(infolen);
        let mut tmp0: Vec<u8> = vec![0u8; len0 as usize];
        let uu____9: (&mut [u8], &mut [u8]) = (&mut tmp0).split_at_mut(0usize);
        uu____9.1[0usize] = 0x48u8;
        uu____9.1[1usize] = 0x50u8;
        uu____9.1[2usize] = 0x4bu8;
        uu____9.1[3usize] = 0x45u8;
        uu____9.1[4usize] = 0x2du8;
        uu____9.1[5usize] = 0x76u8;
        uu____9.1[6usize] = 0x31u8;
        ((&mut (&mut tmp0)[7usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp0)[17usize..])[0usize..9usize]).copy_from_slice(
            &(&mut label_info_hash)[0usize..9usize]
        );
        ((&mut (&mut tmp0)[26usize..])[0usize..infolen as usize]).copy_from_slice(
            &info[0usize..infolen as usize]
        );
        crate::hacl::hkdf::extract_sha2_256(&mut o_info_hash, empty.1, 0u32, &mut tmp0, len0);
        (&mut (&mut o_context)[0usize..])[0usize] = 0u8;
        ((&mut (&mut o_context)[1usize..])[0usize..32usize]).copy_from_slice(
            &(&mut o_psk_id_hash)[0usize..32usize]
        );
        ((&mut (&mut o_context)[33usize..])[0usize..32usize]).copy_from_slice(
            &(&mut o_info_hash)[0usize..32usize]
        );
        let mut label_secret: [u8; 6] = [0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8];
        let len1: u32 = 23u32;
        let mut tmp1: Vec<u8> = vec![0u8; len1 as usize];
        let uu____10: (&mut [u8], &mut [u8]) = (&mut tmp1).split_at_mut(0usize);
        uu____10.1[0usize] = 0x48u8;
        uu____10.1[1usize] = 0x50u8;
        uu____10.1[2usize] = 0x4bu8;
        uu____10.1[3usize] = 0x45u8;
        uu____10.1[4usize] = 0x2du8;
        uu____10.1[5usize] = 0x76u8;
        uu____10.1[6usize] = 0x31u8;
        ((&mut (&mut tmp1)[7usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp1)[17usize..])[0usize..6usize]).copy_from_slice(
            &(&mut label_secret)[0usize..6usize]
        );
        ((&mut (&mut tmp1)[23usize..])[0usize..0usize]).copy_from_slice(&empty.1[0usize..0usize]);
        crate::hacl::hkdf::extract_sha2_256(&mut o_secret, &mut o_shared, 32u32, &mut tmp1, len1);
        let mut label_exp: [u8; 3] = [0x65u8, 0x78u8, 0x70u8];
        let len2: u32 = 87u32;
        let mut tmp2: Vec<u8> = vec![0u8; len2 as usize];
        crate::lowstar::endianness::store16_be(&mut (&mut tmp2)[0usize..], 32u32 as u16);
        let uu____11: (&mut [u8], &mut [u8]) = (&mut tmp2).split_at_mut(2usize);
        uu____11.1[0usize] = 0x48u8;
        uu____11.1[1usize] = 0x50u8;
        uu____11.1[2usize] = 0x4bu8;
        uu____11.1[3usize] = 0x45u8;
        uu____11.1[4usize] = 0x2du8;
        uu____11.1[5usize] = 0x76u8;
        uu____11.1[6usize] = 0x31u8;
        ((&mut (&mut tmp2)[9usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp2)[19usize..])[0usize..3usize]).copy_from_slice(
            &(&mut label_exp)[0usize..3usize]
        );
        ((&mut (&mut tmp2)[22usize..])[0usize..65usize]).copy_from_slice(
            &(&mut o_context)[0usize..65usize]
        );
        crate::hacl::hkdf::expand_sha2_256(
            o_ctx.ctx_exporter,
            &mut o_secret,
            32u32,
            &mut tmp2,
            len2,
            32u32
        );
        let mut label_key: [u8; 3] = [0x6bu8, 0x65u8, 0x79u8];
        let len3: u32 = 87u32;
        let mut tmp3: Vec<u8> = vec![0u8; len3 as usize];
        crate::lowstar::endianness::store16_be(&mut (&mut tmp3)[0usize..], 32u32 as u16);
        let uu____12: (&mut [u8], &mut [u8]) = (&mut tmp3).split_at_mut(2usize);
        uu____12.1[0usize] = 0x48u8;
        uu____12.1[1usize] = 0x50u8;
        uu____12.1[2usize] = 0x4bu8;
        uu____12.1[3usize] = 0x45u8;
        uu____12.1[4usize] = 0x2du8;
        uu____12.1[5usize] = 0x76u8;
        uu____12.1[6usize] = 0x31u8;
        ((&mut (&mut tmp3)[9usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp3)[19usize..])[0usize..3usize]).copy_from_slice(
            &(&mut label_key)[0usize..3usize]
        );
        ((&mut (&mut tmp3)[22usize..])[0usize..65usize]).copy_from_slice(
            &(&mut o_context)[0usize..65usize]
        );
        crate::hacl::hkdf::expand_sha2_256(
            o_ctx.ctx_key,
            &mut o_secret,
            32u32,
            &mut tmp3,
            len3,
            32u32
        );
        let mut label_base_nonce: [u8; 10] =
            [0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8];
        let len4: u32 = 94u32;
        let mut tmp4: Vec<u8> = vec![0u8; len4 as usize];
        crate::lowstar::endianness::store16_be(&mut (&mut tmp4)[0usize..], 12u32 as u16);
        let uu____13: (&mut [u8], &mut [u8]) = (&mut tmp4).split_at_mut(2usize);
        uu____13.1[0usize] = 0x48u8;
        uu____13.1[1usize] = 0x50u8;
        uu____13.1[2usize] = 0x4bu8;
        uu____13.1[3usize] = 0x45u8;
        uu____13.1[4usize] = 0x2du8;
        uu____13.1[5usize] = 0x76u8;
        uu____13.1[6usize] = 0x31u8;
        ((&mut (&mut tmp4)[9usize..])[0usize..10usize]).copy_from_slice(
            &(&mut suite_id)[0usize..10usize]
        );
        ((&mut (&mut tmp4)[19usize..])[0usize..10usize]).copy_from_slice(
            &(&mut label_base_nonce)[0usize..10usize]
        );
        ((&mut (&mut tmp4)[29usize..])[0usize..65usize]).copy_from_slice(
            &(&mut o_context)[0usize..65usize]
        );
        crate::hacl::hkdf::expand_sha2_256(
            o_ctx.ctx_nonce,
            &mut o_secret,
            32u32,
            &mut tmp4,
            len4,
            12u32
        );
        o_ctx.ctx_seq[0usize] = 0u64;
        res0
    }
    else
    { res0 }
}

pub fn setupBaseR(
    o_ctx: crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s,
    enc: &mut [u8],
    skR: &mut [u8],
    infolen: u32,
    info: &mut [u8]
) ->
    u32
{
    let mut pkR: [u8; 64] = [0u8; 64usize];
    let res: bool = crate::hacl::p256::ecp256dh_i(&mut pkR, skR);
    let res1: u32 = if res { 0u32 } else { 1u32 };
    if res1 == 0u32
    {
        let mut shared: [u8; 32] = [0u8; 32usize];
        let pkE: (&mut [u8], &mut [u8]) = enc.split_at_mut(1usize);
        let mut dh: [u8; 64] = [0u8; 64usize];
        let mut tmp: [u8; 64] = [0u8; 64usize];
        let res0: bool = crate::hacl::p256::ecp256dh_r(&mut tmp, pkE.1, skR);
        ((&mut dh)[0usize..64usize]).copy_from_slice(&(&mut tmp)[0usize..64usize]);
        let res11: u32 = if res0 { 0u32 } else { 1u32 };
        let res2: u32 =
            if res11 == 0u32
            {
                let mut kemcontext: [u8; 130] = [0u8; 130usize];
                let pkRm: (&mut [u8], &mut [u8]) = (&mut kemcontext).split_at_mut(65usize);
                let pkR1: (&mut [u8], &mut [u8]) = pkRm.1.split_at_mut(1usize);
                let res2: bool = crate::hacl::p256::ecp256dh_i(pkR1.1, skR);
                let res20: u32 = if res2 { 0u32 } else { 1u32 };
                if res20 == 0u32
                {
                    ((&mut (&mut kemcontext)[0usize..])[0usize..65usize]).copy_from_slice(
                        &enc[0usize..65usize]
                    );
                    ();
                    pkRm.1[0usize] = 4u8;
                    ();
                    let dhm: (&mut [u8], &mut [u8]) = (&mut dh).split_at_mut(0usize);
                    let mut o_eae_prk: [u8; 32] = [0u8; 32usize];
                    let mut suite_id_kem: [u8; 5] = [0u8; 5usize];
                    let uu____0: (&mut [u8], &mut [u8]) = (&mut suite_id_kem).split_at_mut(0usize);
                    uu____0.1[0usize] = 0x4bu8;
                    ();
                    uu____0.1[1usize] = 0x45u8;
                    ();
                    uu____0.1[2usize] = 0x4du8;
                    ();
                    let uu____1: (&mut [u8], &mut [u8]) = uu____0.1.split_at_mut(3usize);
                    uu____1.1[0usize] = 0u8;
                    ();
                    uu____1.1[1usize] = 16u8;
                    ();
                    let empty: (&mut [u8], &mut [u8]) = uu____1.0.split_at_mut(0usize);
                    let mut label_eae_prk: [u8; 7] =
                        [0x65u8, 0x61u8, 0x65u8, 0x5fu8, 0x70u8, 0x72u8, 0x6bu8];
                    let len: u32 = 51u32;
                    let mut tmp0: Vec<u8> = vec![0u8; len as usize];
                    let uu____2: (&mut [u8], &mut [u8]) = (&mut tmp0).split_at_mut(0usize);
                    uu____2.1[0usize] = 0x48u8;
                    ();
                    uu____2.1[1usize] = 0x50u8;
                    ();
                    uu____2.1[2usize] = 0x4bu8;
                    ();
                    uu____2.1[3usize] = 0x45u8;
                    ();
                    uu____2.1[4usize] = 0x2du8;
                    ();
                    uu____2.1[5usize] = 0x76u8;
                    ();
                    uu____2.1[6usize] = 0x31u8;
                    ();
                    ((&mut (&mut tmp0)[7usize..])[0usize..5usize]).copy_from_slice(
                        &(&mut suite_id_kem)[0usize..5usize]
                    );
                    ();
                    ((&mut (&mut tmp0)[12usize..])[0usize..7usize]).copy_from_slice(
                        &(&mut label_eae_prk)[0usize..7usize]
                    );
                    ();
                    ((&mut (&mut tmp0)[19usize..])[0usize..32usize]).copy_from_slice(
                        &dhm.1[0usize..32usize]
                    );
                    ();
                    crate::hacl::hkdf::extract_sha2_256(
                        &mut o_eae_prk,
                        empty.1,
                        0u32,
                        &mut tmp0,
                        len
                    );
                    ();
                    let mut label_shared_secret: [u8; 13] =
                        [0x73u8, 0x68u8, 0x61u8, 0x72u8, 0x65u8, 0x64u8, 0x5fu8, 0x73u8, 0x65u8,
                            0x63u8, 0x72u8, 0x65u8, 0x74u8];
                    let len0: u32 = 157u32;
                    let mut tmp1: Vec<u8> = vec![0u8; len0 as usize];
                    crate::lowstar::endianness::store16_be(&mut (&mut tmp1)[0usize..], 32u32 as u16);
                    ();
                    let uu____3: (&mut [u8], &mut [u8]) = (&mut tmp1).split_at_mut(2usize);
                    uu____3.1[0usize] = 0x48u8;
                    ();
                    uu____3.1[1usize] = 0x50u8;
                    ();
                    uu____3.1[2usize] = 0x4bu8;
                    ();
                    uu____3.1[3usize] = 0x45u8;
                    ();
                    uu____3.1[4usize] = 0x2du8;
                    ();
                    uu____3.1[5usize] = 0x76u8;
                    ();
                    uu____3.1[6usize] = 0x31u8;
                    ();
                    ((&mut (&mut tmp1)[9usize..])[0usize..5usize]).copy_from_slice(
                        &(&mut suite_id_kem)[0usize..5usize]
                    );
                    ();
                    ((&mut (&mut tmp1)[14usize..])[0usize..13usize]).copy_from_slice(
                        &(&mut label_shared_secret)[0usize..13usize]
                    );
                    ();
                    ((&mut (&mut tmp1)[27usize..])[0usize..130usize]).copy_from_slice(
                        &(&mut kemcontext)[0usize..130usize]
                    );
                    ();
                    crate::hacl::hkdf::expand_sha2_256(
                        &mut shared,
                        &mut o_eae_prk,
                        32u32,
                        &mut tmp1,
                        len0,
                        32u32
                    );
                    ();
                    ();
                    0u32
                }
                else
                { 1u32 }
            }
            else
            { 1u32 };
        if res2 == 0u32
        {
            let mut o_context: [u8; 65] = [0u8; 65usize];
            let mut o_secret: [u8; 32] = [0u8; 32usize];
            let mut suite_id: [u8; 10] = [0u8; 10usize];
            let uu____4: (&mut [u8], &mut [u8]) = (&mut suite_id).split_at_mut(0usize);
            uu____4.1[0usize] = 0x48u8;
            uu____4.1[1usize] = 0x50u8;
            uu____4.1[2usize] = 0x4bu8;
            uu____4.1[3usize] = 0x45u8;
            let uu____5: (&mut [u8], &mut [u8]) = uu____4.1.split_at_mut(4usize);
            uu____5.1[0usize] = 0u8;
            uu____5.1[1usize] = 16u8;
            let uu____6: (&mut [u8], &mut [u8]) = uu____5.1.split_at_mut(2usize);
            uu____6.1[0usize] = 0u8;
            uu____6.1[1usize] = 1u8;
            let uu____7: (&mut [u8], &mut [u8]) = uu____6.1.split_at_mut(2usize);
            uu____7.1[0usize] = 0u8;
            uu____7.1[1usize] = 3u8;
            let mut label_psk_id_hash: [u8; 11] =
                [0x70u8, 0x73u8, 0x6bu8, 0x5fu8, 0x69u8, 0x64u8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8,
                    0x68u8];
            let mut o_psk_id_hash: [u8; 32] = [0u8; 32usize];
            let empty: (&mut [u8], &mut [u8]) = uu____5.0.split_at_mut(0usize);
            let len: u32 = 28u32;
            let mut tmp0: Vec<u8> = vec![0u8; len as usize];
            let uu____8: (&mut [u8], &mut [u8]) = (&mut tmp0).split_at_mut(0usize);
            uu____8.1[0usize] = 0x48u8;
            uu____8.1[1usize] = 0x50u8;
            uu____8.1[2usize] = 0x4bu8;
            uu____8.1[3usize] = 0x45u8;
            uu____8.1[4usize] = 0x2du8;
            uu____8.1[5usize] = 0x76u8;
            uu____8.1[6usize] = 0x31u8;
            ((&mut (&mut tmp0)[7usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp0)[17usize..])[0usize..11usize]).copy_from_slice(
                &(&mut label_psk_id_hash)[0usize..11usize]
            );
            ((&mut (&mut tmp0)[28usize..])[0usize..0usize]).copy_from_slice(
                &empty.1[0usize..0usize]
            );
            crate::hacl::hkdf::extract_sha2_256(&mut o_psk_id_hash, empty.1, 0u32, &mut tmp0, len);
            let mut label_info_hash: [u8; 9] =
                [0x69u8, 0x6eu8, 0x66u8, 0x6fu8, 0x5fu8, 0x68u8, 0x61u8, 0x73u8, 0x68u8];
            let mut o_info_hash: [u8; 32] = [0u8; 32usize];
            let len0: u32 = 26u32.wrapping_add(infolen);
            let mut tmp1: Vec<u8> = vec![0u8; len0 as usize];
            let uu____9: (&mut [u8], &mut [u8]) = (&mut tmp1).split_at_mut(0usize);
            uu____9.1[0usize] = 0x48u8;
            uu____9.1[1usize] = 0x50u8;
            uu____9.1[2usize] = 0x4bu8;
            uu____9.1[3usize] = 0x45u8;
            uu____9.1[4usize] = 0x2du8;
            uu____9.1[5usize] = 0x76u8;
            uu____9.1[6usize] = 0x31u8;
            ((&mut (&mut tmp1)[7usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp1)[17usize..])[0usize..9usize]).copy_from_slice(
                &(&mut label_info_hash)[0usize..9usize]
            );
            ((&mut (&mut tmp1)[26usize..])[0usize..infolen as usize]).copy_from_slice(
                &info[0usize..infolen as usize]
            );
            crate::hacl::hkdf::extract_sha2_256(&mut o_info_hash, empty.1, 0u32, &mut tmp1, len0);
            (&mut (&mut o_context)[0usize..])[0usize] = 0u8;
            ((&mut (&mut o_context)[1usize..])[0usize..32usize]).copy_from_slice(
                &(&mut o_psk_id_hash)[0usize..32usize]
            );
            ((&mut (&mut o_context)[33usize..])[0usize..32usize]).copy_from_slice(
                &(&mut o_info_hash)[0usize..32usize]
            );
            let mut label_secret: [u8; 6] = [0x73u8, 0x65u8, 0x63u8, 0x72u8, 0x65u8, 0x74u8];
            let len1: u32 = 23u32;
            let mut tmp2: Vec<u8> = vec![0u8; len1 as usize];
            let uu____10: (&mut [u8], &mut [u8]) = (&mut tmp2).split_at_mut(0usize);
            uu____10.1[0usize] = 0x48u8;
            uu____10.1[1usize] = 0x50u8;
            uu____10.1[2usize] = 0x4bu8;
            uu____10.1[3usize] = 0x45u8;
            uu____10.1[4usize] = 0x2du8;
            uu____10.1[5usize] = 0x76u8;
            uu____10.1[6usize] = 0x31u8;
            ((&mut (&mut tmp2)[7usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp2)[17usize..])[0usize..6usize]).copy_from_slice(
                &(&mut label_secret)[0usize..6usize]
            );
            ((&mut (&mut tmp2)[23usize..])[0usize..0usize]).copy_from_slice(
                &empty.1[0usize..0usize]
            );
            crate::hacl::hkdf::extract_sha2_256(&mut o_secret, &mut shared, 32u32, &mut tmp2, len1);
            let mut label_exp: [u8; 3] = [0x65u8, 0x78u8, 0x70u8];
            let len2: u32 = 87u32;
            let mut tmp3: Vec<u8> = vec![0u8; len2 as usize];
            crate::lowstar::endianness::store16_be(&mut (&mut tmp3)[0usize..], 32u32 as u16);
            let uu____11: (&mut [u8], &mut [u8]) = (&mut tmp3).split_at_mut(2usize);
            uu____11.1[0usize] = 0x48u8;
            uu____11.1[1usize] = 0x50u8;
            uu____11.1[2usize] = 0x4bu8;
            uu____11.1[3usize] = 0x45u8;
            uu____11.1[4usize] = 0x2du8;
            uu____11.1[5usize] = 0x76u8;
            uu____11.1[6usize] = 0x31u8;
            ((&mut (&mut tmp3)[9usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp3)[19usize..])[0usize..3usize]).copy_from_slice(
                &(&mut label_exp)[0usize..3usize]
            );
            ((&mut (&mut tmp3)[22usize..])[0usize..65usize]).copy_from_slice(
                &(&mut o_context)[0usize..65usize]
            );
            crate::hacl::hkdf::expand_sha2_256(
                o_ctx.ctx_exporter,
                &mut o_secret,
                32u32,
                &mut tmp3,
                len2,
                32u32
            );
            let mut label_key: [u8; 3] = [0x6bu8, 0x65u8, 0x79u8];
            let len3: u32 = 87u32;
            let mut tmp4: Vec<u8> = vec![0u8; len3 as usize];
            crate::lowstar::endianness::store16_be(&mut (&mut tmp4)[0usize..], 32u32 as u16);
            let uu____12: (&mut [u8], &mut [u8]) = (&mut tmp4).split_at_mut(2usize);
            uu____12.1[0usize] = 0x48u8;
            uu____12.1[1usize] = 0x50u8;
            uu____12.1[2usize] = 0x4bu8;
            uu____12.1[3usize] = 0x45u8;
            uu____12.1[4usize] = 0x2du8;
            uu____12.1[5usize] = 0x76u8;
            uu____12.1[6usize] = 0x31u8;
            ((&mut (&mut tmp4)[9usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp4)[19usize..])[0usize..3usize]).copy_from_slice(
                &(&mut label_key)[0usize..3usize]
            );
            ((&mut (&mut tmp4)[22usize..])[0usize..65usize]).copy_from_slice(
                &(&mut o_context)[0usize..65usize]
            );
            crate::hacl::hkdf::expand_sha2_256(
                o_ctx.ctx_key,
                &mut o_secret,
                32u32,
                &mut tmp4,
                len3,
                32u32
            );
            let mut label_base_nonce: [u8; 10] =
                [0x62u8, 0x61u8, 0x73u8, 0x65u8, 0x5fu8, 0x6eu8, 0x6fu8, 0x6eu8, 0x63u8, 0x65u8];
            let len4: u32 = 94u32;
            let mut tmp5: Vec<u8> = vec![0u8; len4 as usize];
            crate::lowstar::endianness::store16_be(&mut (&mut tmp5)[0usize..], 12u32 as u16);
            let uu____13: (&mut [u8], &mut [u8]) = (&mut tmp5).split_at_mut(2usize);
            uu____13.1[0usize] = 0x48u8;
            uu____13.1[1usize] = 0x50u8;
            uu____13.1[2usize] = 0x4bu8;
            uu____13.1[3usize] = 0x45u8;
            uu____13.1[4usize] = 0x2du8;
            uu____13.1[5usize] = 0x76u8;
            uu____13.1[6usize] = 0x31u8;
            ((&mut (&mut tmp5)[9usize..])[0usize..10usize]).copy_from_slice(
                &(&mut suite_id)[0usize..10usize]
            );
            ((&mut (&mut tmp5)[19usize..])[0usize..10usize]).copy_from_slice(
                &(&mut label_base_nonce)[0usize..10usize]
            );
            ((&mut (&mut tmp5)[29usize..])[0usize..65usize]).copy_from_slice(
                &(&mut o_context)[0usize..65usize]
            );
            crate::hacl::hkdf::expand_sha2_256(
                o_ctx.ctx_nonce,
                &mut o_secret,
                32u32,
                &mut tmp5,
                len4,
                12u32
            );
            o_ctx.ctx_seq[0usize] = 0u64;
            0u32
        }
        else
        { 1u32 }
    }
    else
    { 1u32 }
}

pub fn sealBase(
    skE: &mut [u8],
    pkR: &mut [u8],
    infolen: u32,
    info: &mut [u8],
    aadlen: u32,
    aad: &mut [u8],
    plainlen: u32,
    plain: &mut [u8],
    o_enc: &mut [u8],
    o_ct: &mut [u8]
) ->
    u32
{
    let mut ctx_key: [u8; 32] = [0u8; 32usize];
    let mut ctx_nonce: [u8; 12] = [0u8; 12usize];
    let mut ctx_seq: [u64; 1] = [0u64; 1usize];
    let mut ctx_exporter: [u8; 32] = [0u8; 32usize];
    let o_ctx: crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s =
        crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s
        {
            ctx_key: &mut ctx_key,
            ctx_nonce: &mut ctx_nonce,
            ctx_seq: &mut ctx_seq,
            ctx_exporter: &mut ctx_exporter
        };
    let res: u32 = setupBaseS(o_enc, o_ctx, skE, pkR, infolen, info);
    if res == 0u32
    {
        let mut nonce: [u8; 12] = [0u8; 12usize];
        let s: u64 = o_ctx.ctx_seq[0usize];
        let mut enc: [u8; 12] = [0u8; 12usize];
        crate::lowstar::endianness::store64_be(&mut (&mut enc)[4usize..], s);
        for i in 0u32..12u32
        {
            let xi: u8 = (&mut enc)[i as usize];
            let yi: u8 = o_ctx.ctx_nonce[i as usize];
            (&mut nonce)[i as usize] = xi ^ yi
        };
        let cipher: (&mut [u8], &mut [u8]) = o_ct.split_at_mut(0usize);
        let tag: (&mut [u8], &mut [u8]) = cipher.1.split_at_mut(plainlen as usize);
        crate::hacl::aead_chacha20poly1305::encrypt(
            tag.0,
            tag.1,
            plain,
            plainlen,
            aad,
            aadlen,
            o_ctx.ctx_key,
            &mut nonce
        );
        let s1: u64 = o_ctx.ctx_seq[0usize];
        let res1: u32 =
            if s1 == 18446744073709551615u64
            { 1u32 }
            else
            {
                let s·: u64 = s1.wrapping_add(1u64);
                o_ctx.ctx_seq[0usize] = s·;
                ();
                0u32
            };
        let res10: u32 = res1;
        res10
    }
    else
    { 1u32 }
}

pub fn openBase(
    pkE: &mut [u8],
    skR: &mut [u8],
    infolen: u32,
    info: &mut [u8],
    aadlen: u32,
    aad: &mut [u8],
    ctlen: u32,
    ct: &mut [u8],
    o_pt: &mut [u8]
) ->
    u32
{
    let mut ctx_key: [u8; 32] = [0u8; 32usize];
    let mut ctx_nonce: [u8; 12] = [0u8; 12usize];
    let mut ctx_seq: [u64; 1] = [0u64; 1usize];
    let mut ctx_exporter: [u8; 32] = [0u8; 32usize];
    let o_ctx: crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s =
        crate::hacl::hpke_interface_hacl_impl_hpke_hacl_meta_hpke::context_s
        {
            ctx_key: &mut ctx_key,
            ctx_nonce: &mut ctx_nonce,
            ctx_seq: &mut ctx_seq,
            ctx_exporter: &mut ctx_exporter
        };
    let res: u32 = setupBaseR(o_ctx, pkE, skR, infolen, info);
    if res == 0u32
    {
        let mut nonce: [u8; 12] = [0u8; 12usize];
        let s: u64 = o_ctx.ctx_seq[0usize];
        let mut enc: [u8; 12] = [0u8; 12usize];
        crate::lowstar::endianness::store64_be(&mut (&mut enc)[4usize..], s);
        for i in 0u32..12u32
        {
            let xi: u8 = (&mut enc)[i as usize];
            let yi: u8 = o_ctx.ctx_nonce[i as usize];
            (&mut nonce)[i as usize] = xi ^ yi
        };
        let cipher: (&mut [u8], &mut [u8]) = ct.split_at_mut(0usize);
        let tag: (&mut [u8], &mut [u8]) = cipher.1.split_at_mut(ctlen.wrapping_sub(16u32) as usize);
        let res1: u32 =
            crate::hacl::aead_chacha20poly1305::decrypt(
                o_pt,
                tag.0,
                ctlen.wrapping_sub(16u32),
                aad,
                aadlen,
                o_ctx.ctx_key,
                &mut nonce,
                tag.1
            );
        if res1 == 0u32
        {
            let s1: u64 = o_ctx.ctx_seq[0usize];
            if s1 == 18446744073709551615u64
            { 1u32 }
            else
            {
                let s·: u64 = s1.wrapping_add(1u64);
                o_ctx.ctx_seq[0usize] = s·;
                0u32
            }
        }
        else
        { 1u32 }
    }
    else
    { 1u32 }
}
