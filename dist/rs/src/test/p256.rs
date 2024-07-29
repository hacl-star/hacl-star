#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(const_item_mutation)]

const msg: [u8; 128] = [
  89u8,  5u8,   35u8,  136u8, 119u8,
  199u8, 116u8, 33u8,  247u8, 62u8,
  67u8,  238u8, 61u8,  166u8, 242u8,
  217u8, 226u8, 204u8, 173u8, 95u8,
  201u8, 66u8,  220u8, 236u8, 12u8,
  189u8, 37u8,  72u8,  41u8,  53u8,
  250u8, 175u8, 65u8,  105u8, 131u8,
  254u8, 22u8,  91u8,  26u8,  4u8,
  94u8,  226u8, 188u8, 210u8, 230u8,
  220u8, 163u8, 189u8, 244u8, 108u8,
  67u8,  16u8,  167u8, 70u8,  31u8,
  154u8, 55u8,  150u8, 12u8,  166u8,
  114u8, 211u8, 254u8, 181u8, 71u8,
  62u8,  37u8,  54u8,  5u8,   251u8,
  29u8,  223u8, 210u8, 128u8, 101u8,
  181u8, 60u8,  181u8, 133u8, 138u8,
  138u8, 210u8, 129u8, 117u8, 191u8,
  155u8, 211u8, 134u8, 165u8, 228u8,
  113u8, 234u8, 122u8, 101u8, 193u8,
  124u8, 201u8, 52u8,  169u8, 215u8,
  145u8, 233u8, 20u8,  145u8, 235u8,
  55u8,  84u8,  208u8, 55u8,  153u8,
  121u8, 15u8,  226u8, 211u8, 8u8,
  209u8, 97u8,  70u8,  213u8, 201u8,
  176u8, 208u8, 222u8, 189u8, 151u8,
  215u8, 156u8, 232u8
];

const private_key: [u8; 32] = [
  81u8,  155u8, 66u8,  61u8,  113u8,
  95u8,  139u8, 88u8,  31u8,  79u8,
  168u8, 238u8, 89u8,  244u8, 119u8,
  26u8,  91u8,  68u8,  200u8, 19u8,
  11u8,  78u8,  62u8,  172u8, 202u8,
  84u8,  165u8, 109u8, 218u8, 114u8,
  180u8, 100u8
];

const public_key: [u8; 64] = [
  28u8,  203u8, 233u8, 28u8,  7u8,
  95u8,  199u8, 244u8, 240u8, 51u8,
  191u8, 162u8, 72u8,  219u8, 143u8,
  204u8, 211u8, 86u8,  93u8,  233u8,
  75u8,  191u8, 177u8, 47u8,  60u8,
  89u8,  255u8, 70u8,  194u8, 113u8,
  191u8, 131u8, 206u8, 64u8,  20u8,
  198u8, 136u8, 17u8,  249u8, 162u8,
  26u8,  31u8,  219u8, 44u8,  14u8,
  97u8,  19u8,  224u8, 109u8, 183u8,
  202u8, 147u8, 183u8, 64u8,  78u8,
  120u8, 220u8, 124u8, 205u8, 92u8,
  168u8, 154u8, 76u8,  169u8
];

const nonce: [u8; 32] = [
  148u8, 161u8, 187u8, 177u8, 75u8,
  144u8, 106u8, 97u8,  162u8, 128u8,
  242u8, 69u8,  249u8, 233u8, 60u8,
  127u8, 59u8,  74u8,  98u8,  71u8,
  130u8, 79u8,  93u8,  51u8,  185u8,
  103u8, 7u8,   135u8, 100u8, 42u8,
  104u8, 222u8
];

const sgnt: [u8; 64] = [
  243u8, 172u8, 128u8, 97u8,  181u8,
  20u8,  121u8, 91u8,  136u8, 67u8,
  227u8, 214u8, 98u8,  149u8, 39u8,
  237u8, 42u8,  253u8, 107u8, 31u8,
  106u8, 85u8,  90u8,  122u8, 202u8,
  187u8, 94u8,  111u8, 121u8, 200u8,
  194u8, 172u8, 139u8, 247u8, 120u8,
  25u8,  202u8, 5u8,   166u8, 178u8,
  120u8, 108u8, 118u8, 38u8,  43u8,
  247u8, 55u8,  28u8,  239u8, 151u8,
  178u8, 24u8,  233u8, 111u8, 23u8,
  90u8,  60u8,  205u8, 218u8, 42u8,
  204u8, 5u8,   137u8, 3u8
];

#[test]
pub fn test_p256() { 
  let mut sig = [ 0u8; 64 ];
  let mut pk = [ 0u8; 64 ];

  let valid = crate::hacl::p256::dh_initiator(&mut pk, &mut private_key);
  assert!(valid);
  assert_eq!(pk, public_key);

  let flag = crate::hacl::p256::ecdsa_sign_p256_sha2(&mut sig, 128, &mut msg, &mut private_key, &mut nonce);
  assert!(flag);
  assert_eq!(sig, sgnt);
  
  
  let mut sg = sgnt;
  let mut sp = (&mut sg).split_at_mut(32usize);
  let ver = crate::hacl::p256::ecdsa_verif_p256_sha2(128, &mut msg, &mut public_key, &mut sp.0, &mut sp.1);
  assert!(ver);
}
