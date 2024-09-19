#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(const_item_mutation)]

const input1: [u8; 3] = [ 0x61, 0x62, 0x63 ];

const input2: [u8; 0] = [];


const tag1_sha1: [u8; 20] = [
  0xa9, 0x99, 0x3e, 0x36, 0x47, 0x06, 0x81, 0x6a,
  0xba, 0x3e, 0x25, 0x71, 0x78, 0x50, 0xc2, 0x6c,
  0x9c, 0xd0, 0xd8, 0x9d
];

const tag2_sha1: [u8; 20] = [
  0xda, 0x39, 0xa3, 0xee, 0x5e, 0x6b, 0x4b, 0x0d,
  0x32, 0x55, 0xbf, 0xef, 0x95, 0x60, 0x18, 0x90,
  0xaf, 0xd8, 0x07, 0x09
];


#[test]
pub fn test_sha1() {
  let mut tag1 = [0u8; 20];
  let mut state1 = crate::hacl::hash_sha1::malloc();
  crate::hacl::hash_sha1::update0(&mut state1, &mut input1, input1.len() as u32);
  crate::hacl::hash_sha1::digest(&mut state1, &mut tag1);
  assert_eq!(tag1, tag1_sha1);

  let mut tag1 = [0u8; 20];
  crate::hacl::hash_sha1::hash(&mut tag1, &mut input1, input1.len() as u32);

  let mut tag2 = [0u8; 20];
  let mut state2 = crate::hacl::hash_sha1::malloc();
  crate::hacl::hash_sha1::update0(&mut state2, &mut input2, input2.len() as u32);
  crate::hacl::hash_sha1::digest(&mut state2, &mut tag2);
  assert_eq!(tag2, tag2_sha1);

  let mut tag2 = [0u8; 20];
  crate::hacl::hash_sha1::hash(&mut tag2, &mut input2, input2.len() as u32);

}
