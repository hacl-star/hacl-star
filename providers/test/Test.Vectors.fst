module Test.Vectors

open Test.Lowstarize
open EverCrypt.Hash
open Spec.Hash.Definitions

/// Hash algorithms

type hash_alg = EverCrypt.Hash.alg

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

noeq noextract
type hash_vector = {
  (* The input [input] is repeated [repeat] times. *)
  hash_alg: hash_alg;
  input: string;
  output: hex_encoded;
  repeat: UInt32.t;
}

noextract
let hash_vectors = [{
    hash_alg = MD5;
    input = "";
    output = h"d41d8cd98f00b204e9800998ecf8427e";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "a";
    output = h"0cc175b9c0f1b6a831c399e269772661";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "abc";
    output = h"900150983cd24fb0d6963f7d28e17f72";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "message digest";
    output = h"f96b697d7cb7938d525a2f31aaf161d0";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "abcdefghijklmnopqrstuvwxyz";
    output = h"c3fcd3d76192e4007dfb496cca67e13b";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    output = h"d174ab98d277d9f5a5611c2c9f419d9f";
    repeat = 1ul
  }; {
    hash_alg = MD5;
    input = "12345678901234567890123456789012345678901234567890123456789012345678901234567890";
    output = h"57edf4a22be3c955ac49da2e2107b67a";
    repeat = 1ul
  }; {
    hash_alg = SHA1;
    input = "abc";
    output = h"a9993e364706816aba3e25717850c26c9cd0d89d";
    repeat = 1ul
  }; {
    hash_alg = SHA1;
    input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    output = h"84983e441c3bd26ebaae4aa1f95129e5e54670f1";
    repeat = 1ul
  }; {
    hash_alg = SHA1;
    input = "a";
    output = h"34aa973cd4c4daa4f61eeb2bdbad27316534016f";
    repeat = 1000000ul
  }; {
    hash_alg = SHA1;
    input = "0123456701234567012345670123456701234567012345670123456701234567";
    output = h"dea356a2cddd90c7a7ecedc5ebb563934f460452";
    repeat = 10ul
  }; {
    hash_alg = SHA2_256;
    input = "abc";
    output = h"ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    repeat = 1ul
  }; {
    hash_alg = SHA2_256;
    input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    output = h"248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1";
    repeat = 1ul
  }; {
    hash_alg = SHA2_256;
    input = "a";
    output = h"cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0";
    repeat = 1000000ul
  }; {
    hash_alg = SHA2_256;
    input = "0123456701234567012345670123456701234567012345670123456701234567";
    output = h"594847328451bdfa85056225462cc1d867d877fb388df0ce35f25ab5562bfbb5";
    repeat = 10ul
  }; {
    hash_alg = SHA2_256;
    input = "\x19";
    output = h"68aa2e2ee5dff96e3355e6c7ee373e3d6a4e17f75f9518d843709c0c9bc3e3d4";
    repeat = 1ul
  };(* {
    hash_alg = SHA2_256;
    // 2018.05.26: Don't know how to encode byte literals in strings; this doesn't work
    // as in OCaml
    input = "\xe3\xd7\x25\x70\xdc\xdd\x78\x7c\xe3\x88\x7a\xb2\xcd\x68\x46\x52";
    output = h"175ee69b02ba9b58e2b0a5fd13819cea573f3940a94f825128cf4209beabb4e8";
    repeat = 1ul
  }; *){
    hash_alg = SHA2_384;
    input = "abc";
    output = h"cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7";
    repeat = 1ul
  }; {
    hash_alg = SHA2_384;
    input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    output = h"09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039";
    repeat = 1ul
  }; {
    hash_alg = SHA2_384;
    input = "a";
    output = h"9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985";
    repeat = 1000000ul
  }; {
    hash_alg = SHA2_384;
    input = "0123456701234567012345670123456701234567012345670123456701234567";
    output = h"2fc64a4f500ddb6828f6a3430b8dd72a368eb7f3a8322a70bc84275b9c0b3ab00d27a5cc3c2d224aa6b61a0d79fb4596";
    repeat = 10ul
  }; {
    hash_alg = SHA2_512;
    input = "abc";
    output = h"ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f";
    repeat = 1ul
  }; {
    hash_alg = SHA2_512;
    input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    output = h"8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909";
    repeat = 1ul
  }; {
    hash_alg = SHA2_512;
    input = "a";
    output = h"e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b";
    repeat = 1000000ul
  }; {
    hash_alg = SHA2_512;
    input = "0123456701234567012345670123456701234567012345670123456701234567";
    output = h"89d05ba632c699c31231ded4ffc127d5a894dad412c0e024db872d1abd2ba8141a0f85072a9be1e2aa04cf33c765cb510813a39cd5a84c4acaa64d3f3fb7bae9";
    repeat = 10ul
  }
]

noextract
let hash_vectors_tmp = List.Tot.map (fun h ->
  h.hash_alg, h.input, h.output, h.repeat
) hash_vectors

// 2018.08.06 SZ: I can't verify this in interactive mode but verifies from the command-line
%splice[] (lowstarize_toplevel "hash_vectors_tmp" "hash_vectors_low")

/// HMAC

noeq noextract
type hmac_vector = {
  ha: hash_alg;
  key: hex_encoded;
  data: hex_encoded;
  output: hex_encoded;
}

// selected test vectors from
// https://tools.ietf.org/html/rfc4231#section-4.2
// pls extend me!
noextract
let hmac_vectors = [{
    ha     = SHA2_256;
    key    = h"0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
    data   = h"4869205468657265";
    output = h"b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7";
  }; {
    ha     = SHA2_384;
    key    = h"0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";
    data   = h"4869205468657265";
    output = h"afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6";
  }]

noextract
let hmac_vectors_tmp = List.Tot.map (fun h ->
  h.ha, h.key, h.data, h.output
) hmac_vectors

%splice[] (lowstarize_toplevel "hmac_vectors_tmp" "hmac_vectors_low")



/// HKDF
/// https://tools.ietf.org/html/rfc5869.html
/// pls extend me! We miss SHA2_384 and SHA2_512 tests
///
/// The test is in 2 steps:
/// prk <- extract sal ikm        
/// okm <- expand prk info okmlen 

noeq noextract
type hkdf_vector = {
  ha:   hash_alg;
  ikm:  hex_encoded;  // input key materials
  salt: hex_encoded; // input salt 
  info: hex_encoded; // expansion label
  prk:  hex_encoded;  // extracted pseudo-random key (its length is Spec.Hash.Definitions.hash_len ha)
  okm:  hex_encoded;  // output: expanded key materials (its length is an input)
}

noextract 
let hkdf_vectors = [{
    // Test Case 1
    // Basic test case with SHA-256
    ha   = SHA2_256;
    ikm  = h"0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";// (22 octets)
    salt = h"000102030405060708090a0b0c";// (13 octets)
    info = h"f0f1f2f3f4f5f6f7f8f9";// (10 octets)
    prk  = h"077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5";// (32 octets)
    okm  = h"3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865";// (42 octets)
  }; {
    // Test Case 2
    // Test with SHA-256 and longer inputs/outputs
    ha   = SHA2_256;
    ikm  = h"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f";// (80 octets)
    salt = h"606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf";// (80 octets)
    info = h"b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff";// (80 octets)
    prk  = h"06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244";// (32 octets)
    okm  = h"b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87";// (82 octets)
  }; {
    // Test Case 3
    // Test with SHA-256 and zero-length salt/info
    ha   = SHA2_256;
    ikm  = h"0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b";// (22 octets)
    salt = h"";
    info = h"";
    prk  = h"19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04";// (32 octets)
    okm  = h"8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8";// (42 octets)
  }]

noextract
let hkdf_vectors_tmp = List.Tot.map (fun h ->
  h.ha, h.ikm, h.salt, h.info, h.prk, h.okm
) hkdf_vectors

%splice[] (lowstarize_toplevel "hkdf_vectors_tmp" "hkdf_vectors_low")

//TODO add test_hkdf, test_hkdf_one as for HMAC


/// Cipher block function

type block_cipher =
  | AES128
  | AES256

// Funky field names to avoid collisions...
noeq noextract
type block_cipher_vector = {
  block: block_cipher;
  rkey: hex_encoded;
  plain: hex_encoded;
  enc: hex_encoded;
}

noextract
let block_cipher_vectors = [
  {
    block = AES128;
    rkey = h"2b7e151628aed2a6abf7158809cf4f3c";
    plain = h"6bc1bee22e409f96e93d7e117393172a";
    enc = h"3ad77bb40d7a3660a89ecaf32466ef97"
  }; {
    block = AES128;
    rkey = h"2b7e151628aed2a6abf7158809cf4f3c";
    plain = h"ae2d8a571e03ac9c9eb76fac45af8e51";
    enc = h"f5d3d58503b9699de785895a96fdbaaf"
  }; {
    block = AES128;
    rkey = h"2b7e151628aed2a6abf7158809cf4f3c";
    plain = h"30c81c46a35ce411e5fbc1191a0a52ef";
    enc = h"43b1cd7f598ece23881b00e3ed030688"
  }; {
    block = AES128;
    rkey = h"2b7e151628aed2a6abf7158809cf4f3c";
    plain = h"f69f2445df4f9b17ad2b417be66c3710";
    enc = h"7b0c785e27e8ad3f8223207104725dd4"
  }; {
    block = AES256;
    rkey = h"603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    plain = h"6bc1bee22e409f96e93d7e117393172a";
    enc = h"f3eed1bdb5d2a03c064b5a7e3db181f8"
  }; {
    block = AES256;
    rkey = h"603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    plain = h"ae2d8a571e03ac9c9eb76fac45af8e51";
    enc = h"591ccb10d410ed26dc5ba74a31362870"
  }; {
    block = AES256;
    rkey = h"603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    plain = h"30c81c46a35ce411e5fbc1191a0a52ef";
    enc = h"b6ed21b99ca6f4f9f153e7b1beafed1d"
  }; {
    block = AES256;
    rkey = h"603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4";
    plain = h"f69f2445df4f9b17ad2b417be66c3710";
    enc = h"23304b7a39f9f3ff067d8d8f9e24ecc7"
  }]

noextract
let block_cipher_vectors_tmp = List.Tot.map (fun h ->
  h.block, h.rkey, h.plain, h.enc
) block_cipher_vectors

%splice[] (lowstarize_toplevel "block_cipher_vectors_tmp" "block_cipher_vectors_low")

noeq noextract
type chacha20_vector = {
  c20_key: hex_encoded;
  c20_iv: hex_encoded;
  c20_ctr: UInt32.t;
  c20_plain: hex_encoded;
  c20_cipher: hex_encoded;
}

noextract
let chacha20_vectors = [
  {
    c20_key = h"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    c20_iv = h"000000000000004a00000000";
    c20_ctr = 1ul;
    c20_plain = h"4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e";
    c20_cipher = h"6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d";
  }]

noextract
let chacha20_vectors_tmp = List.Tot.map (fun h ->
  h.c20_key, h.c20_iv, h.c20_ctr, h.c20_plain, h.c20_cipher
) chacha20_vectors

%splice[] (lowstarize_toplevel "chacha20_vectors_tmp" "chacha20_vectors_low")

/// AEAD

type cipher =
  | AES_128_GCM
  | AES_256_GCM
  | CHACHA20_POLY1305

noeq noextract
type aead_vector = {
  cipher: cipher;
  key: hex_encoded;
  iv : hex_encoded;
  aad: hex_encoded;
  tag: hex_encoded;
  plaintext: hex_encoded;
  ciphertext: hex_encoded;
}

noextract
let aead_vectors = [
  { (* rfc7539#page-22 *)
    cipher = CHACHA20_POLY1305;
    key = h"808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f";
    iv  = h"070000004041424344454647";
    aad = h"50515253c0c1c2c3c4c5c6c7";
    tag = h"1ae10b594f09e26a7e902ecbd0600691";
    plaintext  = h"4c616469657320616e642047656e746c656d656e206f662074686520636c617373206f66202739393a204966204920636f756c64206f6666657220796f75206f6e6c79206f6e652074697020666f7220746865206675747572652c2073756e73637265656e20776f756c642062652069742e";
    ciphertext = h"d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116";
  };
  {
    cipher = CHACHA20_POLY1305;
    key = h"1c9240a5eb55d38af333888604f6b5f0473917c1402b80099dca5cbc207075c0";
    iv  = h"000000000102030405060708";
    aad = h"f33388860000000000004e91";
    tag = h"eead9d67890cbb22392336fea1851f38";
    plaintext  = h"496e7465726e65742d4472616674732061726520647261667420646f63756d656e74732076616c696420666f722061206d6178696d756d206f6620736978206d6f6e74687320616e64206d617920626520757064617465642c207265706c616365642c206f72206f62736f6c65746564206279206f7468657220646f63756d656e747320617420616e792074696d652e20497420697320696e617070726f70726961746520746f2075736520496e7465726e65742d447261667473206173207265666572656e6365206d6174657269616c206f7220746f2063697465207468656d206f74686572207468616e206173202fe2809c776f726b20696e2070726f67726573732e2fe2809d";
    ciphertext = h"64a0861575861af460f062c79be643bd5e805cfd345cf389f108670ac76c8cb24c6cfc18755d43eea09ee94e382d26b0bdb7b73c321b0100d4f03b7f355894cf332f830e710b97ce98c8a84abd0b948114ad176e008d33bd60f982b1ff37c8559797a06ef4f0ef61c186324e2b3506383606907b6a7c02b0f9f6157b53c867e4b9166c767b804d46a59b5216cde7a4e99040c5a40433225ee282a1b0a06c523eaf4534d7f83fa1155b0047718cbc546a0d072b04b3564eea1b422273f548271a0bb2316053fa76991955ebd63159434ecebb4e466dae5a1073a6727627097a1049e617d91d361094fa68f0ff77987130305beaba2eda04df997b714d6c6f2c29a6ad5cb4022b02709b";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"58e2fccefa7e3061367f1d57a4e7455a";
    plaintext  = h"";
    ciphertext = h"";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"ab6e47d42cec13bdf53a67b21257bddf";
    plaintext  = h"00000000000000000000000000000000";
    ciphertext = h"0388dace60b6a392f328c2b971b2fe78";
  };
  {
    cipher = AES_128_GCM;
    key = h"feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbaddecaf888";
    aad = h"";
    tag = h"4d5c2af327cd64a62cf35abd2ba6fab4";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = h"42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985";
  };
  {
    cipher = AES_128_GCM;
    key = h"feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbaddecaf888";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"5bc94fbc3221a5db94fae95ae7121a47";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091";
  };
  {
    cipher = AES_128_GCM;
    key = h"feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbad";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"3612d2e79e3b0785561be14aaca2fccb";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"61353b4c2806934a777ff51fa22a4755699b2a714fcdc6f83766e5f97b6c742373806900e49f24b22b097544d4896b424989b5e1ebac0f07c23f4598";
  };
  {
    cipher = AES_128_GCM;
    key = h"feffe9928665731c6d6a8f9467308308";
    iv  = h"9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"619cc5aefffe0bfa462af43c1699d050";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"8ce24998625615b603a033aca13fb894be9112a5c3a211a8ba262a3cca7e2ca701e4a9a4fba43c90ccdcb281d48c7c6fd62875d2aca417034c34aee5";
  };
  {
    cipher = AES_256_GCM;
    key = h"0000000000000000000000000000000000000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"530f8afbc74536b9a963b4f1c4cb738b";
    plaintext  = h"";
    ciphertext = h"";
  };
  {
    cipher = AES_256_GCM;
    key = h"feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbaddecaf888";
    aad = h"";
    tag = h"b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = h"522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = h"feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbaddecaf888";
    aad = h"";
    tag = h"b094dac5d93471bdec1a502270e3cc6c";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255";
    ciphertext = h"522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
  };
  {
    cipher = AES_256_GCM;
    key = h"feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbaddecaf888";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"76fc6ece0f4e1768cddf8853bb2d551b";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662";
  };
  {
    cipher = AES_256_GCM;
    key = h"feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = h"cafebabefacedbad";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"3a337dbf46a792c45e454913fe2ea8f2";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"c3762df1ca787d32ae47c13bf19844cbaf1ae14d0b976afac52ff7d79bba9de0feb582d33934a4f0954cc2363bc73f7862ac430e64abe499f47c9b1f";
  };
  {
    cipher = AES_256_GCM;
    key = h"feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308";
    iv  = h"9313225df88406e555909c5aff5269aa6a7a9538534f7da1e4c303d2a318a728c3c0c95156809539fcf0e2429a6b525416aedbf5a0de6a57a637b39b";
    aad = h"feedfacedeadbeeffeedfacedeadbeefabaddad2";
    tag = h"a44a8266ee1c8eb0c8b5d4cf5ae9f19a";
    plaintext  = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39";
    ciphertext = h"5a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad";
    tag = h"5fea793a2d6f974d37e68e0cb8ff9492";
    plaintext  = h"";
    ciphertext = h"";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"9dd0a376b08e40eb00c35f29f9ea61a4";
    plaintext  = h"000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = h"0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"98885a3a22bd4742fe7b72172193b163";
    plaintext  = h"0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = h"0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d5270291";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"000000000000000000000000";
    aad = h"";
    tag = h"cac45f60e31efd3b5a43b98a22ce1aa1";
    plaintext  = h"0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = h"0388dace60b6a392f328c2b971b2fe78f795aaab494b5923f7fd89ff948bc1e0200211214e7394da2089b6acd093abe0c94da219118e297d7b7ebcbcc9c388f28ade7d85a8ee35616f7124a9d527029195b84d1b96c690ff2f2de30bf2ec89e00253786e126504f0dab90c48a30321de3345e6b0461e7c9e6c6b7afedde83f40";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    aad = h"";
    tag = h"566f8ef683078bfdeeffa869d751a017";
    plaintext  = h"000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = h"56b3373ca9ef6e4a2b64fe1e9a17b61425f10d47a75a5fce13efc6bc784af24f4141bdd48cf7c770887afd573cca5418a9aeffcd7c5ceddfc6a78397b9a85b499da558257267caab2ad0b23ca476a53cb17fb41c4b8b475cb4f3f7165094c229c9e8c4dc0a2a5ff1903e501511221376a1cdb8364c5061a20cae74bc4acd76ceb0abc9fd3217ef9f8c90be402ddf6d8697f4f880dff15bfb7a6b28241ec8fe183c2d59e3f9dfff653c7126f0acb9e64211f42bae12af462b1070bef1ab5e3606";
  };
  {
    cipher = AES_128_GCM;
    key = h"00000000000000000000000000000000";
    iv  = h"ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    aad = h"";
    tag = h"8b307f6b33286d0ab026a9ed3fe1e85f";
    plaintext  = h"000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    ciphertext = h"56b3373ca9ef6e4a2b64fe1e9a17b61425f10d47a75a5fce13efc6bc784af24f4141bdd48cf7c770887afd573cca5418a9aeffcd7c5ceddfc6a78397b9a85b499da558257267caab2ad0b23ca476a53cb17fb41c4b8b475cb4f3f7165094c229c9e8c4dc0a2a5ff1903e501511221376a1cdb8364c5061a20cae74bc4acd76ceb0abc9fd3217ef9f8c90be402ddf6d8697f4f880dff15bfb7a6b28241ec8fe183c2d59e3f9dfff653c7126f0acb9e64211f42bae12af462b1070bef1ab5e3606872ca10dee15b3249b1a1b958f23134c4bccb7d03200bce420a2f8eb66dcf3644d1423c1b5699003c13ecef4bf38a3b60eedc34033bac1902783dc6d89e2e774188a439c7ebcc0672dbda4ddcfb2794613b0be41315ef778708a70ee7d75165c";
  };
  {
    cipher = AES_128_GCM;
    key = h"843ffcf5d2b72694d19ed01d01249412";
    iv  = h"dbcca32ebf9b804617c3aa9e";
    aad = h"00000000000000000000000000000000101112131415161718191a1b1c1d1e1f";
    tag = h"3b629ccfbc1119b7319e1dce2cd6fd6d";
    plaintext  = h"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f";
    ciphertext = h"6268c6fa2a80b2d137467f092f657ac04d89be2beaa623d61b5a868c8f03ff95d3dcee23ad2f1ab3a6c80eaf4b140eb05de3457f0fbc111a6b43d0763aa422a3013cf1dc37fe417d1fbfc449b75d4cc5";
  };
]

noextract
let aead_vectors_tmp = List.Tot.map (fun h ->
  h.cipher, h.key, h.iv, h.aad, h.tag, h.plaintext, h.ciphertext
) aead_vectors

%splice[] (lowstarize_toplevel "aead_vectors_tmp" "aead_vectors_low")
