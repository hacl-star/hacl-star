module Spec.SHA2.Constants

#set-options "--z3rlimit 100"
open Lib.IntTypes
// K shuffling vectors

[@"opaque_to_smt"]
inline_for_extraction
let k224_256_l: List.llist uint32 64 =
  [@inline_let]
  let l =
    [u32 0x428a2f98; u32 0x71374491; u32 0xb5c0fbcf; u32 0xe9b5dba5;
     u32 0x3956c25b; u32 0x59f111f1; u32 0x923f82a4; u32 0xab1c5ed5;
     u32 0xd807aa98; u32 0x12835b01; u32 0x243185be; u32 0x550c7dc3;
     u32 0x72be5d74; u32 0x80deb1fe; u32 0x9bdc06a7; u32 0xc19bf174;
     u32 0xe49b69c1; u32 0xefbe4786; u32 0x0fc19dc6; u32 0x240ca1cc;
     u32 0x2de92c6f; u32 0x4a7484aa; u32 0x5cb0a9dc; u32 0x76f988da;
     u32 0x983e5152; u32 0xa831c66d; u32 0xb00327c8; u32 0xbf597fc7;
     u32 0xc6e00bf3; u32 0xd5a79147; u32 0x06ca6351; u32 0x14292967;
     u32 0x27b70a85; u32 0x2e1b2138; u32 0x4d2c6dfc; u32 0x53380d13;
     u32 0x650a7354; u32 0x766a0abb; u32 0x81c2c92e; u32 0x92722c85;
     u32 0xa2bfe8a1; u32 0xa81a664b; u32 0xc24b8b70; u32 0xc76c51a3;
     u32 0xd192e819; u32 0xd6990624; u32 0xf40e3585; u32 0x106aa070;
     u32 0x19a4c116; u32 0x1e376c08; u32 0x2748774c; u32 0x34b0bcb5;
     u32 0x391c0cb3; u32 0x4ed8aa4a; u32 0x5b9cca4f; u32 0x682e6ff3;
     u32 0x748f82ee; u32 0x78a5636f; u32 0x84c87814; u32 0x8cc70208;
     u32 0x90befffa; u32 0xa4506ceb; u32 0xbef9a3f7; u32 0xc67178f2] in
  assert_norm (List.length l = 64);
  l

let k224_256 = Seq.seq_of_list k224_256_l

[@"opaque_to_smt"]
inline_for_extraction
let k384_512_l: List.llist uint64 80 =
  [@inline_let]
  let l =
    [u64 0x428a2f98d728ae22; u64 0x7137449123ef65cd; u64 0xb5c0fbcfec4d3b2f; u64 0xe9b5dba58189dbbc;
     u64 0x3956c25bf348b538; u64 0x59f111f1b605d019; u64 0x923f82a4af194f9b; u64 0xab1c5ed5da6d8118;
     u64 0xd807aa98a3030242; u64 0x12835b0145706fbe; u64 0x243185be4ee4b28c; u64 0x550c7dc3d5ffb4e2;
     u64 0x72be5d74f27b896f; u64 0x80deb1fe3b1696b1; u64 0x9bdc06a725c71235; u64 0xc19bf174cf692694;
     u64 0xe49b69c19ef14ad2; u64 0xefbe4786384f25e3; u64 0x0fc19dc68b8cd5b5; u64 0x240ca1cc77ac9c65;
     u64 0x2de92c6f592b0275; u64 0x4a7484aa6ea6e483; u64 0x5cb0a9dcbd41fbd4; u64 0x76f988da831153b5;
     u64 0x983e5152ee66dfab; u64 0xa831c66d2db43210; u64 0xb00327c898fb213f; u64 0xbf597fc7beef0ee4;
     u64 0xc6e00bf33da88fc2; u64 0xd5a79147930aa725; u64 0x06ca6351e003826f; u64 0x142929670a0e6e70;
     u64 0x27b70a8546d22ffc; u64 0x2e1b21385c26c926; u64 0x4d2c6dfc5ac42aed; u64 0x53380d139d95b3df;
     u64 0x650a73548baf63de; u64 0x766a0abb3c77b2a8; u64 0x81c2c92e47edaee6; u64 0x92722c851482353b;
     u64 0xa2bfe8a14cf10364; u64 0xa81a664bbc423001; u64 0xc24b8b70d0f89791; u64 0xc76c51a30654be30;
     u64 0xd192e819d6ef5218; u64 0xd69906245565a910; u64 0xf40e35855771202a; u64 0x106aa07032bbd1b8;
     u64 0x19a4c116b8d2d0c8; u64 0x1e376c085141ab53; u64 0x2748774cdf8eeb99; u64 0x34b0bcb5e19b48a8;
     u64 0x391c0cb3c5c95a63; u64 0x4ed8aa4ae3418acb; u64 0x5b9cca4f7763e373; u64 0x682e6ff3d6b2b8a3;
     u64 0x748f82ee5defb2fc; u64 0x78a5636f43172f60; u64 0x84c87814a1f0ab72; u64 0x8cc702081a6439ec;
     u64 0x90befffa23631e28; u64 0xa4506cebde82bde9; u64 0xbef9a3f7b2c67915; u64 0xc67178f2e372532b;
     u64 0xca273eceea26619c; u64 0xd186b8c721c0c207; u64 0xeada7dd6cde0eb1e; u64 0xf57d4f7fee6ed178;
     u64 0x06f067aa72176fba; u64 0x0a637dc5a2c898a6; u64 0x113f9804bef90dae; u64 0x1b710b35131c471b;
     u64 0x28db77f523047d84; u64 0x32caab7b40c72493; u64 0x3c9ebe0a15c9bebc; u64 0x431d67c49c100d4c;
     u64 0x4cc5d4becb3e42b6; u64 0x597f299cfc657e2a; u64 0x5fcb6fab3ad6faec; u64 0x6c44198c4a475817
    ] in
  assert_norm (List.length l = 80);
  l

let k384_512 = Seq.seq_of_list k384_512_l

// H0 vectors, i.e. initial values of the accumulator

[@"opaque_to_smt"]
inline_for_extraction
let h224_l: List.llist uint32 8 =
  [@inline_let]
  let l = [
    u32 0xc1059ed8; u32 0x367cd507; u32 0x3070dd17; u32 0xf70e5939;
    u32 0xffc00b31; u32 0x68581511; u32 0x64f98fa7; u32 0xbefa4fa4
  ] in
  assert_norm (List.length l = 8);
  l

let h224 = Seq.seq_of_list h224_l

[@"opaque_to_smt"]
inline_for_extraction
let h256_l: List.llist uint32 8 =
  [@inline_let]
  let l =
    [u32 0x6a09e667; u32 0xbb67ae85; u32 0x3c6ef372; u32 0xa54ff53a;
     u32 0x510e527f; u32 0x9b05688c; u32 0x1f83d9ab; u32 0x5be0cd19]
  in
  assert_norm (List.length l = 8);
  l

let h256 = Seq.seq_of_list h256_l

[@"opaque_to_smt"]
inline_for_extraction
let h384_l: List.llist uint64 8 =
  [@inline_let]
  let l = [
    u64 0xcbbb9d5dc1059ed8; u64 0x629a292a367cd507; u64 0x9159015a3070dd17; u64 0x152fecd8f70e5939;
    u64 0x67332667ffc00b31; u64 0x8eb44a8768581511; u64 0xdb0c2e0d64f98fa7; u64 0x47b5481dbefa4fa4
  ] in
  assert_norm (List.length l = 8);
  l

let h384 = Seq.seq_of_list h384_l

[@"opaque_to_smt"]
inline_for_extraction
let h512_l: List.llist uint64 8 =
  [@inline_let]
  let l = [
    u64 0x6a09e667f3bcc908; u64 0xbb67ae8584caa73b; u64 0x3c6ef372fe94f82b; u64 0xa54ff53a5f1d36f1;
    u64 0x510e527fade682d1; u64 0x9b05688c2b3e6c1f; u64 0x1f83d9abfb41bd6b; u64 0x5be0cd19137e2179
  ] in
  assert_norm (List.length l = 8);
  l

let h512 = Seq.seq_of_list h512_l
