module Spec.SHA2Again.Constants

// K shuffling vectors

[@"opaque_to_smt"]
inline_for_extraction
let k224_256_l: List.llist UInt32.t 64 =
  [@inline_let]
  let l =
    [0x428a2f98ul; 0x71374491ul; 0xb5c0fbcful; 0xe9b5dba5ul;
     0x3956c25bul; 0x59f111f1ul; 0x923f82a4ul; 0xab1c5ed5ul;
     0xd807aa98ul; 0x12835b01ul; 0x243185beul; 0x550c7dc3ul;
     0x72be5d74ul; 0x80deb1feul; 0x9bdc06a7ul; 0xc19bf174ul;
     0xe49b69c1ul; 0xefbe4786ul; 0x0fc19dc6ul; 0x240ca1ccul;
     0x2de92c6ful; 0x4a7484aaul; 0x5cb0a9dcul; 0x76f988daul;
     0x983e5152ul; 0xa831c66dul; 0xb00327c8ul; 0xbf597fc7ul;
     0xc6e00bf3ul; 0xd5a79147ul; 0x06ca6351ul; 0x14292967ul;
     0x27b70a85ul; 0x2e1b2138ul; 0x4d2c6dfcul; 0x53380d13ul;
     0x650a7354ul; 0x766a0abbul; 0x81c2c92eul; 0x92722c85ul;
     0xa2bfe8a1ul; 0xa81a664bul; 0xc24b8b70ul; 0xc76c51a3ul;
     0xd192e819ul; 0xd6990624ul; 0xf40e3585ul; 0x106aa070ul;
     0x19a4c116ul; 0x1e376c08ul; 0x2748774cul; 0x34b0bcb5ul;
     0x391c0cb3ul; 0x4ed8aa4aul; 0x5b9cca4ful; 0x682e6ff3ul;
     0x748f82eeul; 0x78a5636ful; 0x84c87814ul; 0x8cc70208ul;
     0x90befffaul; 0xa4506cebul; 0xbef9a3f7ul; 0xc67178f2ul] in
  assert_norm (List.length l = 64);
  l

[@"opaque_to_smt"]
let k224_256: Seq.lseq UInt32.t 64 =
  Seq.seq_of_list k224_256_l

[@"opaque_to_smt"]
inline_for_extraction
let k384_512_l: List.llist UInt64.t 80 =
  [@inline_let]
  let l =
    [0x428a2f98d728ae22uL; 0x7137449123ef65cduL; 0xb5c0fbcfec4d3b2fuL; 0xe9b5dba58189dbbcuL;
     0x3956c25bf348b538uL; 0x59f111f1b605d019uL; 0x923f82a4af194f9buL; 0xab1c5ed5da6d8118uL;
     0xd807aa98a3030242uL; 0x12835b0145706fbeuL; 0x243185be4ee4b28cuL; 0x550c7dc3d5ffb4e2uL;
     0x72be5d74f27b896fuL; 0x80deb1fe3b1696b1uL; 0x9bdc06a725c71235uL; 0xc19bf174cf692694uL;
     0xe49b69c19ef14ad2uL; 0xefbe4786384f25e3uL; 0x0fc19dc68b8cd5b5uL; 0x240ca1cc77ac9c65uL;
     0x2de92c6f592b0275uL; 0x4a7484aa6ea6e483uL; 0x5cb0a9dcbd41fbd4uL; 0x76f988da831153b5uL;
     0x983e5152ee66dfabuL; 0xa831c66d2db43210uL; 0xb00327c898fb213fuL; 0xbf597fc7beef0ee4uL;
     0xc6e00bf33da88fc2uL; 0xd5a79147930aa725uL; 0x06ca6351e003826fuL; 0x142929670a0e6e70uL;
     0x27b70a8546d22ffcuL; 0x2e1b21385c26c926uL; 0x4d2c6dfc5ac42aeduL; 0x53380d139d95b3dfuL;
     0x650a73548baf63deuL; 0x766a0abb3c77b2a8uL; 0x81c2c92e47edaee6uL; 0x92722c851482353buL;
     0xa2bfe8a14cf10364uL; 0xa81a664bbc423001uL; 0xc24b8b70d0f89791uL; 0xc76c51a30654be30uL;
     0xd192e819d6ef5218uL; 0xd69906245565a910uL; 0xf40e35855771202auL; 0x106aa07032bbd1b8uL;
     0x19a4c116b8d2d0c8uL; 0x1e376c085141ab53uL; 0x2748774cdf8eeb99uL; 0x34b0bcb5e19b48a8uL;
     0x391c0cb3c5c95a63uL; 0x4ed8aa4ae3418acbuL; 0x5b9cca4f7763e373uL; 0x682e6ff3d6b2b8a3uL;
     0x748f82ee5defb2fcuL; 0x78a5636f43172f60uL; 0x84c87814a1f0ab72uL; 0x8cc702081a6439ecuL;
     0x90befffa23631e28uL; 0xa4506cebde82bde9uL; 0xbef9a3f7b2c67915uL; 0xc67178f2e372532buL;
     0xca273eceea26619cuL; 0xd186b8c721c0c207uL; 0xeada7dd6cde0eb1euL; 0xf57d4f7fee6ed178uL;
     0x06f067aa72176fbauL; 0x0a637dc5a2c898a6uL; 0x113f9804bef90daeuL; 0x1b710b35131c471buL;
     0x28db77f523047d84uL; 0x32caab7b40c72493uL; 0x3c9ebe0a15c9bebcuL; 0x431d67c49c100d4cuL;
     0x4cc5d4becb3e42b6uL; 0x597f299cfc657e2auL; 0x5fcb6fab3ad6faecuL; 0x6c44198c4a475817uL
    ] in
  assert_norm (List.length l = 80);
  l

[@"opaque_to_smt"]
let k384_512: Seq.lseq UInt64.t 80 =
  Seq.seq_of_list k384_512_l

// H0 vectors, i.e. initial values of the accumulator

[@"opaque_to_smt"]
inline_for_extraction
let h224_l: List.llist UInt32.t 8 =
  [@inline_let]
  let l = [
    0xc1059ed8ul; 0x367cd507ul; 0x3070dd17ul; 0xf70e5939ul;
    0xffc00b31ul; 0x68581511ul; 0x64f98fa7ul; 0xbefa4fa4ul
  ] in
  assert_norm (List.length l = 8);
  l

[@"opaque_to_smt"]
let h224: Seq.lseq UInt32.t 8 = Seq.seq_of_list h224_l

[@"opaque_to_smt"]
inline_for_extraction
let h256_l: List.llist UInt32.t 8 =
  [@inline_let]
  let l =
    [0x6a09e667ul; 0xbb67ae85ul; 0x3c6ef372ul; 0xa54ff53aul;
     0x510e527ful; 0x9b05688cul; 0x1f83d9abul; 0x5be0cd19ul]
  in
  assert_norm (List.length l = 8);
  l

[@"opaque_to_smt"]
let h256: Seq.lseq UInt32.t 8 = Seq.seq_of_list h256_l

[@"opaque_to_smt"]
inline_for_extraction
let h384_l: List.llist UInt64.t 8 =
  [@inline_let]
  let l = [
    0xcbbb9d5dc1059ed8uL; 0x629a292a367cd507uL; 0x9159015a3070dd17uL; 0x152fecd8f70e5939uL;
    0x67332667ffc00b31uL; 0x8eb44a8768581511uL; 0xdb0c2e0d64f98fa7uL; 0x47b5481dbefa4fa4uL
  ] in
  assert_norm (List.length l = 8);
  l

[@"opaque_to_smt"]
let h384: Seq.lseq UInt64.t 8 =
  Seq.seq_of_list h384_l

[@"opaque_to_smt"]
inline_for_extraction
let h512_l: List.llist UInt64.t 8 =
  [@inline_let]
  let l = [
    0x6a09e667f3bcc908uL; 0xbb67ae8584caa73buL; 0x3c6ef372fe94f82buL; 0xa54ff53a5f1d36f1uL;
    0x510e527fade682d1uL; 0x9b05688c2b3e6c1fuL; 0x1f83d9abfb41bd6buL; 0x5be0cd19137e2179uL
  ] in
  assert_norm (List.length l = 8);
  l

[@"opaque_to_smt"]
let h512: Seq.lseq UInt64.t 8 =
  Seq.seq_of_list h512_l
