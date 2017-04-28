module Spec.SHA2.Word

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open Spec.SHA2.Specialization

module U32 = FStar.UInt32
module Word = FStar.UInt64



//
// SHA-2 Large (384 & 512)
//

(* Define algorithm parameters *)
let size_block_w = 16
let size_hash = 8 * size_hash_w
let size_block = 8 * size_block_w
let size_k_w = 80
let size_len_8 = 16
let size_len_ul_8 = 16ul
let max_input_len_8 = pow2 125

type bytes = m:seq UInt8.t
type word = Word.t
type hash_w = m:seq word {length m = size_hash_w}
type block_w = m:seq word {length m = size_block_w}
type blocks_w = m:seq block_w
type counter = UInt.uint_t 32

(* Define word based operators *)
let words_to_be = Spec.Lib.uint64s_to_be
let words_from_be = Spec.Lib.uint64s_from_be
let word_logxor = Word.logxor
let word_logand = Word.logand
let word_logor = Word.logor
let word_lognot = Word.lognot
let word_shift_right = Word.shift_right
let word_add_mod = Word.add_mod

let rotate_right (a:word) (s:UInt32.t{v s < 64}) : Tot word =
  Word.((a >>^ s) |^ (a <<^ (U32.sub 64ul s)))

let constants_Sigma0 = Seq.seq_of_list [28ul; 34ul; 39ul]
let constants_Sigma1 = Seq.seq_of_list [14ul; 18ul; 41ul]
let constants_sigma0 = Seq.seq_of_list [ 1ul;  8ul;  7ul]
let constants_sigma1 = Seq.seq_of_list [19ul; 61ul;  6ul]

let k = [
  0x428a2f98d728ae22uL; 0x7137449123ef65cduL; 0xb5c0fbcfec4d3b2fuL; 0xe9b5dba58189dbbcuL;
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
]
