module Spec.SHA2

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

module ST = FStar.HyperStack.ST


#set-options "--max_fuel 0 --z3rlimit 25"

val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 61 -> p=2305843009213693952
   | 125 -> p=42535295865117307932921825928971026432
   | _  -> True))
  [SMTPat (pow2 x)]
let pow2_values x =
   match x with
   | 61 -> assert_norm (pow2 61 == 2305843009213693952)
   | 125 -> assert_norm (pow2 125 == 42535295865117307932921825928971026432)
   | _  -> ()


(* List the Hash algorithms *)
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512

(* Defines the size of the word for each algorithm *)
inline_for_extraction
let size_word: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8

(* Number of words for intermediate hash *)
let size_hash_w = 8

(* Number of words for final hash *)
inline_for_extraction
let size_hash_final_w: hash_alg -> Tot nat = function
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 7
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)
let size_hash a = size_word a * size_hash_final_w a

(* Number of words for a block size *)
let size_block_w = 16

(* Define the size block in bytes *)
let size_block a = size_word a * size_block_w

(* Define the length of the constants *)
inline_for_extraction
let size_k_w: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80

(* Define the length of scheduling block *)
let size_ws_w = size_k_w

(* Define the length of the encoded lenght in the padding *)
inline_for_extraction
let size_len_8: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16

inline_for_extraction
let size_len_ul_8: hash_alg -> Tot UInt32.t = function
  | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

(* Define the maximum input length in bytes *)
inline_for_extraction
let max_input8: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> pow2 61
  | SHA2_384 | SHA2_512 -> pow2 125

(* Definition of main types *)
type bytes = m:Seq.seq UInt8.t

inline_for_extraction
let word: hash_alg -> Tot Type0 = function
  | SHA2_224 | SHA2_256 -> UInt32.t
  | SHA2_384 | SHA2_512 -> UInt64.t

inline_for_extraction
let word_n: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 32
  | SHA2_384 | SHA2_512 -> 64

let hash_w   a = m:Seq.seq (word a) {length m = size_hash_w}
let k_w      a = m:Seq.seq (word a) {length m = size_k_w a}
let ws_w     a = m:Seq.seq (word a) {length m = size_ws_w a}
let block_w  a = m:Seq.seq (word a) {length m = size_block_w}
let counter = nat


(* Define word based operators *)
inline_for_extraction
let words_to_be: a:hash_alg -> Tot (len:nat -> s:seq (word a){length s = len} -> Tot (lbytes (size_word a * len))) = function
  | SHA2_224 | SHA2_256 -> Spec.Lib.uint32s_to_be
  | SHA2_384 | SHA2_512 -> Spec.Lib.uint64s_to_be

inline_for_extraction
let words_from_be: a:hash_alg -> Tot (len:nat -> b:lbytes (size_word a * len) -> Tot (s:seq (word a){length s = len})) = function
  | SHA2_224 | SHA2_256 -> Spec.Lib.uint32s_from_be
  | SHA2_384 | SHA2_512 -> Spec.Lib.uint64s_from_be

inline_for_extraction
let word_add_mod: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.add_mod
  | SHA2_384 | SHA2_512 -> UInt64.add_mod

inline_for_extraction
let word_logxor: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.logxor
  | SHA2_384 | SHA2_512 -> UInt64.logxor

inline_for_extraction
let word_logand: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.logand
  | SHA2_384 | SHA2_512 -> UInt64.logand

inline_for_extraction
let word_logor: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.logor
  | SHA2_384 | SHA2_512 -> UInt64.logor

inline_for_extraction
let word_lognot: a:hash_alg -> Tot ((word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.lognot
  | SHA2_384 | SHA2_512 -> UInt64.lognot

inline_for_extraction
let word_shift_right: a:hash_alg -> Tot (word a -> s:UInt32.t -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> UInt32.shift_right
  | SHA2_384 | SHA2_512 -> UInt64.shift_right

let rotate_right32 (x:UInt32.t) (s:UInt32.t{v s < 32}) : Tot UInt32.t =
  ((x >>^ s) |^ (x <<^ (32ul -^ s)))

let rotate_right64 (a:UInt64.t) (s:UInt32.t{UInt32.v s < 64}) : Tot UInt64.t =
  FStar.UInt64.((a >>^ s) |^ (a <<^ (UInt32.sub 64ul s)))

inline_for_extraction
let word_rotate_right: a:hash_alg -> Tot (word a -> s:UInt32.t{UInt32.v s < word_n a} -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> rotate_right32
  | SHA2_384 | SHA2_512 -> rotate_right64


(* Definition of the SHA2 word functions *)
val _Ch: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Ch a x y z = word_logxor a (word_logand a x y) (word_logand a (word_lognot a x) z)

val _Maj: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Maj a x y z = word_logxor a (word_logand a x y) (word_logxor a (word_logand a x z) (word_logand a y z))

val _Sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma0 a x = word_logxor a (word_rotate_right a x 2ul) (word_logxor a (word_rotate_right a x 13ul) (word_rotate_right a x 22ul))

val _Sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma1 a x = word_logxor a (word_rotate_right a x 6ul) (word_logxor a (word_rotate_right a x 11ul) (word_rotate_right a x 25ul))

val _sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma0 a x = word_logxor a (word_rotate_right a x 7ul) (word_logxor a (word_rotate_right a x 18ul) (word_shift_right a x 3ul))

val _sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma1 a x = word_logxor a (word_rotate_right a x 17ul) (word_logxor a (word_rotate_right a x 19ul) (word_shift_right a x 10ul))


(* Definition of the SHA2 constants *)
let k224_256 : m:Seq.seq UInt32.t {length m = size_k_w SHA2_256} =
  Seq.Create.create_64
  0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul
  0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul
  0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul
  0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul
  0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul
  0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul
  0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul
  0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul
  0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul
  0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul
  0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul
  0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul
  0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul
  0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul
  0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul
  0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul

let h224 : m:Seq.seq UInt32.t {length m = size_hash_w} =
  Seq.Create.create_8
  0xc1059ed8ul 0x367cd507ul 0x3070dd17ul 0xf70e5939ul
  0xffc00b31ul 0x68581511ul 0x64f98fa7ul 0xbefa4fa4ul

let h256 : m:Seq.seq UInt32.t {length m = size_hash_w} =
  Seq.Create.create_8
  0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul
  0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul

let k384_512 : m:Seq.seq UInt64.t {length m = size_k_w SHA2_512} =
  Seq.Create.create_80
  0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
  0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
  0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
  0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
  0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
  0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
  0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
  0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
  0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
  0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
  0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
  0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
  0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
  0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
  0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
  0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
  0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
  0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
  0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
  0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL

let h384 : m:Seq.seq UInt64.t {length m = size_hash_w} =
  Seq.Create.create_8
  0xcbbb9d5dc1059ed8uL 0x629a292a367cd507uL 0x9159015a3070dd17uL 0x152fecd8f70e5939uL
  0x67332667ffc00b31uL 0x8eb44a8768581511uL 0xdb0c2e0d64f98fa7uL 0x47b5481dbefa4fa4uL

let h512 : m:Seq.seq UInt64.t {length m = size_hash_w} =
  Seq.Create.create_8
  0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
  0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL


inline_for_extraction
let k0: a:hash_alg -> Tot (m:Seq.seq (word a) {length m = size_k_w a}) = function
  | SHA2_224 -> k224_256
  | SHA2_256 -> k224_256
  | SHA2_384 -> k384_512
  | SHA2_512 -> k384_512

inline_for_extraction
let h0: a:hash_alg -> Tot (m:Seq.seq (word a) {length m = size_hash_w}) = function
  | SHA2_224 -> h224
  | SHA2_256 -> h256
  | SHA2_384 -> h384
  | SHA2_512 -> h512


(* Scheduling function *)
let rec ws (a:hash_alg) (b:block_w a) (t:counter{t < size_k_w a}) : Tot (word a) =
  if t < size_block_w then b.[t]
  else
    let t16 = ws a b (t - 16) in
    let t15 = ws a b (t - 15) in
    let t7  = ws a b (t - 7) in
    let t2  = ws a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (word_add_mod a s1 (word_add_mod a t7 (word_add_mod a s0 t16)))


(* Core shuffling function *)
let shuffle_core (a:hash_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < size_k_w a}) : Tot (hash_w a) =
  (**) assert(7 <= Seq.length hash);
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  (**) assert(Seq.length (k0 a) = size_k_w a);
  let t1 = word_add_mod a h0 (word_add_mod a (_Sigma1 a e0) (word_add_mod a (_Ch a e0 f0 g0) (word_add_mod a (k0 a).[t] (ws a block t)))) in
  let t2 = word_add_mod a (_Sigma0 a a0) (_Maj a a0 b0 c0) in

  (**) assert(t < Seq.length (k0 a));
  Seq.Create.create_8 (word_add_mod a t1 t2) a0 b0 c0 (word_add_mod a d0 t1) e0 f0 g0


(* Full shuffling function *)
let shuffle (a:hash_alg) (hash:hash_w a) (block:block_w a) : Tot (hash_w a) =
  Spec.Loops.repeat_range_spec 0 (size_ws_w a) (shuffle_core a block) hash


(* Compression function *)
let update (a:hash_alg) (hash:hash_w a) (block:bytes{length block = size_block a}) : Tot (hash_w a) =
  let block_w = words_from_be a size_block_w block in
  let hash_1 = shuffle a hash block_w in
  Spec.Lib.map2 (fun x y -> word_add_mod a x y) hash hash_1


(* Compression function for multiple blocks *)
let rec update_multi (a:hash_alg) (hash:hash_w a) (blocks:bytes{length blocks % (size_block a) = 0}) : Tot (hash_w a) (decreases (Seq.length blocks)) =
  if Seq.length blocks = 0 then hash
  else
    let (block,rem) = Seq.split blocks (size_block a) in
    let hash = update a hash block in
    update_multi a hash rem


(* Compute the length for the zeroed part of the padding *)
let pad0_length (a:hash_alg) (len:nat) : Tot (n:nat{(len + 1 + n + (size_len_8 a)) % (size_block a) = 0}) =
  ((size_block a) - (len + (size_len_8 a) + 1)) % (size_block a)


(* Compute the padding *)
let pad (a:hash_alg) (prevlen:nat{prevlen % (size_block a) = 0}) (len:nat{prevlen + len < (max_input8 a)}) : Tot (b:bytes{(length b + len) % (size_block a) = 0}) =
  let tlen = prevlen + len in
  let firstbyte = Seq.create 1 0x80uy in
  let zeros = Seq.create (pad0_length a len) 0uy in
  let encodedlen = Endianness.big_bytes (size_len_ul_8 a) (tlen * 8) in
  firstbyte @| zeros @| encodedlen


(* Compress full blocks, then pad the partial block and compress the last block *)
let update_last (a:hash_alg) (hash:hash_w a) (prevlen:nat{prevlen % (size_block a) = 0}) (input:bytes{(Seq.length input) + prevlen < (max_input8 a)}) : Tot (hash_w a) =
  let blocks = pad a prevlen (Seq.length input) in
  update_multi a hash (input @| blocks)


(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:hash_alg) (hashw:hash_w a) : Tot (hash:bytes{length hash = (size_hash a)}) =
  let hash_final_w = Seq.slice hashw 0 (size_hash_final_w a) in
  words_to_be a (size_hash_final_w a) hash_final_w


(* Hash function using the incremental definition *)
let hash (a:hash_alg) (input:bytes{Seq.length input < (max_input8 a)}) : Tot (hash:bytes{length hash = (size_hash a)}) =
  let n = Seq.length input / (size_block a) in
  let (bs,l) = Seq.split input (n * (size_block a)) in
  let hash = update_multi a (h0 a) bs in
  let hash = update_last a hash (n * (size_block a)) l in
  finish a hash


(* Hash function using the padding function first *)
let hash' (a:hash_alg) (input:bytes{Seq.length input < (max_input8 a)}) : Tot (hash:bytes{length hash = (size_hash a)}) =
  let blocks = pad a 0 (Seq.length input) in
  finish a (update_multi a (h0 a) (input @| blocks))
