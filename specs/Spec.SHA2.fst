module Spec.SHA2

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2.Constants
module S = FStar.Seq
module E = FStar.Kremlin.Endianness

open Spec.Hash.Helpers

(* The core compression, padding and extraction functions for all SHA2
 * algorithms. *)

(* Define the length of the constants. Also the number of scheduling rounds. *)
inline_for_extraction
let size_k_w: sha2_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80

inline_for_extraction
let size_len_ul_8: a:sha2_alg -> Tot (n:U32.t{U32.v n = size_len_8 a}) = function
  | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

inline_for_extraction
let word_n: sha2_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 32
  | SHA2_384 | SHA2_512 -> 64

let v' (#a: sha2_alg) (x:word a) = match a with
  | SHA2_224 | SHA2_256 -> U32.v x
  | SHA2_384 | SHA2_512 -> U64.v x

let k_w      (a: sha2_alg) = m:S.seq (word a) {S.length m = size_k_w a}
let block_w  (a: sha2_alg) = m:S.seq (word a) {S.length m = size_block_w}
let counter = nat

(* Define word based operators *)
let words_to_be: a:sha2_alg -> Tot (s:S.seq (word a) -> Tot (Spec.Lib.lbytes FStar.Mul.(size_word a * S.length s))) = function
  | SHA2_224 | SHA2_256 -> E.be_of_seq_uint32
  | SHA2_384 | SHA2_512 -> E.be_of_seq_uint64

let words_from_be: a:sha2_alg -> Tot (len:nat -> b:Spec.Lib.lbytes FStar.Mul.(size_word a * len) -> Tot (s:S.seq (word a){S.length s = len})) = function
  | SHA2_224 | SHA2_256 -> E.seq_uint32_of_be
  | SHA2_384 | SHA2_512 -> E.seq_uint64_of_be

let word_add_mod: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.add_mod
  | SHA2_384 | SHA2_512 -> U64.add_mod

let word_logxor: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logxor
  | SHA2_384 | SHA2_512 -> U64.logxor

let word_logand: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logand
  | SHA2_384 | SHA2_512 -> U64.logand

let word_logor: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logor
  | SHA2_384 | SHA2_512 -> U64.logor

let word_lognot: a:sha2_alg -> Tot ((word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.lognot
  | SHA2_384 | SHA2_512 -> U64.lognot

let word_shift_right: t:sha2_alg -> Tot (a:word t -> s:U32.t -> Pure (word t)
  (requires (FStar.Mul.(U32.v s < 8 * size_word t)))
  (ensures (fun c -> v' c = (v' a / (pow2 (U32.v s)))))) = function
  | SHA2_224 | SHA2_256 -> U32.shift_right
  | SHA2_384 | SHA2_512 -> U64.shift_right

let rotate_right32 (x:U32.t) (s:U32.t{0 < U32.v s /\ U32.v s < 32}): Tot U32.t =
  U32.((x >>^ s) |^ (x <<^ (32ul -^ s)))

let rotate_right64 (a:U64.t) (s:U32.t{0 < U32.v s /\ U32.v s < 64}): Tot U64.t =
  U64.((a >>^ s) |^ (a <<^ (U32.sub 64ul s)))

let word_rotate_right: a:sha2_alg -> Tot (word a -> s:U32.t{0 < U32.v s /\ U32.v s < word_n a} -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> rotate_right32
  | SHA2_384 | SHA2_512 -> rotate_right64

type ops = {
  c0: U32.t; c1: U32.t; c2: U32.t;
  c3: U32.t; c4: U32.t; c5: U32.t;
  e0: U32.t; e1: U32.t; e2: U32.t;
  e3: U32.t; e4: U32.t; e5: U32.t;
}

(* Definition of constants used in word functions *)
let op224_256: ops = {
  c0 = 2ul; c1 = 13ul; c2 = 22ul;
  c3 = 6ul; c4 = 11ul; c5 = 25ul;
  e0 = 7ul; e1 = 18ul; e2 = 3ul;
  e3 = 17ul; e4 = 19ul; e5 = 10ul
}

let op384_512: ops = {
  c0 = 28ul; c1 = 34ul; c2 = 39ul;
  c3 = 14ul; c4 = 18ul; c5 = 41ul;
  e0 = 1ul ; e1 =  8ul; e2 =  7ul;
  e3 = 19ul; e4 = 61ul; e5 =  6ul
}

let op0: a:sha2_alg -> Tot ops = function
  | SHA2_224 -> op224_256
  | SHA2_256 -> op224_256
  | SHA2_384 -> op384_512
  | SHA2_512 -> op384_512


(* Definition of the SHA2 word functions *)
val _Ch: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Ch a x y z = word_logxor a (word_logand a x y)
                                (word_logand a (word_lognot a x) z)

val _Maj: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Maj a x y z = word_logxor a (word_logand a x y)
                                 (word_logxor a (word_logand a x z)
                                                (word_logand a y z))

val _Sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
let _Sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).c0)
                                (word_logxor a (word_rotate_right a x (op0 a).c1)
                                               (word_rotate_right a x (op0 a).c2))

val _Sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
let _Sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).c3)
                                (word_logxor a (word_rotate_right a x (op0 a).c4)
                                               (word_rotate_right a x (op0 a).c5))

val _sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
let _sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).e0)
                                (word_logxor a (word_rotate_right a x (op0 a).e1)
                                               (word_shift_right a x (op0 a).e2))

val _sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
let _sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).e3)
                                (word_logxor a (word_rotate_right a x (op0 a).e4)
                                               (word_shift_right a x (op0 a).e5))

let h0: a:sha2_alg -> Tot (m:hash_w a) = function
  | SHA2_224 -> C.h224
  | SHA2_256 -> C.h256
  | SHA2_384 -> C.h384
  | SHA2_512 -> C.h512

let k0: a:sha2_alg -> Tot (m:S.seq (word a) {S.length m = size_k_w a}) = function
  | SHA2_224 -> C.k224_256
  | SHA2_256 -> C.k224_256
  | SHA2_384 -> C.k384_512
  | SHA2_512 -> C.k384_512

unfold
let (.[]) = S.index

(* Scheduling function *)
let rec ws (a:sha2_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
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
let shuffle_core (a:sha2_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < size_k_w a}): Tot (hash_w a) =
  (**) assert(7 <= S.length hash);
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  (**) assert(S.length (k0 a) = size_k_w a);
  let t1 = word_add_mod a h0 (word_add_mod a (_Sigma1 a e0) (word_add_mod a (_Ch a e0 f0 g0) (word_add_mod a (k0 a).[t] (ws a block t)))) in
  let t2 = word_add_mod a (_Sigma0 a a0) (_Maj a a0 b0 c0) in

  (**) assert(t < S.length (k0 a));
  let l = [ word_add_mod a t1 t2; a0; b0; c0; word_add_mod a d0 t1; e0; f0; g0 ] in
  assert_norm (List.Tot.length l = 8);
  S.seq_of_list l


(* Full shuffling function *)
let shuffle (a:sha2_alg) (hash:hash_w a) (block:block_w a): Tot (hash_w a) =
  Spec.Loops.repeat_range 0 (size_k_w a) (shuffle_core a block) hash

let init = h0

(* Compression function *)
let update (a:sha2_alg) (hash:hash_w a) (block:bytes{S.length block = size_block a}): Tot (hash_w a) =
  let block_w = words_from_be a size_block_w block in
  let hash_1 = shuffle a hash block_w in
  Spec.Loops.seq_map2 (word_add_mod a) hash hash_1


let max_input_size_len (a: sha2_alg): Lemma
  (ensures FStar.Mul.(max_input8 a * 8 = pow2 (size_len_8 a * 8)))
=
  let open FStar.Mul in
  match a with
  | SHA2_224 | SHA2_256 ->
      assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))
  | SHA2_384 | SHA2_512 ->
      assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))

#set-options "--max_fuel 0 --max_ifuel 0"

(* Compute the padding *)
let pad (a:sha2_alg)
  (total_len:nat{total_len < max_input8 a}):
  Tot (b:bytes{(S.length b + total_len) % size_block a = 0})
=
  let open FStar.Mul in
  let firstbyte = S.create 1 0x80uy in
  let zeros = S.create (pad0_length a total_len) 0uy in
  let total_len_bits = total_len * 8 in
  // Saves the need for high fuel + makes hint replayable.
  max_input_size_len a;
  let encodedlen = E.n_to_be (size_len_ul_8 a) (total_len * 8) in
  S.(firstbyte @| zeros @| encodedlen)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:sha2_alg) (hashw:hash_w a): Tot (hash:bytes{S.length hash = (size_hash a)}) =
  let hash_final_w = S.slice hashw 0 (size_hash_final_w a) in
  words_to_be a hash_final_w
