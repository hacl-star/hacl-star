module Spec.SHA2

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2.Constants
module S = FStar.Seq
module E = FStar.Kremlin.Endianness

open Spec.Hash.Definitions

(* The core compression, padding and extraction functions for all SHA2
 * algorithms. *)

(* Define the length of the constants. Also the number of scheduling rounds. *)
inline_for_extraction
let size_k_w: sha2_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80

inline_for_extraction
let word_n: sha2_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 32
  | SHA2_384 | SHA2_512 -> 64

let v' (#a: sha2_alg) (x:word a) = match a with
  | SHA2_224 | SHA2_256 -> U32.v x
  | SHA2_384 | SHA2_512 -> U64.v x

let k_w      (a: sha2_alg) = m:S.seq (word a) {S.length m = size_k_w a}
let block_w  (a: sha2_alg) = m:S.seq (word a) {S.length m = block_word_length}
let counter = nat

inline_for_extraction
let word_add_mod: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.add_mod
  | SHA2_384 | SHA2_512 -> U64.add_mod

inline_for_extraction
let word_logxor: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logxor
  | SHA2_384 | SHA2_512 -> U64.logxor

inline_for_extraction
let word_logand: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logand
  | SHA2_384 | SHA2_512 -> U64.logand

inline_for_extraction
let word_logor: a:sha2_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logor
  | SHA2_384 | SHA2_512 -> U64.logor

inline_for_extraction
let word_lognot: a:sha2_alg -> Tot ((word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.lognot
  | SHA2_384 | SHA2_512 -> U64.lognot

inline_for_extraction
let word_shift_right: t:sha2_alg -> Tot (a:word t -> s:U32.t -> Pure (word t)
  (requires (FStar.Mul.(U32.v s < 8 * word_length t)))
  (ensures (fun c -> v' c = (v' a / (pow2 (U32.v s)))))) = function
  | SHA2_224 | SHA2_256 -> U32.shift_right
  | SHA2_384 | SHA2_512 -> U64.shift_right

inline_for_extraction
let rotate_right32 (x:U32.t) (s:U32.t{0 < U32.v s /\ U32.v s < 32}): Tot U32.t =
  U32.((x >>^ s) |^ (x <<^ (32ul -^ s)))

inline_for_extraction
let rotate_right64 (a:U64.t) (s:U32.t{0 < U32.v s /\ U32.v s < 64}): Tot U64.t =
  U64.((a >>^ s) |^ (a <<^ (U32.sub 64ul s)))

inline_for_extraction
let word_rotate_right: a:sha2_alg -> Tot (word a -> s:U32.t{0 < U32.v s /\ U32.v s < word_n a} -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> rotate_right32
  | SHA2_384 | SHA2_512 -> rotate_right64

inline_for_extraction noextract
type ops = {
  c0: U32.t; c1: U32.t; c2: U32.t;
  c3: U32.t; c4: U32.t; c5: U32.t;
  e0: U32.t; e1: U32.t; e2: U32.t;
  e3: U32.t; e4: U32.t; e5: U32.t;
}

(* Definition of constants used in word functions *)
inline_for_extraction noextract
let op224_256: ops = {
  c0 = 2ul; c1 = 13ul; c2 = 22ul;
  c3 = 6ul; c4 = 11ul; c5 = 25ul;
  e0 = 7ul; e1 = 18ul; e2 = 3ul;
  e3 = 17ul; e4 = 19ul; e5 = 10ul
}

inline_for_extraction noextract
let op384_512: ops = {
  c0 = 28ul; c1 = 34ul; c2 = 39ul;
  c3 = 14ul; c4 = 18ul; c5 = 41ul;
  e0 = 1ul ; e1 =  8ul; e2 =  7ul;
  e3 = 19ul; e4 = 61ul; e5 =  6ul
}

inline_for_extraction
let op0: a:sha2_alg -> Tot ops = function
  | SHA2_224 -> op224_256
  | SHA2_256 -> op224_256
  | SHA2_384 -> op384_512
  | SHA2_512 -> op384_512


(* Definition of the SHA2 word functions *)
inline_for_extraction
val _Ch: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
inline_for_extraction
let _Ch a x y z = word_logxor a (word_logand a x y)
                                (word_logand a (word_lognot a x) z)

inline_for_extraction
val _Maj: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
inline_for_extraction
let _Maj a x y z = word_logxor a (word_logand a x y)
                                 (word_logxor a (word_logand a x z)
                                                (word_logand a y z))

inline_for_extraction
val _Sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _Sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).c0)
                                (word_logxor a (word_rotate_right a x (op0 a).c1)
                                               (word_rotate_right a x (op0 a).c2))

inline_for_extraction
val _Sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _Sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).c3)
                                (word_logxor a (word_rotate_right a x (op0 a).c4)
                                               (word_rotate_right a x (op0 a).c5))

inline_for_extraction
val _sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).e0)
                                (word_logxor a (word_rotate_right a x (op0 a).e1)
                                               (word_shift_right a x (op0 a).e2))

inline_for_extraction
val _sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).e3)
                                (word_logxor a (word_rotate_right a x (op0 a).e4)
                                               (word_shift_right a x (op0 a).e5))

let h0: a:sha2_alg -> Tot (m:words_state a) = function
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
let rec ws_aux (a:sha2_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < block_word_length then b.[t]
  else
    let t16 = ws_aux a b (t - 16) in
    let t15 = ws_aux a b (t - 15) in
    let t7  = ws_aux a b (t - 7) in
    let t2  = ws_aux a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (word_add_mod a s1 (word_add_mod a t7 (word_add_mod a s0 t16)))

[@"opaque_to_smt"]
let ws = ws_aux

(* Core shuffling function *)
let shuffle_core_aux (a:sha2_alg) (block:block_w a) (hash:words_state a) (t:counter{t < size_k_w a}): Tot (words_state a) =
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

[@"opaque_to_smt"]
let shuffle_core = shuffle_core_aux

(* Full shuffling function *)
let shuffle_aux (a:sha2_alg) (hash:words_state a) (block:block_w a): Tot (words_state a) =
  Spec.Loops.repeat_range 0 (size_k_w a) (shuffle_core a block) hash

[@"opaque_to_smt"]
let shuffle = shuffle_aux

let init = h0

(* Compression function *)
let update_aux (a:sha2_alg) (hash:words_state a) (block:bytes{S.length block = block_length a}): Tot (words_state a) =
  let block_w = words_of_bytes a block_word_length block in
  let hash_1 = shuffle a hash block_w in
  Spec.Loops.seq_map2 (word_add_mod a) hash hash_1

[@"opaque_to_smt"]
let update = update_aux

let pad = Spec.Hash.PadFinish.pad

let finish = Spec.Hash.PadFinish.finish
