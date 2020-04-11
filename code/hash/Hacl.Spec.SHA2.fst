module Hacl.Spec.SHA2

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
module C = Spec.SHA2.Constants
module S = FStar.Seq

open Spec.Hash.Definitions

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

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

inline_for_extraction
let to_word (a:sha2_alg) (n:nat{n < pow2 (word_n a)}) : word a =
  match a with
  | SHA2_224 | SHA2_256 -> u32 n
  | SHA2_384 | SHA2_512 -> u64 n

let v' (#a: sha2_alg) (x:word a) = match a with
  | SHA2_224 | SHA2_256 -> uint_v #U32 #SEC x
  | SHA2_384 | SHA2_512 -> uint_v #U64 #SEC x

inline_for_extraction
let num_rounds16 (a:sha2_alg) : n:pos{16 * n == size_k_w a} =
  match a with
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 5

let k_w   (a: sha2_alg) = lseq (word a) block_word_length
let block_t (a: sha2_alg) = lseq uint8 (block_length a)
let counter = nat

inline_for_extraction noextract
type ops = {
  c0: size_t; c1: size_t; c2: size_t;
  c3: size_t; c4: size_t; c5: size_t;
  e0: size_t; e1: size_t; e2: size_t;
  e3: size_t; e4: size_t; e5: size_t;
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

inline_for_extraction
let ( +. ) (#a:sha2_alg): word a -> word a -> word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( +. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( +. ) #U64 #SEC

inline_for_extraction
let ( ^. ) (#a:sha2_alg): word a -> word a -> word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( ^. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( ^. ) #U64 #SEC


inline_for_extraction
let ( &. ) (#a:sha2_alg): word a -> word a -> word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( &. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( &. ) #U64 #SEC

inline_for_extraction
let ( ~. ) (#a:sha2_alg): word a -> word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( ~. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( ~. ) #U64 #SEC

inline_for_extraction
let ( >>>. ) (#a:sha2_alg): word a -> rotval (word_t a) -> word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>>. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( >>>. ) #U64 #SEC

inline_for_extraction
let ( >>. ) (#a:sha2_alg): word a -> shiftval (word_t a) ->  word a =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>. ) #U32 #SEC
  | SHA2_384 | SHA2_512 -> ( >>. ) #U64 #SEC

(* Definition of the SHA2 word functions *)
inline_for_extraction
val _Ch: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Ch a x y z =  (x &. y) ^. (~.x &. z)

inline_for_extraction
val _Maj: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Maj a x y z = (x &. y) ^. ((x &. z) ^. (y &. z))

inline_for_extraction
val _Sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
let _Sigma0 a x = (x >>>. (op0 a).c0) ^. (x >>>. (op0 a).c1) ^. (x >>>. (op0 a).c2)

inline_for_extraction
val _Sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
let _Sigma1 a x = (x >>>. (op0 a).c3) ^. (x >>>. (op0 a).c4) ^. (x >>>. (op0 a).c5)

inline_for_extraction
val _sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
let _sigma0 a x = (x >>>. (op0 a).e0) ^. (x >>>. (op0 a).e1) ^. (x >>. (op0 a).e2)

inline_for_extraction
val _sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
let _sigma1 a x = (x >>>. (op0 a).e3) ^. (x >>>. (op0 a).e4) ^. (x >>. (op0 a).e5)

let h0: a:sha2_alg -> Tot (words_state a) = function
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

(* Core shuffling function *)

let shuffle_core_pre (a:sha2_alg) (k_t: word a) (ws_t: word a) (hash:words_state a) : Tot (words_state a) =
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
  let t1 = h0 +. (_Sigma1 a e0) +. (_Ch a e0 f0 g0) +. k_t +. ws_t in
  let t2 = (_Sigma0 a a0) +. (_Maj a a0 b0 c0) in

  let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  assert_norm (List.Tot.length l = 8);
  S.seq_of_list l

(* Scheduling function *)

let ws_next_inner (a:sha2_alg) (i:nat{i < 16}) (ws:k_w a) : k_w a =
  let t16 = ws.[i] in
  let t15 = ws.[(i+1) % 16] in
  let t7  = ws.[(i+9) % 16] in
  let t2  = ws.[(i+14) % 16] in
  let s1 = _sigma1 a t2 in
  let s0 = _sigma0 a t15 in
  Seq.upd ws i (s1 +. t7 +. s0 +. t16)

let ws_next (a:sha2_alg) (ws:k_w a) : k_w a =
  Lib.LoopCombinators.repeati 16 (ws_next_inner a) ws


val shuffle_inner:
    a:sha2_alg
  -> ws:k_w a
  -> i:nat{i < num_rounds16 a}
  -> j:nat{j < 16}
  -> hash:words_state a ->
  words_state a

let shuffle_inner a ws i j hash =
  let k_t = Seq.index (k0 a) (16 * i + j) in
  let ws_t = ws.[j] in
  shuffle_core_pre a k_t ws_t hash


val shuffle_inner_loop:
    a:sha2_alg
  -> i:nat{i < num_rounds16 a}
  -> ws_st:tuple2 (k_w a) (words_state a) ->
  k_w a & words_state a

let shuffle_inner_loop a i (ws, st) =
  let st' = Lib.LoopCombinators.repeati 16 (shuffle_inner a ws i) st in
  let ws' = if i < num_rounds16 a - 1 then ws_next a ws else ws in
  (ws', st')

(* Full shuffling function *)

let shuffle (a:sha2_alg) (ws:k_w a) (hash:words_state a) : Tot (words_state a) =
  let (ws, st) = Lib.LoopCombinators.repeati (num_rounds16 a) (shuffle_inner_loop a) (ws, hash) in
  st


let init = h0

let update (a:sha2_alg) (block:block_t a) (hash:words_state a): Tot (words_state a) =
  let block_w = Lib.ByteSequence.uints_from_bytes_be #(word_t a) #SEC block in
  let hash_1 = shuffle a block_w hash in
  map2 #_ #_ #_ #8 ( +. ) hash_1 hash


let padded_blocks (a:sha2_alg) (len:size_nat{len < block_length a}) : n:nat{n <= 2} =
  if (len + len_length a + 1 <= block_length a) then 1 else 2


let load_last (a:sha2_alg) (totlen_seq:lseq uint8 (len_length a))
   (fin:size_nat{fin == block_length a \/ fin == 2 * block_length a})
   (len:size_nat{len < block_length a}) (b:bytes{S.length b = len}) :
   (block_t a & block_t a)
 =
  let last = create (2 * block_length a) (u8 0) in
  let last = update_sub last 0 len b in
  let last = last.[len] <- u8 0x80 in
  let last = update_sub last (fin - len_length a) (len_length a) totlen_seq in
  let b0 = sub last 0 (block_length a) in
  let b1 = sub last (block_length a) (block_length a) in
  (b0, b1)


let update_last (a:sha2_alg) (totlen:len_t a)
  (len:size_nat{len < block_length a})
  (b:bytes{S.length b = len}) (hash:words_state a) : Tot (words_state a) =
  let blocks = padded_blocks a len in
  let fin = blocks * block_length a in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in
  let totlen_seq = Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let (b0, b1) = load_last a totlen_seq fin len b in
  let hash = update a b0 hash in
  if blocks > 1 then update a b1 hash else hash


let store_state (a:sha2_alg) (hashw:words_state a) : Tot (lseq uint8 (8 * word_length a)) =
  Lib.ByteSequence.uints_to_bytes_be #(word_t a) #SEC #8 hashw


let emit (a:sha2_alg) (h:lseq uint8 (8 * word_length a)) : Tot (lseq uint8 (hash_length a)) =
  sub h 0 (hash_length a)


let hash (#a:sha2_alg) (len:size_nat) (b:lseq uint8 len) =
  let len' = mk_int #(len_int_type a) #PUB len in
  let st = init a in
  let blocks = len / block_length a in
  let rem = len % block_length a in
  let st = Lib.LoopCombinators.repeati blocks
  (fun i st ->
    let mb = sub b (i * block_length a) (block_length a) in
    update a mb st) st in
  let mb = sub b (len - rem) rem in
  let st = update_last a len' rem mb st in
  let hseq = store_state a st in
  emit a hseq


let sha224 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_224 len b

let sha256 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_256 len b

let sha384 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_384 len b

let sha512 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_512 len b
