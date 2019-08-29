module Spec.SHA2

open Lib.IntTypes
module C = Spec.SHA2.Constants
module S = FStar.Seq

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

inline_for_extraction
let to_word (a:sha2_alg) (n:nat{n < pow2 (word_n a)}) : word a =
  match a with
  | SHA2_224 | SHA2_256 -> u32 n
  | SHA2_384 | SHA2_512 -> u64 n

let v' (#a: sha2_alg) (x:word a) = match a with
  | SHA2_224 | SHA2_256 -> uint_v #U32 #SEC x
  | SHA2_384 | SHA2_512 -> uint_v #U64 #SEC x

let k_w      (a: sha2_alg) = m:S.seq (word a) {S.length m = size_k_w a}
let block_w  (a: sha2_alg) = m:S.seq (word a) {S.length m = block_word_length}
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
inline_for_extraction
let _Ch a x y z =  (x &. y) ^. (~.x &. z)

inline_for_extraction
val _Maj: a:sha2_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
inline_for_extraction
let _Maj a x y z = (x &. y) ^. ((x &. z) ^. (y &. z))

inline_for_extraction
val _Sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _Sigma0 a x = (x >>>. (op0 a).c0) ^. (x >>>. (op0 a).c1) ^. (x >>>. (op0 a).c2)

inline_for_extraction
val _Sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _Sigma1 a x = (x >>>. (op0 a).c3) ^. (x >>>. (op0 a).c4) ^. (x >>>. (op0 a).c5)

inline_for_extraction
val _sigma0: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _sigma0 a x = (x >>>. (op0 a).e0) ^. (x >>>. (op0 a).e1) ^. (x >>. (op0 a).e2)

inline_for_extraction
val _sigma1: a:sha2_alg -> x:(word a) -> Tot (word a)
inline_for_extraction
let _sigma1 a x = (x >>>. (op0 a).e3) ^. (x >>>. (op0 a).e4) ^. (x >>. (op0 a).e5)

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

(* Core shuffling function *)
let shuffle_core_pre_ (a:sha2_alg) (k_t: word a) (ws_t: word a) (hash:words_state a) : Tot (words_state a) =
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

[@"opaque_to_smt"]
let shuffle_core_pre = shuffle_core_pre_


(* Scheduling function *)

(* Recursive Version *)
let rec ws_aux (a:sha2_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < block_word_length then b.[t]
  else
    let t16 = ws_aux a b (t - 16) in
    let t15 = ws_aux a b (t - 15) in
    let t7  = ws_aux a b (t - 7) in
    let t2  = ws_aux a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (s1 +. t7 +. s0 +. t16)

[@"opaque_to_smt"]
let ws = ws_aux

(* Incremental Version *)
let ws_pre_inner (a:sha2_alg) (block:block_w a) (i:nat{i < size_k_w a}) (ws:k_w a) : k_w a =
    if i < block_word_length then
      Seq.upd ws i (Seq.index block i)
    else
      let t16 = ws.[i - 16] in
      let t15 = ws.[i - 15] in
      let t7  = ws.[i - 7] in
      let t2  = ws.[i - 2] in
      let s1 = _sigma1 a t2 in
      let s0 = _sigma0 a t15 in
      Seq.upd ws i (s1 +. t7 +. s0 +. t16)

let ws_pre_ (a:sha2_alg) (block:block_w a) : k_w a =
  Lib.LoopCombinators.repeati (size_k_w a) (ws_pre_inner a block) (Seq.create (size_k_w a) (to_word a 0))

[@"opaque_to_smt"]
let ws_pre = ws_pre_

(* Full shuffling function *)
let shuffle_pre (a:sha2_alg) (hash:words_state a) (block:block_w a): Tot (words_state a) =
  let ws = ws_pre a block in
  let k = k0 a in
  Lib.LoopCombinators.repeati (size_k_w a)
    (fun i h -> shuffle_core_pre a k.[i] ws.[i] h) hash

(* Core shuffling function *)
let shuffle_core_ (a:sha2_alg) (block:block_w a) (hash:words_state a) (t:counter{t < size_k_w a}): Tot (words_state a) =
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
  let t1 = h0 +. (_Sigma1 a e0) +. (_Ch a e0 f0 g0) +. (k0 a).[t] +. (ws a block t) in
  let t2 = (_Sigma0 a a0) +. (_Maj a a0 b0 c0) in

  (**) assert(t < S.length (k0 a));
  let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  assert_norm (List.Tot.length l = 8);
  S.seq_of_list l

[@"opaque_to_smt"]
let shuffle_core = shuffle_core_

(* Full shuffling function *)
let shuffle_aux (a:sha2_alg) (hash:words_state a) (block:block_w a): Tot (words_state a) =
  Spec.Loops.repeat_range 0 (size_k_w a) (shuffle_core a block) hash

[@"opaque_to_smt"]
let shuffle = shuffle_pre

#push-options "--max_fuel 1 --max_ifuel 0"

val shuffle_is_shuffle_pre: a:sha2_alg -> hash:words_state a -> block:block_w a ->
  Lemma (shuffle a hash block == shuffle_aux a hash block)
let shuffle_is_shuffle_pre a hash block =
  let rec repeati_is_repeat_range #a (n:nat)
    (f:a -> (i:nat{i < n}) -> Tot a)
    (f': (i:nat{i < n}) -> a -> Tot a)
    (i:nat{i <= n})
    (acc0:a)
    : Lemma
      (requires forall x i. f x i == f' i x)
      (ensures Spec.Loops.repeat_range 0 i f acc0 == Lib.LoopCombinators.repeati i f' acc0)
    = if i = 0 then (
         Lib.LoopCombinators.eq_repeati0 n f' acc0
      ) else (
         Spec.Loops.repeat_range_induction 0 i f acc0;
         Lib.LoopCombinators.unfold_repeati n f' acc0 (i-1);
         repeati_is_repeat_range n f f' (i-1) acc0
      )
  in
  let rec ws_is_ws_pre (i:nat{i <= size_k_w a}) : Lemma
    (ensures forall (j:nat{j < i}).
      ws a block j ==
      (Lib.LoopCombinators.repeati i
        (ws_pre_inner a block)
        (Seq.create (size_k_w a) (to_word a 0))).[j]
    )

    = if i = 0 then ()
      else (
        ws_is_ws_pre (i - 1);

        Lib.LoopCombinators.unfold_repeati (size_k_w a) (ws_pre_inner a block)
          (Seq.create (size_k_w a) (to_word a 0)) (i - 1);

        let f = ws_pre_inner a block in
        let acc0 = Seq.create (size_k_w a) (to_word a 0) in

        assert (Lib.LoopCombinators.repeati i f acc0 ==
          f (i - 1) (Lib.LoopCombinators.repeati (i-1) f acc0));
        reveal_opaque (`%ws) ws
      )
  in
  let ws = ws_pre a block in
  let k = k0 a in
  let shuffle_core_is_shuffle_core_pre
    hash
    (i:counter{i < size_k_w a})
    : Lemma (shuffle_core a block hash i == shuffle_core_pre a (k0 a).[i] (ws_pre a block).[i] hash)
    = ws_is_ws_pre (size_k_w a);
      reveal_opaque (`%ws_pre) ws_pre;
      reveal_opaque (`%shuffle_core) shuffle_core;
      reveal_opaque (`%shuffle_core_pre) shuffle_core_pre
  in
  Classical.forall_intro_2 shuffle_core_is_shuffle_core_pre;
  repeati_is_repeat_range (size_k_w a) (shuffle_core a block) (fun i h -> shuffle_core_pre a (k0 a).[i] (ws_pre a block).[i] h) (size_k_w a) hash;
  assert (shuffle_pre a hash block == shuffle_aux a hash block);
  reveal_opaque (`%shuffle) shuffle

#pop-options

let init = h0

(* Compression function *)
let update_aux (a:sha2_alg) (hash:words_state a) (block:bytes{S.length block = block_length a}): Tot (words_state a) =
  let block_w = words_of_bytes a #block_word_length block in
  let hash_1 = shuffle_aux a hash block_w in
  Lib.Sequence.map2 ( +. ) (hash <: Lib.Sequence.lseq (word a) (state_word_length a)) hash_1

let update_pre (a:sha2_alg) (hash:words_state a) (block:bytes{S.length block = block_length a}): Tot (words_state a) =
  let block_w = words_of_bytes a #block_word_length block in
  let hash_1 = shuffle a hash block_w in
  Spec.Loops.seq_map2 ( +. ) (hash <: Lib.Sequence.lseq (word a) (state_word_length a)) hash_1

[@"opaque_to_smt"]
let update = update_pre

val update_is_update_pre: a:sha2_alg -> hash:words_state a -> block:bytes{S.length block = block_length a} ->
  Lemma (update a hash block == update_aux a hash block)
let update_is_update_pre a hash block =
  let block_w = words_of_bytes a #block_word_length block in
  let hash_1 = shuffle a hash block_w in
  shuffle_is_shuffle_pre a hash block_w;
  let hash:Lib.Sequence.lseq (word a) (state_word_length a) = hash in
  reveal_opaque (`%update) update;
  let s1 = Lib.Sequence.map2 (+.) hash hash_1 in
  let s2 = Spec.Loops.seq_map2 (+.) hash hash_1 in
  assert (Seq.length s1 == Seq.length s2);
  let aux (i:nat{i < Seq.length s1}) : Lemma (Seq.index s1 i == Seq.index s2 i)
    =
      // Need Lib.Sequence.index in the context for map2's postcondition to trigger
      assert (Lib.Sequence.index s1 i == ( +. ) (Seq.index hash i) (Seq.index hash_1 i))
  in Classical.forall_intro aux;
  assert (s1 `Seq.equal` s2)


let pad = Spec.Hash.PadFinish.pad

let finish = Spec.Hash.PadFinish.finish
