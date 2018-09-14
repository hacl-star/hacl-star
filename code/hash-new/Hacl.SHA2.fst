module Hacl.SHA2

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module Common = Hacl.Hash.Common
module Cast = FStar.Int.Cast.Full
module Constants = Spec.SHA2.Constants
module Tactics = FStar.Tactics
module Helpers = Spec.Hash.Helpers
module Endianness = FStar.Kremlin.Endianness
module Math = FStar.Math.Lemmas
module Spec = Spec.SHA2

module M = LowStar.Modifies
module S = FStar.Seq
module B = LowStar.Buffer
module G = FStar.Ghost
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open Spec.Hash.Helpers
open LowStar.BufferOps
open Hacl.Hash.Lemmas
open Hacl.Hash.Common

friend Spec.SHA2
friend Hacl.Hash.Common


module IB = LowStar.ImmutableBuffer

#set-options "--max_fuel 0 --max_ifuel 0"

(** Top-level constant arrays for the SHA2 algorithms. *)

let h224 = IB.igcmalloc_of_list HS.root Constants.h224_l
let h256 = IB.igcmalloc_of_list HS.root Constants.h256_l
let h384 = IB.igcmalloc_of_list HS.root Constants.h384_l
let h512 = IB.igcmalloc_of_list HS.root Constants.h512_l

noextract
let h (a: sha2_alg): S.lseq (word a) 8 =
  match a with
  | SHA2_224 -> Constants.h224
  | SHA2_256 -> Constants.h256
  | SHA2_384 -> Constants.h384
  | SHA2_512 -> Constants.h512

noextract
let index_h (a: sha2_alg) (i: U32.t): ST.Stack (word a)
  (requires (fun _ -> U32.v i < 8))
  (ensures (fun h0 r h1 ->
    B.(modifies loc_none h0 h1) /\
    r = S.index (h a) (U32.v i)))
=
    match a with
    | SHA2_224 -> B.recall h224; IB.recall_contents h224 Constants.h224; h224.(i)
    | SHA2_256 -> B.recall h256; IB.recall_contents h256 Constants.h256; h256.(i)
    | SHA2_384 -> B.recall h384; IB.recall_contents h384 Constants.h384; h384.(i)
    | SHA2_512 -> B.recall h512; IB.recall_contents h512 Constants.h512; h512.(i)

let k224_256 = IB.igcmalloc_of_list HS.root Constants.k224_256_l
let k384_512 = IB.igcmalloc_of_list HS.root Constants.k384_512_l


(** Alloca *)

#set-options "--max_fuel 1"

noextract
val alloca: a:sha2_alg -> alloca_st a
noextract
let alloca a () =
  [@ inline_let ]
  let l: list (word a) = Spec.(match a with
    | SHA2_224 -> Constants.h224_l
    | SHA2_256 -> Constants.h256_l
    | SHA2_384 -> Constants.h384_l
    | SHA2_512 -> Constants.h512_l) in
  B.alloca_of_list l

#set-options "--max_fuel 0"

let alloca_224: alloca_st SHA2_224 =
  Tactics.(synth_by_tactic (specialize (alloca SHA2_224) [`%alloca]))
let alloca_256: alloca_st SHA2_256 =
  Tactics.(synth_by_tactic (specialize (alloca SHA2_256) [`%alloca]))
let alloca_384: alloca_st SHA2_384 =
  Tactics.(synth_by_tactic (specialize (alloca SHA2_384) [`%alloca]))
let alloca_512: alloca_st SHA2_512 =
  Tactics.(synth_by_tactic (specialize (alloca SHA2_512) [`%alloca]))

(** Init *)

noextract
val init: a:sha2_alg -> init_st a
noextract
let init a s =
  let h0 = ST.get () in
  let inv h1 (i: nat): Type0 =
    i <= 8 /\
    M.(modifies (loc_buffer s) h0 h1) /\
    S.equal (S.slice (B.as_seq h1 s) 0 i) (S.slice (h a) 0 i)
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < 8) }):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 -> U32.(inv h0 (v i) /\ inv h1 (v i + 1))))
  =
    s.(i) <- index_h a i;
    let h2 = ST.get () in
    assert (S.equal (S.slice (B.as_seq h2 s) 0 (U32.v i + 1))
      (S.append
        (S.slice (B.as_seq h2 s) 0 (U32.v i))
        (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1))))
  in
  C.Loops.for 0ul 8ul inv f

let init_224: init_st SHA2_224 =
  Tactics.(synth_by_tactic (specialize (init SHA2_224) [`%init; `%index_h]))
let init_256: init_st SHA2_256 =
  Tactics.(synth_by_tactic (specialize (init SHA2_256) [`%init; `%index_h]))
let init_384: init_st SHA2_384 =
  Tactics.(synth_by_tactic (specialize (init SHA2_384) [`%init; `%index_h]))
let init_512: init_st SHA2_512 =
  Tactics.(synth_by_tactic (specialize (init SHA2_512) [`%init; `%h]))


(** Update *)

inline_for_extraction
let block_w (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = Helpers.size_block_w }

let block_b (a: sha2_alg) =
  b:B.buffer U8.t { FStar.Mul.(B.length b = size_block_w * size_word a) }

inline_for_extraction
let ws_w (a: sha2_alg) = b:B.buffer (word a) { B.length b = Spec.size_k_w a }

let block_words_be (a: sha2_alg) (h: HS.mem) (b: block_b a) =
  words_from_be a size_block_w (B.as_seq h b)

inline_for_extraction
val ws (a: sha2_alg) (b: block_b a) (ws: ws_w a):
  ST.Stack unit
    (requires (fun h ->
      B.live h b /\ B.live h ws /\ B.disjoint b ws))
    (ensures (fun h0 _ h1 ->
      let b = block_words_be a h0 b in
      M.(modifies (loc_buffer ws) h0 h1) /\
      B.as_seq h1 ws == S.init (Spec.size_k_w a) (Spec.ws a b)))

inline_for_extraction
let index_be (a: sha2_alg) (b: B.buffer U8.t) (i: U32.t):
  ST.Stack (word a)
    (requires (fun h ->
      B.length b % size_word a = 0 /\
      B.live h b /\
      U32.v i < B.length b / size_word a))
    (ensures (fun h0 r h1 ->
       M.(modifies loc_none h0 h1) /\
       r = S.index (words_from_be a (B.length b / size_word a) (B.as_seq h0 b)) (U32.v i)))
=
  match a with
  | SHA2_224 | SHA2_256 -> C.Endianness.index_32_be b i
  | SHA2_384 | SHA2_512 -> C.Endianness.index_64_be b i

#set-options "--max_fuel 1 --z3rlimit 100"

inline_for_extraction
let ws a b ws =
  let h0 = ST.get () in
  let inv h1 (i: nat): Type0 =
    let b = block_words_be a h0 b in
    i <= Spec.size_k_w a /\
    M.(modifies (loc_buffer ws) h0 h1) /\
    S.equal (S.slice (B.as_seq h1 ws) 0 i) (S.init i (Spec.ws a b))
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < Spec.size_k_w a) }):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 -> U32.(inv h0 (v i) /\ inv h1 (v i + 1))))
  =
    if U32.(i <^ 16ul) then begin
      (**) let h1 = ST.get () in
      ws.(i) <- index_be a b i;
      (**) let h2 = ST.get () in
      (**) init_next (B.as_seq h2 ws) (Spec.ws a (block_words_be a h0 b)) (U32.v i)
    end else
      let h1 = ST.get () in
      let t16 = ws.(U32.sub i 16ul) in
      let t15 = ws.(U32.sub i 15ul) in
      let t7  = ws.(U32.sub i 7ul) in
      let t2  = ws.(U32.sub i 2ul) in

      // JP: TODO, understand why this is not going through.
      (**) assert (S.index (B.as_seq h1 ws) (U32.v i - 16) ==
      (**)   S.index (S.init (U32.v i) (Spec.ws a (block_words_be a h0 b))) (U32.v i - 16));
      (**) assert (t16 == Spec.ws a (block_words_be a h0 b) (U32.v i - 16));
      (**) assert (S.index (B.as_seq h1 ws) (U32.v i - 15) ==
      (**)   S.index (S.init (U32.v i) (Spec.ws a (block_words_be a h0 b))) (U32.v i - 15));
      (**) assert (t15 == Spec.ws a (block_words_be a h0 b) (U32.v i - 15));
      (**) assert (S.index (B.as_seq h1 ws) (U32.v i - 7) ==
      (**)   S.index (S.init (U32.v i) (Spec.ws a (block_words_be a h0 b))) (U32.v i - 7));
      (**) assert (t7 == Spec.ws a (block_words_be a h0 b) (U32.v i - 7));
      (**) assert (S.index (B.as_seq h1 ws) (U32.v i - 2) ==
      (**)   S.index (S.init (U32.v i) (Spec.ws a (block_words_be a h0 b))) (U32.v i - 2));
      (**) assert (t2 == Spec.ws a (block_words_be a h0 b) (U32.v i - 2));

      let s1 = Spec._sigma1 a t2 in
      let s0 = Spec._sigma0 a t15 in
      let w = Spec.word_add_mod a s1 (Spec.word_add_mod a t7 (Spec.word_add_mod a s0 t16)) in
      ws.(i) <- w;
      (**) let h2 = ST.get () in
      (**) init_next (B.as_seq h2 ws) (Spec.ws a (block_words_be a h0 b)) (U32.v i)
  in
  C.Loops.for 0ul (U32.uint_to_t (Spec.size_k_w a)) inv f

#set-options "--max_fuel 0 --z3rlimit 20"

inline_for_extraction
let hash_w (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = size_hash_w a }

inline_for_extraction
val k0 (a: sha2_alg): ST.Stack (IB.ibuffer (word a))
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    B.length b = Spec.size_k_w a /\
    B.live h1 b /\
    M.(modifies loc_none h0 h1) /\
    B.as_seq h1 b == Spec.k0 a))
inline_for_extraction
let k0 a =
  match a with
  | SHA2_224 | SHA2_256 ->
      IB.recall_contents k224_256 (S.seq_of_list Constants.k224_256_l);
      k224_256
  | SHA2_384 | SHA2_512 ->
      IB.recall_contents k384_512 (S.seq_of_list Constants.k384_512_l);
      k384_512

inline_for_extraction unfold
let add = Spec.word_add_mod

inline_for_extraction
val shuffle_core (a: sha2_alg)
  (block: G.erased (block_b a))
  (hash: hash_w a)
  (ws: ws_w a)
  (t: U32.t { U32.v t < Spec.size_k_w a }):
  ST.Stack unit
    (requires (fun h ->
      let block = G.reveal block in
      let b = block_words_be a h block in
      B.live h block /\ B.live h hash /\ B.live h ws /\
      B.disjoint block hash /\ B.disjoint block ws /\ B.disjoint hash ws /\
      B.as_seq h ws == S.init (Spec.size_k_w a) (Spec.ws a b)))
    (ensures (fun h0 _ h1 ->
      let block = G.reveal block in
      let b = block_words_be a h0 block in
      M.(modifies (loc_buffer hash) h0 h1) /\
      B.as_seq h1 hash == Spec.shuffle_core a b (B.as_seq h0 hash) (U32.v t)))

#set-options "--z3rlimit 50"
inline_for_extraction
let shuffle_core a block hash ws t =
  let a0 = hash.(0ul) in
  let b0 = hash.(1ul) in
  let c0 = hash.(2ul) in
  let d0 = hash.(3ul) in
  let e0 = hash.(4ul) in
  let f0 = hash.(5ul) in
  let g0 = hash.(6ul) in
  let h0 = hash.(7ul) in

  let w = ws.(t) in

  let t1 = add a h0 (add a (Spec._Sigma1 a e0) (add a (Spec._Ch a e0 f0 g0) (add a (k0 a).(t) w))) in
  let t2 = add a (Spec._Sigma0 a a0) (Spec._Maj a a0 b0 c0) in

  hash.(0ul) <- add a t1 t2;
  hash.(1ul) <- a0;
  hash.(2ul) <- b0;
  hash.(3ul) <- c0;
  hash.(4ul) <- add a d0 t1;
  hash.(5ul) <- e0;
  hash.(6ul) <- f0;
  hash.(7ul) <- g0;

  (**) let h = ST.get () in
  (**) [@inline_let]
  (**) let l = [ add a t1 t2; a0; b0; c0; add a d0 t1; e0; f0; g0 ] in
  (**) assert_norm (List.Tot.length l = 8);
  (**) S.intro_of_list #(word a) (B.as_seq h hash) l

inline_for_extraction
val shuffle: a:sha2_alg -> block:G.erased (block_b a) -> hash:hash_w a -> ws:ws_w a ->
  ST.Stack unit
    (requires (fun h ->
      let block = G.reveal block in
      let b = block_words_be a h block in
      B.live h block /\ B.live h hash /\ B.live h ws /\
      B.disjoint block hash /\ B.disjoint block ws /\ B.disjoint hash ws /\
      B.as_seq h ws == S.init (Spec.size_k_w a) (Spec.ws a b)))
    (ensures (fun h0 _ h1 ->
      let block = G.reveal block in
      let b = block_words_be a h0 block in
      M.(modifies (loc_buffer hash) h0 h1 /\
      B.as_seq h1 hash == Spec.shuffle a (B.as_seq h0 hash) b)))

inline_for_extraction
let size_k_w (a: sha2_alg) = U32.uint_to_t (Spec.size_k_w a)

inline_for_extraction
let shuffle a block hash ws =
  let h0 = ST.get () in
  let inv (h1: HS.mem) (i: nat) =
    let block = G.reveal block in
    let block = block_words_be a h0 block in
    M.(modifies (loc_buffer hash) h0 h1) /\
    i <= Spec.size_k_w a /\
    B.as_seq h1 hash ==
      Spec.Loops.repeat_range 0 i (Spec.shuffle_core a block) (B.as_seq h0 hash)
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < Spec.size_k_w a)}):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 ->
        U32.(inv h0 (v i) /\ inv h1 (v i + 1))))
  =
    (**) let h1 = ST.get () in
    shuffle_core a block hash ws i;
    (**) let h2 = ST.get () in
    (**) let block = G.reveal block in
    (**) let block = block_words_be a h0 block in
    (**) let hash = B.as_seq h0 hash in
    (**) Spec.Loops.repeat_range_induction 0 (U32.v i + 1) (Spec.shuffle_core a block) hash
  in
  (**) Spec.Loops.repeat_range_base 0 (Spec.shuffle_core a (block_words_be a h0 (G.reveal block))) (B.as_seq h0 hash);
  C.Loops.for 0ul (size_k_w a) inv f


inline_for_extraction
let zero (a: sha2_alg): word a =
  match a with
  | SHA2_224 | SHA2_256 -> 0ul
  | SHA2_384 | SHA2_512 -> 0UL

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

noextract
val update: a:sha2_alg -> update_st a
noextract
let update a hash block =
  (**) ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash1: hash_w a = B.alloca (zero a) 8ul in
  let computed_ws: ws_w a = B.alloca (zero a) (U32.uint_to_t (Spec.size_k_w a)) in
  ws a block computed_ws;
  B.blit hash 0ul hash1 0ul 8ul;
  (**) let h1 = ST.get () in
  (**) assert (S.equal (B.as_seq h1 hash1) (B.as_seq h0 hash));
  (**) assert (S.equal (B.as_seq h1 hash) (B.as_seq h0 hash));
  shuffle a (G.hide block) hash1 computed_ws;
  C.Loops.in_place_map2 hash hash1 8ul (add a);
  (**) ST.pop_frame ()

let update_224: update_st SHA2_224 =
  Tactics.(synth_by_tactic (specialize (update SHA2_224) [`%update; `%shuffle; `%shuffle_core; `%ws]))
let update_256: update_st SHA2_256 =
  Tactics.(synth_by_tactic (specialize (update SHA2_256) [`%update; `%shuffle; `%shuffle_core; `%ws]))
let update_384: update_st SHA2_384 =
  Tactics.(synth_by_tactic (specialize (update SHA2_384) [`%update; `%shuffle; `%shuffle_core; `%ws]))
let update_512: update_st SHA2_512 =
  Tactics.(synth_by_tactic (specialize (update SHA2_512) [`%update; `%shuffle; `%shuffle_core; `%ws]))

let pad_224: pad_st SHA2_224 =
  Tactics.(synth_by_tactic (specialize (Common.pad SHA2_224) [`%Common.pad]))
let pad_256: pad_st SHA2_256 =
  Tactics.(synth_by_tactic (specialize (Common.pad SHA2_256) [`%Common.pad]))
let pad_384: pad_st SHA2_384 =
  Tactics.(synth_by_tactic (specialize (Common.pad SHA2_384) [`%Common.pad]))
let pad_512: pad_st SHA2_512 =
  Tactics.(synth_by_tactic (specialize (Common.pad SHA2_512) [`%Common.pad]))

let finish_224: finish_st SHA2_224 =
  Tactics.(synth_by_tactic (specialize (Common.finish SHA2_224) [`%Common.finish]))
let finish_256: finish_st SHA2_256 =
  Tactics.(synth_by_tactic (specialize (Common.finish SHA2_256) [`%Common.finish]))
let finish_384: finish_st SHA2_384 =
  Tactics.(synth_by_tactic (specialize (Common.finish SHA2_384) [`%Common.finish]))
let finish_512: finish_st SHA2_512 =
  Tactics.(synth_by_tactic (specialize (Common.finish SHA2_512) [`%Common.finish]))

