module Hacl.Impl.SHA2_512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.HyperStack.ST
open FStar.Buffer

open C.Compat.Loops

open Hacl.Spec.Endianness
open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Hash.Lib.Create
open Hacl.Hash.Lib.LoadStore


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H32 = Hacl.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module Cast = Hacl.Cast

module Spec = Spec.SHA2_512
module Lemmas = Hacl.Impl.SHA2_512.Lemmas


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t
private let uint128_ht = Hacl.UInt128.t

private let uint64_p = Buffer.buffer uint64_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
inline_for_extraction let  u8_to_h8 = Cast.uint8_to_sint8
inline_for_extraction let  u32_to_h32 = Cast.uint32_to_sint32
inline_for_extraction let  u32_to_u64 = FStar.Int.Cast.uint32_to_uint64
inline_for_extraction let  u32_to_h64 = Cast.uint32_to_sint64
inline_for_extraction let  h32_to_h8  = Cast.sint32_to_sint8
inline_for_extraction let  h32_to_h64 = Cast.sint32_to_sint64
inline_for_extraction let  u32_to_h128 = Cast.uint32_to_sint128
inline_for_extraction let  u64_to_u32 = FStar.Int.Cast.uint64_to_uint32
inline_for_extraction let  u64_to_h64 = Cast.uint64_to_sint64
inline_for_extraction let  u64_to_h128 = Cast.uint64_to_sint128
inline_for_extraction let  h64_to_h32 = Cast.sint64_to_sint32
inline_for_extraction let  h64_to_h128 = Cast.sint64_to_sint128


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 10"

//
// SHA-512
//

(* Define word size *)
inline_for_extraction let word_length = 8ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let state_word_length   = 8ul // 8 words (Final hash output size)
inline_for_extraction let block_word_length  = 16ul  // 16 words (Working data block size)
inline_for_extraction let hash_length     = word_length *^ state_word_length
inline_for_extraction let block_length    = word_length *^ block_word_length

(* Sizes of objects in the state *)
inline_for_extraction let size_k_w     = 80ul  // 80 words of 64 bits (block_length)
inline_for_extraction let size_ws_w    = size_k_w
inline_for_extraction let size_whash_w = state_word_length
inline_for_extraction let size_count_w = 1ul  // 1 word
inline_for_extraction let len_length   = 2ul *^ word_length

inline_for_extraction let size_state   = size_k_w +^ size_ws_w +^ size_whash_w +^ size_count_w

(* Positions of objects in the state *)
inline_for_extraction let pos_k_w      = 0ul
inline_for_extraction let pos_ws_w     = size_k_w
inline_for_extraction let pos_whash_w  = size_k_w +^ size_ws_w
inline_for_extraction let pos_count_w  = size_k_w +^ size_ws_w +^ size_whash_w


[@"substitute"]
let rotate_right64 (a:uint64_ht) (b:uint32_t{0 < v b && v b < 64}) : Tot uint64_ht =
  H64.logor (H64.shift_right a b) (H64.shift_left a (U32.sub 64ul b))

[@"substitute"]
private val _Ch: x:uint64_ht -> y:uint64_ht -> z:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Ch x y z = H64.logxor (H64.logand x y) (H64.logand (H64.lognot x) z)

[@"substitute"]
private val _Maj: x:uint64_ht -> y:uint64_ht -> z:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Maj x y z = H64.logxor (H64.logand x y) (H64.logxor (H64.logand x z) (H64.logand y z))

[@"substitute"]
private val _Sigma0: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Sigma0 x = H64.logxor (rotate_right64 x 28ul) (H64.logxor (rotate_right64 x 34ul) (rotate_right64 x 39ul))

[@"substitute"]
private val _Sigma1: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _Sigma1 x = H64.logxor (rotate_right64 x 14ul) (H64.logxor (rotate_right64 x 18ul) (rotate_right64 x 41ul))

[@"substitute"]
private val _sigma0: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _sigma0 x = H64.logxor (rotate_right64 x 1ul) (H64.logxor (rotate_right64 x 8ul) (H64.shift_right x 7ul))

[@"substitute"]
private val _sigma1: x:uint64_ht -> Tot uint64_ht
[@"substitute"]
let _sigma1 x = H64.logxor (rotate_right64 x 19ul) (H64.logxor (rotate_right64 x 61ul) (H64.shift_right x 6ul))


#reset-options " --z3refresh --max_fuel 0 --z3rlimit 10"

[@"substitute"]
private val constants_set_k:
  k:uint64_p{length k = v size_k_w} ->
  Stack unit
        (requires (fun h -> live h k))
        (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1
                 /\ (let seq_k = Hacl.Spec.Endianness.reveal_h64s (as_seq h1 k) in
                   seq_k == Spec.k)))

private
let assign_k:
  b:buffer UInt64.t ->
    Stack unit
      (requires (fun h0 ->
        live h0 b /\ length b = List.Tot.length Spec.k_list))
      (ensures (fun h0 _ h1 ->
        live h1 b /\ modifies_1 b h0 h1 /\ as_seq h1 b == Seq.seq_of_list Spec.k_list)) =
  let open FStar.Tactics in
  synth_by_tactic (specialize (assignL (normalize_term Spec.k_list)) [`%assignL])

let constants_set_k k =
  assign_k k

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 10"

[@"substitute"]
val constants_set_h_0:
  hash:uint64_p{length hash = v state_word_length} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1
             /\ (let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s (as_seq h1 hash) in
                seq_h_0 == Spec.h_0)))

private
let assign_h0:
  b:buffer UInt64.t ->
    Stack unit
      (requires (fun h0 ->
        live h0 b /\ length b = List.Tot.length Spec.h_0_list))
      (ensures (fun h0 _ h1 ->
        live h1 b /\ modifies_1 b h0 h1 /\ as_seq h1 b == Seq.seq_of_list Spec.h_0_list)) =
  let open FStar.Tactics in
  synth_by_tactic (specialize (assignL (normalize_term Spec.h_0_list)) [`%assignL])


[@"substitute"]
let constants_set_h_0 hash =
  assign_h0 hash

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 20"

[@ Substitute]
private
val ws_part_1_core:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v block_word_length /\ disjoint ws_w block_w} ->
  i:UInt32.t{UInt32.v i < 16} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w
                  /\ (let seq_ws = reveal_h64s (as_seq h ws_w) in
                  let seq_block = reveal_h64s (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index seq_ws j)} j < UInt32.v i ==> Seq.index seq_ws j == Spec.ws seq_block j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  as_seq h1 block_w == as_seq h0 block_w
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i+1 ==> Seq.index w j == Spec.ws b j))))

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 100"

[@ Substitute]
let ws_part_1_core ws_w block_w t =
  (**) let h0 = ST.get() in
  (**) let h = ST.get() in
  let b = block_w.(t) in
  ws_w.(t) <- b;
  (**) let h1 = ST.get() in
  (**) let h' = ST.get() in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
  (**) Lemmas.lemma_spec_ws_def (reveal_h64s (as_seq h block_w)) (UInt32.v t);
  (**) assert(Seq.index (reveal_h64s (as_seq h1 ws_w)) (UInt32.v t) == Seq.index (reveal_h64s(as_seq h block_w)) (UInt32.v t))


#reset-options " --z3refresh --max_fuel 0 --z3rlimit 500"

[@"substitute"]
private val ws_part_1:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v block_word_length /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 200"

[@"substitute"]
let ws_part_1 ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    i <= 16 /\ live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\
    as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_block = reveal_h64s (as_seq h0 block_w) in
       let w = reveal_h64s (as_seq h1 ws_w) in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws seq_block j))
  in
  let f' (t:uint32_t {v t < 16}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    ws_part_1_core ws_w block_w t
  in
  (**) Lemmas.lemma_modifies_0_is_modifies_1 h0 ws_w;
  for 0ul 16ul inv f';
  (**) let h1 = ST.get() in ()


#reset-options " --z3refresh --max_fuel 0 --z3rlimit 20"

[@ Substitute]
private
val ws_part_2_core:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v block_word_length /\ disjoint ws_w block_w} ->
  i:UInt32.t{16 <= UInt32.v i /\ UInt32.v i < 80} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w /\
                  (let w = reveal_h64s (as_seq h ws_w) in
                  let b = reveal_h64s (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i ==> Seq.index w j == Spec.ws b j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  reveal_h64s (as_seq h1 block_w) == reveal_h64s (as_seq h0 block_w)
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i+1 ==> Seq.index w j == Spec.ws b j))))

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 100"

[@ Substitute]
let ws_part_2_core ws_w block_w t =
  (**) let h0 = ST.get () in
  let t16 = ws_w.(t -^ 16ul) in
  let t15 = ws_w.(t -^ 15ul) in
  let t7  = ws_w.(t -^ 7ul) in
  let t2  = ws_w.(t -^ 2ul) in
  ws_w.(t) <- H64.((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)));
  (**) let h1 = ST.get () in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
  (**) Lemmas.lemma_spec_ws_def2 (reveal_h64s (as_seq h0 block_w)) (UInt32.v t);
  (**) assert(Seq.index (reveal_h64s (as_seq h1 ws_w)) (UInt32.v t) == Spec.ws (reveal_h64s (as_seq h0 block_w)) (UInt32.v t))


#reset-options " --z3refresh --max_fuel 0 --z3rlimit 20"

[@"substitute"]
private val ws_part_2:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v block_word_length /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w
                  /\ (let w = reveal_h64s (as_seq h ws_w) in
                  let b = reveal_h64s (as_seq h block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --z3refresh --max_fuel 0 --z3rlimit 200"

[@"substitute"]
let ws_part_2 ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\ 16 <= i /\ i <= 80
    /\ reveal_h64s (as_seq h1 block_w) == reveal_h64s (as_seq h0 block_w)
    /\ (let seq_block = reveal_h64s (as_seq h0 block_w) in
       let w = reveal_h64s (as_seq h1 ws_w) in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws seq_block j))
  in
  let f' (t:uint32_t {16 <= v t /\ v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    ws_part_2_core ws_w block_w t
  in
  (**) Lemmas.lemma_modifies_0_is_modifies_1 h0 ws_w;
  for 16ul 80ul inv f';
  (**) let h1 = ST.get() in ()


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val ws:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v block_word_length /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
let ws ws_w block_w =
  ws_part_1 ws_w block_w;
  ws_part_2 ws_w block_w


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle_core:
  words_state :uint64_p {length words_state = v state_word_length} ->
  block_w:uint64_p {length block_w = v block_word_length} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w} ->
  k_w    :uint64_p {length k_w = v size_k_w} ->
  t      :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h words_state /\ live h ws_w /\ live h k_w /\ live h block_w /\
          reveal_h64s (as_seq h k_w) == Spec.k /\
          (let w = reveal_h64s (as_seq h ws_w) in
           let b = reveal_h64s (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h0 words_state /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
                  /\ live h1 words_state /\ modifies_1 words_state h0 h1
                  /\ (let seq_hash_0 = reveal_h64s (as_seq h0 words_state) in
                  let seq_hash_1 = reveal_h64s (as_seq h1 words_state) in
                  let seq_block = reveal_h64s (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle_core seq_block seq_hash_0 (U32.v t))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

[@"substitute"]
let shuffle_core hash block ws k t =
  let a = hash.(0ul) in
  let b = hash.(1ul) in
  let c = hash.(2ul) in
  let d = hash.(3ul) in
  let e = hash.(4ul) in
  let f = hash.(5ul) in
  let g = hash.(6ul) in
  let h = hash.(7ul) in

  (* Perform computations *)
  let k_t = k.(t) in
  let ws_t = ws.(t) in
  let t1 = H64.(h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ k_t +%^ ws_t) in
  let t2 = H64.((_Sigma0 a) +%^ (_Maj a b c)) in

  (* Store the new working hash in the state *)
  hupd64_8 hash H64.(t1 +%^ t2) a b c H64.(d +%^ t1) e f g


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle:
  words_state :uint64_p {length words_state = v state_word_length} ->
  block_w:uint64_p {length block_w = v block_word_length /\ disjoint block_w words_state} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w words_state} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w words_state} ->
  Stack unit
        (requires (fun h -> live h words_state /\ live h ws_w /\ live h k_w /\ live h block_w /\
          reveal_h64s (as_seq h k_w) == Spec.k /\
          (let w = reveal_h64s (as_seq h ws_w) in
           let b = reveal_h64s (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h1 words_state /\ modifies_1 words_state h0 h1 /\ live h0 block_w
                  /\ live h0 words_state
                  /\ (let seq_hash_0 = reveal_h64s (as_seq h0 words_state) in
                  let seq_hash_1 = reveal_h64s (as_seq h1 words_state) in
                  let seq_block = reveal_h64s (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle seq_hash_0 seq_block)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

[@"substitute"]
let shuffle hash block ws k =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 hash /\ modifies_1 hash h0 h1 /\ i <= v size_ws_w
    /\ (let seq_block = reveal_h64s (as_seq h0 block) in
    reveal_h64s (as_seq h1 hash) == repeat_range_spec 0 i (Spec.shuffle_core seq_block) (reveal_h64s (as_seq h0 hash)))
  in
  let f' (t:uint32_t {v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    shuffle_core hash block ws k t;
    (**) C.Compat.Loops.lemma_repeat_range_spec 0 (UInt32.v t + 1) (Spec.shuffle_core (reveal_h64s (as_seq h0 block))) (reveal_h64s (as_seq h0 hash))
  in
  (**) C.Compat.Loops.lemma_repeat_range_0 0 (Spec.shuffle_core (reveal_h64s (as_seq h0 block))) (reveal_h64s (as_seq h0 hash));
  for 0ul size_ws_w inv f'

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val sum_hash:
  hash_0:uint64_p{length hash_0 = v state_word_length} ->
  hash_1:uint64_p{length hash_1 = v state_word_length /\ disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1
              /\ (let new_seq_hash_0 = reveal_h64s (as_seq h1 hash_0) in
              let seq_hash_0 = reveal_h64s (as_seq h0 hash_0) in
              let seq_hash_1 = reveal_h64s (as_seq h0 hash_1) in
              let res        = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) seq_hash_0 seq_hash_1 in
              new_seq_hash_0 == res)))

[@"substitute"]
let sum_hash hash_0 hash_1 =
  (**) let h0 = ST.get() in
  C.Compat.Loops.in_place_map2 hash_0 hash_1 state_word_length (fun x y -> H64.(x +%^ y));
  (**) let h1 = ST.get() in
  (**) Seq.lemma_eq_intro (Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) (reveal_h64s (as_seq h0 hash_0))
                          (reveal_h64s (as_seq  h0 hash_1))) (reveal_h64s (as_seq h1 hash_0))


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint64_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == (HS.get_tip h1)
             /\ Map.domain (HS.get_hmap h1) == Map.domain (HS.get_hmap h0)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"c_inline"]
let alloc () = Buffer.create (u32_to_h64 0ul) size_state


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

val init:
  state:uint64_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h64s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H64.v counter = 0)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

let init state =
  let n = Buffer.sub state pos_count_w size_count_w in
  let k = Buffer.sub state pos_k_w size_k_w in
  let h_0 = Buffer.sub state pos_whash_w size_whash_w in
  constants_set_k k;
  constants_set_h_0 h_0;
  Buffer.upd n 0ul 0uL


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
private val copy_hash:
  hash_w_1 :uint64_p {length hash_w_1 = v state_word_length} ->
  hash_w_2 :uint64_p {length hash_w_2 = v state_word_length /\ disjoint hash_w_1 hash_w_2} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w_1 /\ live h0 hash_w_2))
        (ensures  (fun h0 _ h1 -> live h0 hash_w_1 /\ live h0 hash_w_2 /\ live h1 hash_w_1 /\ modifies_1 hash_w_1 h0 h1
                  /\ (as_seq h1 hash_w_1 == as_seq h0 hash_w_2)))

[@"substitute"]
let copy_hash hash_w_1 hash_w_2 =
  (**) let h0 = ST.get () in
  Buffer.blit hash_w_2 0ul hash_w_1 0ul state_word_length;
  (**) let h1 = ST.get () in
  (**) assert(Seq.slice (as_seq h1 hash_w_1) 0 (v state_word_length) == Seq.slice (as_seq h0 hash_w_2) 0 (v state_word_length));
  (**) Lemmas.lemma_blit_slices_eq h0 h1 hash_w_1 hash_w_2 (v state_word_length)


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val update_core:
  words_state :uint64_p {length words_state = v state_word_length} ->
  data   :uint8_p  {length data = v block_length /\ disjoint data words_state} ->
  data_w :uint64_p {length data_w = v block_word_length /\ disjoint data_w words_state} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w words_state} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w words_state} ->
  Stack unit
        (requires (fun h0 -> live h0 words_state /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w
                  /\ reveal_h64s (as_seq h0 k_w) == Spec.k
                  /\ (reveal_h64s (as_seq h0 data_w) = Spec.Lib.uint64s_from_be (v block_word_length) (reveal_sbytes (as_seq h0 data)))
                  /\ (let w = reveal_h64s (as_seq h0 ws_w) in
                  let b = reveal_h64s (as_seq h0 data_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 ->
                    live h0 words_state /\ live h0 data /\
                    live h0 data_w /\ live h1 words_state /\
                    modifies_1 words_state h0 h1 /\
                    (let seq_hash_0 = reveal_h64s (as_seq h0 words_state) in
                    let seq_hash_1 = reveal_h64s (as_seq h1 words_state) in
                    let seq_block = reveal_sbytes (as_seq h0 data) in
                    let res = Spec.update seq_hash_0 seq_block in
                    seq_hash_1 == res)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 400"

[@"substitute"]
let update_core words_state data data_w ws_w k_w =
  (**) assert_norm(pow2 32 = 0x100000000);
  (**) assert_norm(pow2 64 = 0x10000000000000000);
  (**) assert_norm(pow2 125 = 42535295865117307932921825928971026432);
  (**) let h0 = ST.get() in

  (* Push a new frame *)
  (**) push_frame();
  (**) let h1 = ST.get() in
  (**) assert(let b = Spec.words_of_bytes Spec.block_word_length (reveal_sbytes (as_seq h0 data)) in
              reveal_h64s (as_seq h0 data_w) == b);

  (* Allocate space for converting the data block *)
  let hash_0 = Buffer.create (u64_to_h64 0uL) state_word_length in
  (**) let h2 = ST.get() in
  assert (modifies_0 h1 h2);

  (* Keep track of the the current working hash from the state *)
  copy_hash hash_0 words_state;
  (**) let h3 = ST.get() in
  assert (modifies_1 hash_0 h2 h3);

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle hash_0 data_w ws_w k_w;
  (**) let h4 = ST.get() in
  assert (modifies_1 hash_0 h3 h4);
  lemma_modifies_1_trans hash_0 h2 h3 h4;
  assert (modifies_1 hash_0 h2 h4);
  (**) assert(let b = Spec.words_of_bytes Spec.block_word_length (reveal_sbytes (as_seq h0 data)) in
              let ha = Spec.shuffle (reveal_h64s (as_seq h0 words_state)) b in
              as_seq h4 words_state == as_seq h0 words_state /\
              reveal_h64s (as_seq h4 hash_0) == ha);

  (* Use the previous one to update it inplace *)
  sum_hash words_state hash_0;
  (**) let h5 = ST.get() in
  assert (modifies_1 words_state h4 h5);
  lemma_modifies_1_1 hash_0 words_state h2 h4 h5;
  assert (modifies_2 hash_0 words_state h2 h5);
  lemma_modifies_0_2' words_state hash_0 h1 h2 h5;
  assert (modifies_2_1 words_state h1 h5);
  (**) assert(let x = reveal_h64s (as_seq h4 words_state) in
          let y = reveal_h64s (as_seq h4 hash_0) in
          x == reveal_h64s (as_seq h0 words_state) /\
          y == Spec.shuffle (reveal_h64s (as_seq h0 words_state)) (Spec.words_of_bytes Spec.block_word_length (reveal_sbytes (as_seq h0 data))));
  (**) assert(let x = reveal_h64s (as_seq h0 words_state) in
         let y = Spec.shuffle (reveal_h64s (as_seq h0 words_state)) (Spec.words_of_bytes Spec.block_word_length (reveal_sbytes (as_seq h0 data))) in
         let z = reveal_h64s (as_seq h5 words_state) in
         let z' = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) x y in
         z == z');

  (* Pop the frame *)
  (**) pop_frame();
  let h6 = ST.get () in
  modifies_popped_1 words_state h0 h1 h5 h6


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val counter_increment:
  counter_w :uint64_p{length counter_w = v size_count_w} ->
  Stack unit
        (requires (fun h -> live h counter_w
                  /\ (let counter = Seq.index (as_seq h counter_w) 0 in
                  H64.v counter < (pow2 64 - 1))))
        (ensures  (fun h0 _ h1 -> live h1 counter_w /\ live h0 counter_w /\ modifies_1 counter_w h0 h1
                  /\ (let counter_0 = Seq.index (as_seq h0 counter_w) 0 in
                  let counter_1 = Seq.index (as_seq h1 counter_w) 0 in
                  H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
let counter_increment counter_w =
  let c0 = counter_w.(0ul) in
  let one = u32_to_h64 1ul in
  counter_w.(0ul) <- H64.(c0 +%^ one)


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 75"

val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v block_length /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 1))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_block = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64
                  /\ reveal_h64s seq_hash_1 == Spec.update (reveal_h64s seq_hash_0) (reveal_sbytes seq_block))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 250"

let update state data =

  (* Push a new frame *)
  (**) let h0 = ST.get () in
  (**) push_frame();
  (**) let h1 = ST.get () in
  (**) Lemmas.lemma_eq_state_k_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
  (**)                    (Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)));
  (**) Lemmas.lemma_eq_state_counter_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))
                          (Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)));
  (**) Lemmas.lemma_eq_state_hash_sub_slice h1 state;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
                          (Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)));

  (* Allocate space for converting the data block *)
  let data_w = Buffer.create (u32_to_h64 0ul) block_word_length in
  (**) let h2 = ST.get () in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_count_w size_count_w);

  (* Cast the data bytes into a uint32_t buffer *)
  uint64s_from_be_bytes data_w data block_word_length;
  (**) let h3 = ST.get () in
  (**) lemma_modifies_0_1' data_w h1 h2 h3;
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_count_w size_count_w);
  (**) no_upd_lemma_1 h2 h3 data_w data;
  (**) assert(reveal_h64s (as_seq h3 data_w) == Spec.Lib.uint64s_from_be (U32.v block_word_length) (reveal_sbytes (as_seq h3 data)));

  (* Retreive values from the state *)
  let words_state = Buffer.sub state pos_whash_w size_whash_w in
  let ws_w = Buffer.sub state pos_ws_w size_ws_w in
  let k_w = Buffer.sub state pos_k_w size_k_w in
  let counter_w = Buffer.sub state pos_count_w size_count_w in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws ws_w data_w;
  (**) let h4 = ST.get () in
  (**) modifies_subbuffer_1 h3 h4 ws_w state;
  (**) no_upd_lemma_1 h3 h4 ws_w data;
  (**) no_upd_lemma_1 h3 h4 ws_w k_w;
  (**) no_upd_lemma_1 h3 h4 ws_w words_state;
  (**) no_upd_lemma_1 h3 h4 ws_w counter_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  (**) assert(reveal_h64s (as_seq h4 k_w) == Spec.k);
  update_core words_state data data_w ws_w k_w;
  (**) let h5 = ST.get () in
  (**) modifies_subbuffer_1 h4 h5 words_state state;
  (**) lemma_modifies_1_trans state h3 h4 h5;
  (**) no_upd_lemma_1 h4 h5 words_state data;
  (**) no_upd_lemma_1 h4 h5 words_state k_w;
  (**) no_upd_lemma_1 h4 h5 words_state counter_w;
  (**) Lemmas.lemma_eq_state_k_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_counter_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_hash_sub_slice h5 state;
  (**) Seq.lemma_eq_intro (as_seq h1 words_state) (as_seq h4 words_state);
  (**) Seq.lemma_eq_intro (as_seq h1 data) (as_seq h4 data);
  (**) assert(reveal_h64s (as_seq h5 words_state) == Spec.update (reveal_h64s (as_seq h0 words_state)) (reveal_sbytes (as_seq h0 data)));

  (* Increment the total number of blocks processed *)
  counter_increment counter_w;
  (**) let h6 = ST.get () in
  (**) modifies_subbuffer_1 h5 h6 counter_w state;
  (**) lemma_modifies_1_trans state h3 h5 h6;
  (**) lemma_modifies_0_1 state h1 h3 h6;
  (**) no_upd_lemma_1 h5 h6 counter_w data;
  (**) no_upd_lemma_1 h5 h6 counter_w k_w;
  (**) no_upd_lemma_1 h5 h6 counter_w words_state;
  (**) Lemmas.lemma_eq_state_k_sub_slice h6 state;
  (**) Lemmas.lemma_eq_state_counter_sub_slice h6 state;
  (**) Lemmas.lemma_eq_state_hash_sub_slice h6 state;
  (**) assert(let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_k_1 = Seq.slice (as_seq h6 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              seq_k_0 == seq_k_1);
  (**) assert(let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h6 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  H64.v counter_1 = H64.v counter_0 + 1 /\ H64.v counter_1 < pow2 64);
  (**) assert(let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_block = as_seq h0 data in
                  reveal_h64s seq_hash_1 == Spec.update (reveal_h64s seq_hash_0) (reveal_sbytes seq_block));

  (* Pop the memory frame *)
  (**) pop_frame();
  (**) let h7 = ST.get () in
  (**) modifies_popped_1 state h0 h1 h6 h7;
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v block_length = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v block_length = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\ 
                 (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - (v n)))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1 /\
                 (let seq_hash0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter0 = Seq.index seq_counter0 0 in
                  let counter1 = Seq.index seq_counter1 0 in
                  seq_k0 == seq_k1 /\ 
                  H64.v counter1 = H64.v counter0 + v n /\
                  H64.v counter1 < pow2 64 /\
                  reveal_h64s seq_hash1 == 
                  Spec.update_multi (reveal_h64s seq_hash0) (reveal_sbytes seq_blocks) )))

let rec update_multi state data n =
  let h0 = ST.get () in

  let inv (h:HS.mem) (i:nat) : Type0 =
    live h state /\ live h data /\ modifies_1 state h0 h /\ 0 <= i /\ i <= v n /\ 
    (let hash0 = // Starting value
      Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
     let seq_counter0 = 
       Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
     let counter0 = Seq.index seq_counter0 0 in    
     let seq_hash = Seq.slice (as_seq h state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
     let seq_k = Seq.slice (as_seq h state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
     let seq_counter = Seq.slice (as_seq h state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
     let counter = Seq.index seq_counter 0 in
     let blocks = as_seq h (Buffer.sub data 0ul (U32.uint_to_t i *^ block_length)) in
     reveal_h64s seq_k == Spec.k /\ 
     H64.v counter < pow2 64 - v n + i /\
     H64.v counter = H64.v counter0 + i /\
     reveal_h64s seq_hash ==
     Spec.update_multi (reveal_h64s hash0) (reveal_sbytes blocks) )
  in
  let empty = Buffer.sub data 0ul (0ul *^ block_length) in
  Spec.lemma_update_multi_empty (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))) (reveal_sbytes (as_seq h0 empty));
  Lemmas.lemma_modifies_0_is_modifies_1 h0 state;

  let f (i:uint32_t{0 <= v i /\ v i < v n}) : Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures  (fun h0 _ h1 -> inv h0 (v i) /\ inv h1 (v i + 1)))
  = 
    let h = ST.get() in
    let blocks = Buffer.sub data 0ul (i *^ block_length) in
    let b      = Buffer.sub data (i *^ block_length) block_length in
    Spec.update_update_multi_append
      (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))))
      (reveal_sbytes (as_seq h blocks))
      (reveal_sbytes (as_seq h b));
    let blocks1 = Buffer.sub data 0ul ((i +^ 1ul) *^ block_length) in
    Seq.lemma_eq_intro (Seq.append (as_seq h blocks) (as_seq h b)) (as_seq h blocks1);
    lemma_disjoint_sub data b state;
    lemma_disjoint_sub data blocks state;
    lemma_disjoint_sub data blocks1 state;
    update state b
  in
  for 0ul n inv f


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

inline_for_extraction
val pad0_length: (len:uint32_t{v len + 1 + v len_length <= 2 * v block_length}) ->
  Tot (n:uint32_t{v n = Spec.pad0_length (v len)})
let pad0_length len =
  (block_length +^ block_length -^ (len +^ len_length +^ 1ul)) %^ block_length


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

inline_for_extraction
let encode_length (count:uint32_ht) (len:uint32_t{v count * v block_length + v len < Spec.max_input_len_8}) : Tot (l:uint128_ht{H128.v l = (v count * v block_length + v len) * 8}) =
  let l0 = H128.mul_wide (u32_to_h64 count) (u32_to_h64 block_length) in
  let l1 = u32_to_h128 len in
  (**) assert(H128.v l0 + H128.v l1 < pow2 125);
  (**) assert_norm(pow2 3 = 8);
  (**) Math.Lemmas.modulo_lemma Hacl.UInt128.(v (shift_left (l0 +^ l1) 3ul)) (pow2 128);
  H128.(H128.shift_left (l0 +^ l1) 3ul) // Multiplication by 2^3


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part1:
  buf1 :uint8_p {length buf1 = 1} ->
  Stack unit
        (requires (fun h0 -> live h0 buf1))
        (ensures  (fun h0 _ h1 -> live h0 buf1 /\ live h1 buf1 /\ modifies_1 buf1 h0 h1
                             /\ (let seq_buf1 = reveal_sbytes (as_seq h1 buf1) in
                             seq_buf1 = Seq.create 1 0x80uy)))

#reset-options "--z3refresh --max_fuel 0 --z3rlimit 100"

[@"substitute"]
let set_pad_part1 buf1 =
  Buffer.upd buf1 0ul (u8_to_h8 0x80uy);
  (**) let h = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h buf1)) (Seq.create 1 0x80uy)


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part2:
  buf2       :uint8_p{length buf2 = v len_length} ->
  encodedlen :uint128_ht ->
  Stack unit
        (requires (fun h0 -> live h0 buf2))
        (ensures  (fun h0 _ h1 -> live h0 buf2 /\ live h1 buf2 /\ modifies_1 buf2 h0 h1
                  /\ (let seq_buf2 = reveal_sbytes (as_seq h1 buf2) in
                  seq_buf2 == FStar.Old.Endianness.big_bytes len_length (H128.v encodedlen))))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 30"

[@"substitute"]
let set_pad_part2 buf2 encodedlen =
  Hacl.Endianness.hstore128_be buf2 encodedlen;
  (**) let h = ST.get () in
  (**) Lemmas.lemma_eq_endianness h buf2 encodedlen


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_downcast: (len:uint64_t) -> Lemma
  (requires (UInt64.v len + 1 + UInt32.v len_length <= 2 * UInt32.v block_length))
  (ensures ((UInt64.v len + 1 + UInt32.v len_length <= 2 * UInt32.v block_length) ==> (UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v len_length <= 2 * UInt32.v block_length) ))
let lemma_downcast len =
  (**) assert(UInt64.v len + 1 + UInt32.v len_length <= 2 * UInt32.v block_length);
  (**) assert(UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v len_length <= 2 * UInt32.v block_length)


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_padding_bounds:
  padding :uint8_p ->
  len     :uint32_t {U32.v len + 1 + v len_length <= 2 * v block_length
                     /\ length padding = (1 + v len_length + Spec.pad0_length (U32.v len))}
  -> Lemma
  (ensures (let p0 = pad0_length len in
    1 <= length padding
    /\ 1 + UInt32.v p0 <= length padding
    /\ 1 + UInt32.v p0 + UInt32.v len_length <= length padding))
let lemma_padding_bounds padding len = ()


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 100"

val lemma_eq_pad0_downcast: len:UInt64.t -> Lemma (ensures (Spec.pad0_length (UInt32.v (u64_to_u32 len)) = Spec.pad0_length (U64.v len)))
let lemma_eq_pad0_downcast len = ()


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
val pad:
  padding :uint8_p ->
  n       :uint32_ht ->
  len     :uint32_t {v len + 1 + v len_length <= 2 * v block_length
                     /\ v n * v block_length + v len < Spec.max_input_len_8
                     /\ length padding = (1 + v len_length + Spec.pad0_length (v len))
                     /\ (length padding + v len) % v block_length = 0} ->
  Stack unit
        (requires (fun h0 -> live h0 padding
                  /\ (let seq_padding = reveal_sbytes (as_seq h0 padding) in
                  seq_padding == Seq.create (1 + v len_length + Spec.pad0_length (v len)) 0uy)))
        (ensures  (fun h0 _ h1 -> live h0 padding /\ live h1 padding /\ modifies_1 padding h0 h1
                  /\ (let seq_padding = reveal_sbytes (as_seq h1 padding) in
                  seq_padding == Spec.pad (v n * v block_length) (v len))))

#reset-options "--z3refresh --max_fuel 0 --z3rlimit 500"

[@"substitute"]
let pad padding n len =

  (* Compute and encode the total length *)
  let encodedlen = encode_length n len in
  assert(H128.v encodedlen = ((v n * v block_length + v len) * 8));

  (* Get the memory *)
  (**) let h0 = ST.get () in

  (* Compute the length of zeros *)
  (**) assert(v len + 1 + v len_length <= 2 * v block_length);
//  (**) lemma_downcast len;
  (**) assert(v len + 1 + v len_length <= 2 * v block_length);
  let pad0len = pad0_length len in
  (**) assert(UInt32.v pad0len = Spec.pad0_length (v len));
//  (**) lemma_eq_pad0_downcast len;
  (**) assert(UInt32.v pad0len = Spec.pad0_length (v len));

  (* Retreive the different parts of the padding *)
  (**) assert(length padding = (1 + v len_length + Spec.pad0_length (v len)));
  (**) assert(1 <= length padding);
  let buf1 = Buffer.sub padding 0ul 1ul in
  (**) let h1 = ST.get () in
  (**) assert(length padding = (1 + v len_length + Spec.pad0_length (v len)));
//  (**) lemma_eq_pad0_downcast len;
  (**) assert(1 + UInt32.v pad0len <= length padding);
  let zeros = Buffer.sub padding 1ul pad0len in
  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(v (1ul +^ pad0len) + v len_length <= length padding);
  let buf2 = Buffer.sub padding (1ul +^ pad0len) len_length in

  (* Set the first byte of the padding *)
  set_pad_part1 buf1;
  (**) no_upd_lemma_1 h0 h1 buf1 zeros;
  (**) no_upd_lemma_1 h0 h1 buf1 buf2;

  (* Encode the total length at the end of the padding *)
  set_pad_part2 buf2 encodedlen;

  (* Proof that this is the concatenation of the three parts *)
  (**) let h3 = ST.get () in
  (**) Buffer.no_upd_lemma_2 h2 h3 buf1 buf2 zeros;
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h3 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 buf1) == Seq.create 1 0x80uy);
  (**) assert(reveal_sbytes (as_seq h3 buf2) == FStar.Old.Endianness.big_bytes len_length (H128.v encodedlen));
  (**) Lemmas.lemma_sub_append_3 h3 padding 0ul buf1 1ul zeros (1ul +^ pad0len) buf2 (1ul +^ pad0len +^ len_length);
  (**) Lemmas.lemma_pad_aux h3 (Cast.sint32_to_sint64 n) (Cast.sint32_to_sint64 len) buf1 zeros buf2


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 100"

val update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v len_length + 1) < 2 * v block_length} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U32.div len block_length in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = H64.((H64.v (Seq.index count 0)) * (U32.v block_length)) in
                  reveal_h64s seq_hash_1 == Spec.update_last (reveal_h64s seq_hash_0) prevlen seq_data)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 750"

let update_last state data len =
  (**) assert_norm(pow2 32 = 0x100000000);

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame();
  (**) let h00 = ST.get() in

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (block_length +^ block_length) in

  (**) let h0 = ST.get () in
 // (**) assert(reveal_sbytes (as_seq h0 blocks) == Seq.create (2 * v block_length) 0uy);

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length is public ! *)
  let nb = if (len <^ 112ul) then 1ul else 2ul in
  let final_blocks =
    (**) let h1 = ST.get () in
    if (len <^ 112ul) then begin
      (**) assert(v block_length <= length blocks);
      (**) assert(live h1 blocks);
      Buffer.offset blocks block_length end
    else begin
      (**) assert(live h1 blocks);
      blocks end in

  (**) assert(blocks `includes` final_blocks);

  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks))
                          (if (len <^ 112ul) then
                              Seq.create (v block_length) 0uy
                           else Seq.create (v block_length + v block_length) 0uy);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks)) (Seq.create (
                          v (if (len <^ 112ul) then 1ul else 2ul)  * v block_length) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 final_blocks) == Seq.create (v nb * v block_length) 0uy);

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
//  (**) assert(length final_blocks)
  Buffer.blit data 0ul final_blocks 0ul len;
  (**) let h3 = ST.get () in
  (**) modifies_subbuffer_1 h2 h3 final_blocks blocks;
  (**) lemma_modifies_0_1' blocks h00 h0 h3;
  (* (\**\) Seq.lemma_eq_intro (as_seq h3 data) (Seq.slice (as_seq h3 data) 0 len); *)
  (* (\**\) Seq.lemma_eq_intro (as_seq h3 data) (Seq.slice (as_seq h3 final_blocks) 0 (U64.v len)); *)
  (**) assert(as_seq h3 data == Seq.slice (as_seq h3 final_blocks) 0 (v len));

  (* Compute the final length of the data *)
  let n = state.(pos_count_w) in

  (* Set the padding *)
  let padding = Buffer.offset final_blocks len in
  (**) assert(v len + v len_length + 1 < 2 * v block_length);
  (**) assert(H64.v n * v block_length + v len < Spec.max_input_len_8);
  (**) assert(length padding = (1 + (Spec.pad0_length (v len)) + v len_length));
  (**) assert((length padding + v len) % v block_length = 0);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h3 padding)) (Seq.create (1 + (Spec.pad0_length (v len)) + v len_length) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 padding) == Seq.create (1 + (Spec.pad0_length (v len)) + v len_length) 0uy);
  pad padding (h64_to_h32 n) len;

  (* Proof that final_blocks = data @| padding *)
  (**) let h4 = ST.get () in
  (**) assert(blocks `includes` padding);
  (**) modifies_subbuffer_1 h3 h4 padding blocks;
  (**) lemma_modifies_0_1' blocks h00 h3 h4;
  (**) lemma_disjoint_sub blocks padding data;
  (**) assert(disjoint padding data);
  (**) no_upd_lemma_1 h3 h4 padding data;
  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.sub final_blocks 0ul len)) (Seq.slice (as_seq h4 final_blocks) 0 (v len));
  (**) no_upd_lemma_1 h3 h4 padding (Buffer.sub final_blocks 0ul len);
  (**) assert(reveal_sbytes (as_seq h4 data) == Seq.slice (reveal_sbytes (as_seq h4 final_blocks)) 0 (v len));

  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.offset final_blocks len)) (Seq.slice (as_seq h4 final_blocks) (v len) (v nb * v block_length));
  (**) Seq.lemma_eq_intro (as_seq h4 padding) (Seq.slice (as_seq h4 final_blocks) (v len) (v nb * v block_length));
  (**) assert(as_seq h4 padding == Seq.slice (as_seq h4 final_blocks) (v len) (v nb * v block_length));
  (**) Lemmas.lemma_sub_append_2 h4 final_blocks 0ul data len padding (nb *^ block_length);
  (**) assert(as_seq h4 final_blocks == Seq.append (as_seq h4 data) (as_seq h4 padding));

  (* Call the update function on one or two blocks *)
  (**) assert(length final_blocks % v block_length = 0 /\ disjoint state data);
  (**) assert(v nb * v block_length = length final_blocks);
  (**) assert(live h4 state /\ live h4 final_blocks);
  (**) assert(let seq_k = Seq.slice (as_seq h4 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_counter = Seq.slice (as_seq h4 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2));

  update_multi state final_blocks nb;
  (**) let h5 = ST.get() in
  (**) lemma_modifies_0_1 state h00 h4 h5;

  (* Pop the memory frame *)
  (**) pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 state hinit h00 h5 hfin;
  admit ()


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

[@"substitute"]
val finish_core:
  words_state :uint64_p {length words_state = v state_word_length} ->
  hash   :uint8_p  {length hash = v hash_length /\ disjoint words_state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 words_state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 words_state /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = reveal_h64s (as_seq h0 words_state) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.bytes_of_words (U32.v state_word_length) seq_hash_w)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 50"

[@"substitute"]
let finish_core words_state hash = uint64s_to_be_bytes hash words_state state_word_length


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v hash_length /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.finish (reveal_h64s seq_hash_w))))

let finish state hash =
  let words_state = Buffer.sub state pos_whash_w size_whash_w in
  finish_core words_state hash


#reset-options "--z3refresh --max_fuel 0  --z3rlimit 20"

val hash:
  hash :uint8_p {length hash = v hash_length} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = reveal_sbytes (as_seq h0 input) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

#reset-options "--z3refresh --max_fuel 0  --z3rlimit 200"

let hash hash input len =

  (**) let hinit = ST.get() in
  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get() in

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h64 0ul) size_state in
  (**) let h1 = ST.get() in

  (* Compute the number of blocks to process *)
  let n = U32.div len block_length in
  let r = U32.rem len block_length in

  (* Get all full blocks the last block *)
  let input_blocks = Buffer.sub input 0ul (n *%^ block_length) in
  let input_last = Buffer.sub input (n *%^ block_length) r in

  (* Initialize the hash function *)
  init state;
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' state h0 h1 h2;

  (* Update the state with input blocks *)
  update_multi state input_blocks n;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' state h0 h2 h3;

  (* Process the last block of input *)
  update_last state input_last r;
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1' state h0 h3 h4;

  (* Finalize the hash output *)
  finish state hash;
  (**) let h5 = ST.get() in
  (**) lemma_modifies_0_1 hash h0 h4 h5;

  (* Pop the memory frame *)
  (**) pop_frame ();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 hash hinit h0 h5 hfin
