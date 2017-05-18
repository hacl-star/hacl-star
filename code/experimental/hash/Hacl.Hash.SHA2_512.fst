module Hacl.Hash.SHA2_512

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open C.Loops

open Hacl.Cast
open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Utils.Experimental


(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H32 = Hacl.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

module HS = FStar.HyperStack
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_512
module Lemmas = Hacl.Hash.SHA2_512.Lemmas
module Utils = Hacl.Utils.Experimental


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
inline_for_extraction let  h64_to_h128 = Cast.sint64_to_sint128


#reset-options "--max_fuel 0  --z3rlimit 10"

//
// SHA-512
//

(* Define word size *)
inline_for_extraction let size_word = 8ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let size_hash_w   = 8ul // 8 words (Final hash output size)
inline_for_extraction let size_block_w  = 16ul  // 16 words (Working data block size)
inline_for_extraction let size_hash     = size_word *^ size_hash_w
inline_for_extraction let size_block    = size_word *^ size_block_w

(* Sizes of objects in the state *)
inline_for_extraction let size_k_w     = 80ul  // 80 words of 64 bits (size_block)
inline_for_extraction let size_ws_w    = size_k_w
inline_for_extraction let size_whash_w = size_hash_w
inline_for_extraction let size_count_w = 1ul  // 1 word
inline_for_extraction let size_len_8   = 2ul *^ size_word

inline_for_extraction let size_state   = size_k_w +^ size_ws_w +^ size_whash_w +^ size_count_w

(* Positions of objects in the state *)
inline_for_extraction let pos_k_w      = 0ul
inline_for_extraction let pos_ws_w     = size_k_w
inline_for_extraction let pos_whash_w  = size_k_w +^ size_ws_w
inline_for_extraction let pos_count_w  = size_k_w +^ size_ws_w +^ size_whash_w


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


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
private val constants_set_k:
  k:uint64_p{length k = v size_k_w} ->
  Stack unit
        (requires (fun h -> live h k))
        (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1
                 /\ (let seq_k = Hacl.Spec.Endianness.reveal_h64s (as_seq h1 k) in
                   seq_k == Spec.k)))

[@"substitute"]
let constants_set_k k =
  Hacl.Utils.Experimental.hupd64_80 k
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


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
val constants_set_h_0:
  hash:uint64_p{length hash = v size_hash_w} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1
             /\ (let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s (as_seq h1 hash) in
                seq_h_0 == Spec.h_0)))

[@"substitute"]
let constants_set_h_0 hash =
  Hacl.Utils.Experimental.hupd64_8 hash
  0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
  0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
private val ws_part_1:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w 
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = as_seq h1 ws_w in
                  let b = as_seq h0 block_w in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --max_fuel 0 --z3rlimit 20"

[@"substitute"]
let ws_part_1 ws_w block_w =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    i <= 16 /\ live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\
    as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_ws = as_seq h0 ws_w in
       let seq_block = as_seq h0 block_w in
       let w = as_seq h1 ws_w in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws seq_block j))
  in
  let f' (t:uint32_t {v t < 16}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    let h = ST.get() in
    ws_w.(t) <- block_w.(t);
    let h' = ST.get() in
    assume(Seq.index (as_seq h' block_w) (UInt32.v t) == Spec.ws (as_seq h0 block_w) (UInt32.v t));
    assume(
      let w = as_seq h' ws_w in
      let b = as_seq h0 block_w in
      forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v t + 1 ==> Seq.index w j == Spec.ws b j);
    no_upd_lemma_1 h h' ws_w block_w;
    assert(as_seq h' block_w == as_seq h block_w)
  in
  assume(modifies_1 ws_w h0 h0);
  for 0ul 16ul inv f';
  let h1 = ST.get() in
  ()


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
private val ws_part_2:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = as_seq h1 ws_w in
                  let b = as_seq h0 block_w in
                  (forall (i:nat). {:pattern (Seq.index w i)} 16 < i /\ i < 80 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --max_fuel 0 --z3rlimit 100"

[@"substitute"]
let ws_part_2 ws_w block_w =
  let h0 = ST.get() in  
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\ 16 < i /\ i <= 80
    /\ as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_block = as_seq h0 block_w in
       let w = as_seq h1 ws_w in
    (forall (j:nat). {:pattern (Seq.index w j)} j < i ==> Seq.index w j == Spec.ws seq_block j))
  in  
  let f' (t:uint32_t {16 < v t /\ v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    let h = ST.get () in
    let t16 = ws_w.(t -^ 16ul) in
    let t15 = ws_w.(t -^ 15ul) in
    let t7  = ws_w.(t -^ 7ul) in
    let t2  = ws_w.(t -^ 2ul) in
    ws_w.(t) <- H64.((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)));
    let h' = ST.get () in
//    no_upd_lemma_1 h h' ws_w block_w;
    assume(as_seq h' block_w == as_seq h block_w);
    assume(Seq.index (as_seq h' ws_w) (UInt32.v t) == Spec.ws (as_seq h0 block_w) (UInt32.v t));
    assume(
      let w = as_seq h' ws_w in
      let b = as_seq h0 block_w in
      forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v t + 1 ==> Seq.index w j == Spec.ws b j)
  in admit();
  assume(modifies_1 ws_w h0 h0);
  for 16ul 80ul inv f';
  let h1 = ST.get() in ()


[@"substitute"]
private val ws:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w 
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = as_seq h1 ws_w in
                  let b = as_seq h0 block_w in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))

[@"substitute"]
let ws ws_w block_w =
  ws_part_1 ws_w block_w;
  ws_part_2 ws_w block_w


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"substitute"]
private val shuffle_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w} ->
  k_w    :uint64_p {length k_w = v size_k_w} ->
  t      :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          as_seq h k_w == Spec.k /\
          (let w = as_seq h ws_w in
           let b = as_seq h block_w in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
          /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = as_seq h0 hash_w in
                  let seq_hash_1 = as_seq h1 hash_w in
                  let seq_block = as_seq h0 block_w in
                  seq_hash_1 == Spec.shuffle_core seq_block seq_hash_0 (U32.v t))))

#reset-options "--max_fuel 0  --z3rlimit 50"

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
  let k_t = k.(t) in // Introduce these variables
  let ws_t = ws.(t) in
  let t1 = H64.(h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ k_t +%^ ws_t) in
  let t2 = H64.((_Sigma0 a) +%^ (_Maj a b c)) in

  (* Store the new working hash in the state *)
  Utils.hupd64_8 hash H64.(t1 +%^ t2) a b c H64.(d +%^ t1) e f g


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"substitute"]
private val shuffle:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w /\ disjoint block_w hash_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          as_seq h k_w == Spec.k /\
          (let w = as_seq h ws_w in
           let b = as_seq h block_w in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h1 hash_w /\ modifies_1 hash_w h0 h1 /\ live h0 block_w
                  /\ live h0 hash_w
                  /\ (let seq_hash_0 = as_seq h0 hash_w in
                  let seq_hash_1 = as_seq h1 hash_w in
                  let seq_block = as_seq h0 block_w in
                  seq_hash_1 == Spec.shuffle seq_hash_0 seq_block)))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let shuffle hash block ws k =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 hash /\ modifies_1 hash h0 h1 /\ i <= v size_ws_w
    /\ (let seq_block = as_seq h0 block in
    as_seq h1 hash == repeat_range_spec 0 i (Spec.shuffle_core seq_block) (as_seq h0 hash))
  in
  let f' (t:uint32_t {v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    shuffle_core hash block ws k t;
    C.Loops.lemma_repeat_range_spec 0 (UInt32.v t + 1) (Spec.shuffle_core (as_seq h0 block)) (as_seq h0 hash)
  in
  C.Loops.lemma_repeat_range_0 0 0 (Spec.shuffle_core (as_seq h0 block)) (as_seq h0 hash);
  for 0ul size_ws_w inv f'


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val sum_hash:
  hash_0:uint64_p{length hash_0 = v size_hash_w} ->
  hash_1:uint64_p{length hash_1 = v size_hash_w /\ disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1
              /\ (let new_seq_hash_0 = as_seq h1 hash_0 in
              let seq_hash_0 = as_seq h0 hash_0 in
              let seq_hash_1 = as_seq h0 hash_1 in
              let res        = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) seq_hash_0 seq_hash_1 in
              new_seq_hash_0 == res)))

[@"substitute"]
let sum_hash hash_0 hash_1 =
  let h0 = ST.get() in
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> H64.(x +%^ y));
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) (as_seq h0 hash_0) (as_seq  h0 hash_1)) (as_seq h1 hash_0)



#reset-options "--max_fuel 0  --z3rlimit 10"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint64_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

[@"c_inline"]
let alloc () = Buffer.create (u32_to_h64 0ul) size_state


#reset-options "--max_fuel 0  --z3rlimit 20"

val init:
  state:uint64_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H64.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h64s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h64s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H64.v counter = 0)))

#reset-options "--max_fuel 0  --z3rlimit 50"

let init state =
  (**) let h0 = ST.get () in
  let n = Buffer.sub state pos_count_w size_count_w in
  let k = Buffer.sub state pos_k_w size_k_w in
  let h_0 = Buffer.sub state pos_whash_w size_whash_w in
  constants_set_k k;
  constants_set_h_0 h_0;
  (**) let h1 = ST.get () in
  (**) no_upd_lemma_2 h0 h1 k h_0 n


[@"substitute"]
private val copy_hash:
  hash_w_1 :uint64_p {length hash_w_1 = v size_hash_w} ->
  hash_w_2 :uint64_p {length hash_w_2 = v size_hash_w /\ disjoint hash_w_1 hash_w_2} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w_1 /\ live h0 hash_w_2))
        (ensures  (fun h0 _ h1 -> live h0 hash_w_1 /\ live h0 hash_w_2 /\ live h1 hash_w_1 /\ modifies_1 hash_w_1 h0 h1
                  /\ (as_seq h1 hash_w_1 == as_seq h0 hash_w_2)))

[@"substitute"]
let copy_hash hash_w_1 hash_w_2 =
  let h0 = ST.get () in
  Buffer.blit hash_w_2 0ul hash_w_1 0ul size_hash_w;
  let h1 = ST.get () in
  assert(Seq.slice (as_seq h1 hash_w_1) 0 (v size_hash_w) == Seq.slice (as_seq h0 hash_w_2) 0 (v size_hash_w));
  Lemmas.lemma_blit_slices_eq h0 h1 hash_w_1 hash_w_2 (v size_hash_w)


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"substitute"]
private val update_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  data   :uint8_p  {length data = v size_block /\ disjoint data hash_w} ->
  data_w :uint64_p {length data_w = v size_block_w /\ disjoint data_w hash_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w
                  /\ as_seq h0 k_w == Spec.k
                  /\ (as_seq h0 data_w = Spec.Lib.uint64s_from_be (v size_block_w) (as_seq h0 data))
                  /\ (let w = as_seq h0 ws_w in
                  let b = as_seq h0 data_w in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = as_seq h0 hash_w in
                  let seq_hash_1 = as_seq h1 hash_w in
                  let seq_block = as_seq h0 data in
                  let res = Spec.update seq_hash_0 seq_block in
                  seq_hash_1 == res)))

#reset-options "--max_fuel 0  --z3rlimit 400"

[@"substitute"]
let update_core hash_w data data_w ws_w k_w =
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 125 = 42535295865117307932921825928971026432);

  let h0 = ST.get() in

  (* Push a new frame *)
  (**) push_frame();

  let h1 = ST.get() in

  assert(  let b = Spec.words_from_be Spec.size_block_w (as_seq h0 data) in
           as_seq h0 data_w == b);

  (* Allocate space for converting the data block *)
  let hash_0 = Buffer.create (u64_to_h64 0uL) size_hash_w in

  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 data;
  no_upd_lemma_0 h1 h2 data_w;
  no_upd_lemma_0 h1 h2 ws_w;
  no_upd_lemma_0 h1 h2 k_w;
  no_upd_lemma_0 h1 h2 hash_w;

  (* Keep track of the the current working hash from the state *)
  copy_hash hash_0 hash_w;

  let h3 = ST.get() in

  no_upd_lemma_1 h2 h3 hash_0 data;
  no_upd_lemma_1 h2 h3 hash_0 data_w;
  no_upd_lemma_1 h2 h3 hash_0 ws_w;
  no_upd_lemma_1 h2 h3 hash_0 k_w;
  no_upd_lemma_1 h2 h3 hash_0 hash_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle hash_0 data_w ws_w k_w;

  let h4 = ST.get() in
  assert(let b = Spec.words_from_be Spec.size_block_w (as_seq h0 data) in
         let ha = Spec.shuffle (as_seq h0 hash_w) b in
         as_seq h4 hash_w == as_seq h0 hash_w /\
         as_seq h4 hash_0 == ha);

  no_upd_lemma_1 h3 h4 hash_0 data;
  no_upd_lemma_1 h3 h4 hash_0 data_w;
  no_upd_lemma_1 h3 h4 hash_0 ws_w;
  no_upd_lemma_1 h3 h4 hash_0 k_w;
  no_upd_lemma_1 h3 h4 hash_0 hash_w;

  (* Use the previous one to update it inplace *)
  sum_hash hash_w hash_0;

  let h5 = ST.get() in

   assert(let x = as_seq h4 hash_w in
          let y = as_seq h4 hash_0 in
          x == as_seq h0 hash_w /\
          y == Spec.shuffle (as_seq h0 hash_w) (Spec.words_from_be Spec.size_block_w (as_seq h0 data)));

  assert(let x = as_seq h0 hash_w in
         let y = Spec.shuffle (as_seq h0 hash_w) (Spec.words_from_be Spec.size_block_w (as_seq h0 data)) in
         let z = as_seq h5 hash_w in
         let z' = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) x y in
         z == z');

  no_upd_lemma_1 h4 h5 hash_w data;
  no_upd_lemma_1 h4 h5 hash_w data_w;
  no_upd_lemma_1 h4 h5 hash_w ws_w;
  no_upd_lemma_1 h4 h5 hash_w k_w;

  (* Pop the frame *)
  (**) pop_frame()


#reset-options "--max_fuel 0  --z3rlimit 50"

val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  seq_k == Spec.k /\ H64.v counter < (pow2 64 - 1))))
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
                  /\ seq_hash_1 == Spec.update seq_hash_0 seq_block)))

#reset-options "--max_fuel 0  --z3rlimit 200"

let update state data =

  (* Push a new frame *)
  (**) push_frame();

  (* Allocate space for converting the data block *)
  let data_w = Buffer.create (u32_to_h64 0ul) size_block_w in

  (* Cast the data bytes into a uint32_t buffer *)
  Hacl.Utils.Experimental.load64s_be data_w data size_block;

  (* Retreive values from the state *)
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  let ws_w = Buffer.sub state pos_ws_w size_ws_w in
  let k_w = Buffer.sub state pos_k_w size_k_w in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws ws_w data_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  update_core hash_w data data_w ws_w k_w;

  (* Increment the total number of blocks processed *)
  let state_len = Buffer.sub state (pos_count_w) 1ul in
  let c0 = state_len.(0ul) in
  let one = u32_to_h64 1ul in
  state_len.(0ul) <- H64.(c0 +%^ one);

  (* Pop the memory frame *)
  (**) pop_frame()


#reset-options "--max_fuel 0  --z3rlimit 100"

val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  seq_k == Spec.k /\ H64.v counter < (pow2 64 - (v n)))))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_k_0 = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_k_1 = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_blocks = as_seq h0 data in
                  let seq_counter_0 = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let seq_counter_1 = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter_0 = Seq.index seq_counter_0 0 in
                  let counter_1 = Seq.index seq_counter_1 0 in
                  seq_k_0 == seq_k_1
                  /\ H64.v counter_1 = H64.v counter_0 + (v n) /\ H64.v counter_1 < pow2 64
                  /\ seq_hash_1 == Spec.update_multi seq_hash_0 seq_blocks)))

#reset-options "--max_fuel 0  --z3rlimit 200"

let rec update_multi state data n =
  let h0 = ST.get() in
  if n =^ 0ul then (
    assert (v n = 0);
    Lemmas.lemma_aux_1 (v n) (v size_block);
    assert (length data = 0);
    Lemmas.lemma_modifies_0_is_modifies_1 h0 state;
    Lemmas.lemma_update_multi_def (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))) (as_seq h0 data)
  )
  else
    begin
    assert(v n > 0);
    Lemmas.lemma_aux_2 (v n) (v size_block);
    assert(length data > 0);
    Lemmas.lemma_update_multi_def (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))) (as_seq h0 data);

    (* Get the current block for the data *)
    let b = Buffer.sub data 0ul size_block in

    (* Remove the current block from the data left to process *)
    let data = Buffer.offset data size_block in
    assert(disjoint b data);

    (* Call the update function on the current block *)
    update state b;

    (* Recursive call *)
    update_multi state data (n -^ 1ul) end


#reset-options "--max_fuel 0  --z3rlimit 50"

inline_for_extraction
let pad0_length (len:uint32_t{v len + 1 + v size_len_8 < pow2 32}) : Tot (n:uint32_t{v n = Spec.pad0_length (v len)}) =
  size_block -^ ((len +^ size_len_8 +^ 1ul) %^ size_block)


#reset-options "--max_fuel 0  --z3rlimit 50"

inline_for_extraction
let encode_length (count:uint64_ht) (len:uint64_t{H64.v count * v size_block + U64.v len < Spec.max_input_len_8}) : Tot (l:uint128_ht{H128.v l = (H64.v count * v size_block + U64.v len) * 8}) =
  let l0 = H128.mul_wide count (u32_to_h64 size_block) in
  let l1 = u64_to_h128 len in
  assert(H128.v l0 + H128.v l1 < pow2 125);
  assert_norm(pow2 3 = 8);
  Math.Lemmas.modulo_lemma Hacl.UInt128.(v (shift_left (l0 +^ l1) 3ul)) (pow2 128);
  H128.(H128.shift_left (l0 +^ l1) 3ul) // Multiplication by 2^3; Call modulo_lemma


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"substitute"]
val set_pad_part1:
  buf1 :uint8_p {length buf1 = 1} ->
  Stack unit
        (requires (fun h0 -> live h0 buf1))
        (ensures  (fun h0 _ h1 -> live h0 buf1 /\ live h1 buf1 /\ modifies_1 buf1 h0 h1
                             /\ (let seq_buf1 = as_seq h1 buf1 in
                             seq_buf1 = Seq.create 1 0x80uy)))

#reset-options "--max_fuel 0 --z3rlimit 50"

[@"substitute"]
let set_pad_part1 buf1 =
  Buffer.upd buf1 0ul (u8_to_h8 0x80uy);
  let h = ST.get () in
  Seq.lemma_eq_intro (as_seq h buf1) (Seq.create 1 0x80uy)


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part2:
  buf2       :uint8_p{length buf2 = v size_len_8} ->
  encodedlen :uint128_ht ->
  Stack unit
        (requires (fun h0 -> live h0 buf2))
        (ensures  (fun h0 _ h1 -> live h0 buf2 /\ live h1 buf2 /\ modifies_1 buf2 h0 h1
                  /\ (let seq_buf2 = as_seq h1 buf2 in
                  seq_buf2 == Endianness.big_bytes size_len_8 (H128.v encodedlen))))

#reset-options "--max_fuel 0  --z3rlimit 30"

[@"substitute"]
let set_pad_part2 buf2 encodedlen =
  Hacl.Endianness.hstore128_be buf2 encodedlen;
  let h = ST.get () in
  Lemmas.lemma_eq_endianness h buf2 encodedlen


#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
val pad:
  padding :uint8_p ->
  n       :uint64_ht ->
  len     :uint64_t {(U64.v len + v size_len_8 + 1) < (2 * v size_block)
                     /\ H64.v n * v size_block + U64.v len < Spec.max_input_len_8
                     /\ length padding = (1 + Spec.pad0_length (U64.v len)) + v size_len_8
                     /\ (length padding + U64.v len) % v size_block = 0} ->
  Stack unit
        (requires (fun h0 -> live h0 padding
                  /\ (let seq_padding = as_seq h0 padding in
                  seq_padding == Seq.create (1 + Spec.pad0_length (U64.v len) + v size_len_8) 0uy )))
        (ensures  (fun h0 _ h1 -> live h0 padding /\ live h1 padding /\ modifies_1 padding h0 h1
                  /\ (let seq_padding = as_seq h1 padding in
                  seq_padding == Spec.pad (H64.v n * v size_block) (U64.v len))))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let pad padding n len =

  (* Compute the length of zeros *)
  let pad0len = pad0_length (u64_to_u32 len) in

  (* Retreive the different parts of the padding *)
  let buf1 = Buffer.sub padding 0ul 1ul in
  let zeros = Buffer.sub padding 1ul pad0len in
  let buf2 = Buffer.sub padding (1ul +^ pad0len) size_len_8 in

  (* Compute and encode the total length *)
  let encodedlen = encode_length n len in

  (**) let h0 = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h0 zeros) (Seq.create (v pad0len) 0uy);
  (**) assert(as_seq h0 zeros == Seq.create (v pad0len) 0uy);

  (* Set the first byte of the padding *)
  set_pad_part1 buf1;

  (* Encode the total length at the end of the padding *)
  set_pad_part2 buf2 encodedlen;

  (* Proof that this is the concatenation of the three parts *)
  let h1 = ST.get () in
  Buffer.no_upd_lemma_2 h0 h1 buf1 buf2 zeros;
  Seq.lemma_eq_intro (as_seq h1 zeros) (Seq.create (v pad0len) 0uy);
  assert(as_seq h1 zeros == Seq.create (v pad0len) 0uy);
  assert(as_seq h1 buf1 == Seq.create 1 0x80uy);
  assert(as_seq h1 buf2 == Endianness.big_bytes size_len_8 (H128.v encodedlen));
  Lemmas.lemma_sub_append_3 h1 padding 0ul buf1 1ul zeros (1ul +^ pad0len) buf2 (1ul +^ pad0len +^ size_len_8);
  Lemmas.lemma_pad_aux h1 n len buf1 zeros buf2


#reset-options "--max_fuel 0  --z3rlimit 50"

val update_last:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint64_t {U64.v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U64.div len (u32_to_u64 size_block) in
                  seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = as_seq h0 data in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U64.(v (Seq.index count 0) * (U32.v size_block)) in
                  seq_hash_1 == Spec.update_last seq_hash_0 prevlen seq_data)))

#reset-options "--max_fuel 0  --z3rlimit 200"

let update_last state data len =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ size_block) in

  (**) let h0 = ST.get () in
  (**) assert(as_seq h0 blocks == Seq.create (2 * v size_block) 0uy);

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length are considered public here ! *)
  let (nb, final_blocks) =
    if U64.(len <^ 112uL) then (1ul, Buffer.offset blocks size_block)
    else (2ul, blocks)
  in

  (**) let h1 = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h1 final_blocks)
                          (if U64.(len <^ 112uL) then
                              Seq.create (v size_block) 0uy
                           else Seq.create (2 * v size_block) 0uy);
  (**) Seq.lemma_eq_intro (as_seq h1 final_blocks) (Seq.create (v nb * v size_block) 0uy);
  (**) assert(as_seq h1 final_blocks == Seq.create (v nb * v size_block) 0uy);

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
  Buffer.blit data 0ul final_blocks 0ul (u64_to_u32 len);

  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h2 data) 0 (U64.v len));
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h2 final_blocks) 0 (U64.v len));
  (**) assert(as_seq h2 data == Seq.slice (as_seq h2 final_blocks) 0 (U64.v len));

  (* Compute the final length of the data *)
  let n = state.(pos_count_w) in

  (* Set the padding *)
  let padding = Buffer.offset final_blocks (u64_to_u32 len) in
  (**) assert(U64.v len + v size_len_8 + 1 < 2 * v size_block);
  (**) assert(H64.v n * v size_block + U64.v len < Spec.max_input_len_8);
  (**) assert(length padding = (1 + (Spec.pad0_length (U64.v len)) + v size_len_8));
  (**) assert((length padding + U64.v len) % v size_block = 0);
  (**) Seq.lemma_eq_intro (as_seq h1 padding) (Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  (**) assert(as_seq h2 padding == Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  pad padding n len;

  (* Proof that final_blocks = data @| padding *)
  (**) let h3 = ST.get () in
  (**) assert(disjoint padding data);
  (**) no_upd_lemma_1 h2 h3 padding data;
  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.sub final_blocks 0ul (u64_to_u32 len))) (Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));
  (**) no_upd_lemma_1 h2 h3 padding (Buffer.sub final_blocks 0ul (u64_to_u32 len));
  (**) assert(as_seq h3 data == Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));

  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.offset final_blocks (u64_to_u32 len))) (Seq.slice (as_seq h3 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Seq.lemma_eq_intro (as_seq h3 padding) (Seq.slice (as_seq h3 final_blocks) (U64.v len) (v nb * v size_block));
  (**) assert(as_seq h3 padding == Seq.slice (as_seq h3 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Lemmas.lemma_sub_append_2 h3 final_blocks 0ul data (u64_to_u32 len) padding (nb *^ size_block);
  (**) assert(as_seq h3 final_blocks == Seq.append (as_seq h3 data) (as_seq h3 padding));

  (* Call the update function on one or two blocks *)
  (**) assert(length final_blocks % v size_block = 0 /\ disjoint state data);
  (**) assert(v nb * v size_block = length final_blocks);
  (**) assert(live h3 state /\ live h3 final_blocks);
  (**) assert(let seq_k = Seq.slice (as_seq h3 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_counter = Seq.slice (as_seq h3 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2));

  update_multi state final_blocks nb;

  (* Pop the memory frame *)
  (**) pop_frame()


#reset-options "--max_fuel 0  --z3rlimit 10"

[@"substitute"]
val finish_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  hash   :uint8_p  {length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 hash_w /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = as_seq h0 hash_w in
                  let seq_hash = as_seq h1 hash in
                  seq_hash = Spec.words_to_be (U32.v size_hash_w) seq_hash_w)))

[@"substitute"]
let finish_core hash_w hash = store64s_be hash hash_w size_hash_w


#reset-options "--max_fuel 0  --z3rlimit 10"

val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = as_seq h1 hash in
                  seq_hash = Spec.finish seq_hash_w)))

let finish state hash =
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  finish_core hash_w hash


#reset-options "--max_fuel 0  --z3rlimit 10"

val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = as_seq h0 input in
                  let seq_hash = as_seq h1 hash in
                  seq_hash == Spec.hash seq_input)))

#reset-options "--max_fuel 0  --z3rlimit 50"

let hash hash input len =

  (* Push a new memory frame *)
  (**) push_frame ();

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h64 0ul) size_state in

  (* Compute the number of blocks to process *)
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks the last block *)
  let input_blocks = Buffer.sub input 0ul (n *%^ size_block) in
  let input_last = Buffer.sub input (n *%^ size_block) r in

  (* Initialize the hash function *)
  init state;

  (* Update the state with input blocks *)
  update_multi state input_blocks n;

  (* Process the last block of input *)
  update_last state input_last (u32_to_u64 r);

  (* Finalize the hash output *)
  finish state hash;

  (* Pop the memory frame *)
  (**) pop_frame ()
