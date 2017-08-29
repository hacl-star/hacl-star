module Hacl.Hash.SHA2_384

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open C.Loops

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

module HS = FStar.HyperStack
module Cast = Hacl.Cast

module Spec = Spec.SHA2_384
module Lemmas = Hacl.Hash.SHA2_384.Lemmas


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
// SHA-384
//

(* Define word size *)
inline_for_extraction let size_word = 8ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let size_hash_w   = 8ul // 8 words (Intermediate hash output size)
inline_for_extraction let size_block_w  = 16ul  // 16 words (Working data block size)
inline_for_extraction let size_hash     = size_word *^ size_hash_w
inline_for_extraction let size_block    = size_word *^ size_block_w
inline_for_extraction let size_hash_final_w = 6ul // 6 words (Final hash output size)
inline_for_extraction let size_hash_final   = size_word *^ size_hash_final_w


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
let constants_set_k k = hupd64_80 k
  (u64_to_h64 0x428a2f98d728ae22uL) (u64_to_h64 0x7137449123ef65cduL)
  (u64_to_h64 0xb5c0fbcfec4d3b2fuL) (u64_to_h64 0xe9b5dba58189dbbcuL)
  (u64_to_h64 0x3956c25bf348b538uL) (u64_to_h64 0x59f111f1b605d019uL)
  (u64_to_h64 0x923f82a4af194f9buL) (u64_to_h64 0xab1c5ed5da6d8118uL)
  (u64_to_h64 0xd807aa98a3030242uL) (u64_to_h64 0x12835b0145706fbeuL)
  (u64_to_h64 0x243185be4ee4b28cuL) (u64_to_h64 0x550c7dc3d5ffb4e2uL)
  (u64_to_h64 0x72be5d74f27b896fuL) (u64_to_h64 0x80deb1fe3b1696b1uL)
  (u64_to_h64 0x9bdc06a725c71235uL) (u64_to_h64 0xc19bf174cf692694uL)
  (u64_to_h64 0xe49b69c19ef14ad2uL) (u64_to_h64 0xefbe4786384f25e3uL)
  (u64_to_h64 0x0fc19dc68b8cd5b5uL) (u64_to_h64 0x240ca1cc77ac9c65uL)
  (u64_to_h64 0x2de92c6f592b0275uL) (u64_to_h64 0x4a7484aa6ea6e483uL)
  (u64_to_h64 0x5cb0a9dcbd41fbd4uL) (u64_to_h64 0x76f988da831153b5uL)
  (u64_to_h64 0x983e5152ee66dfabuL) (u64_to_h64 0xa831c66d2db43210uL)
  (u64_to_h64 0xb00327c898fb213fuL) (u64_to_h64 0xbf597fc7beef0ee4uL)
  (u64_to_h64 0xc6e00bf33da88fc2uL) (u64_to_h64 0xd5a79147930aa725uL)
  (u64_to_h64 0x06ca6351e003826fuL) (u64_to_h64 0x142929670a0e6e70uL)
  (u64_to_h64 0x27b70a8546d22ffcuL) (u64_to_h64 0x2e1b21385c26c926uL)
  (u64_to_h64 0x4d2c6dfc5ac42aeduL) (u64_to_h64 0x53380d139d95b3dfuL)
  (u64_to_h64 0x650a73548baf63deuL) (u64_to_h64 0x766a0abb3c77b2a8uL)
  (u64_to_h64 0x81c2c92e47edaee6uL) (u64_to_h64 0x92722c851482353buL)
  (u64_to_h64 0xa2bfe8a14cf10364uL) (u64_to_h64 0xa81a664bbc423001uL)
  (u64_to_h64 0xc24b8b70d0f89791uL) (u64_to_h64 0xc76c51a30654be30uL)
  (u64_to_h64 0xd192e819d6ef5218uL) (u64_to_h64 0xd69906245565a910uL)
  (u64_to_h64 0xf40e35855771202auL) (u64_to_h64 0x106aa07032bbd1b8uL)
  (u64_to_h64 0x19a4c116b8d2d0c8uL) (u64_to_h64 0x1e376c085141ab53uL)
  (u64_to_h64 0x2748774cdf8eeb99uL) (u64_to_h64 0x34b0bcb5e19b48a8uL)
  (u64_to_h64 0x391c0cb3c5c95a63uL) (u64_to_h64 0x4ed8aa4ae3418acbuL)
  (u64_to_h64 0x5b9cca4f7763e373uL) (u64_to_h64 0x682e6ff3d6b2b8a3uL)
  (u64_to_h64 0x748f82ee5defb2fcuL) (u64_to_h64 0x78a5636f43172f60uL)
  (u64_to_h64 0x84c87814a1f0ab72uL) (u64_to_h64 0x8cc702081a6439ecuL)
  (u64_to_h64 0x90befffa23631e28uL) (u64_to_h64 0xa4506cebde82bde9uL)
  (u64_to_h64 0xbef9a3f7b2c67915uL) (u64_to_h64 0xc67178f2e372532buL)
  (u64_to_h64 0xca273eceea26619cuL) (u64_to_h64 0xd186b8c721c0c207uL)
  (u64_to_h64 0xeada7dd6cde0eb1euL) (u64_to_h64 0xf57d4f7fee6ed178uL)
  (u64_to_h64 0x06f067aa72176fbauL) (u64_to_h64 0x0a637dc5a2c898a6uL)
  (u64_to_h64 0x113f9804bef90daeuL) (u64_to_h64 0x1b710b35131c471buL)
  (u64_to_h64 0x28db77f523047d84uL) (u64_to_h64 0x32caab7b40c72493uL)
  (u64_to_h64 0x3c9ebe0a15c9bebcuL) (u64_to_h64 0x431d67c49c100d4cuL)
  (u64_to_h64 0x4cc5d4becb3e42b6uL) (u64_to_h64 0x597f299cfc657e2auL)
  (u64_to_h64 0x5fcb6fab3ad6faecuL) (u64_to_h64 0x6c44198c4a475817uL)

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
let constants_set_h_0 hash = hupd64_8 hash
  (u64_to_h64 0xcbbb9d5dc1059ed8uL) (u64_to_h64 0x629a292a367cd507uL)
  (u64_to_h64 0x9159015a3070dd17uL) (u64_to_h64 0x152fecd8f70e5939uL)
  (u64_to_h64 0x67332667ffc00b31uL) (u64_to_h64 0x8eb44a8768581511uL)
  (u64_to_h64 0xdb0c2e0d64f98fa7uL) (u64_to_h64 0x47b5481dbefa4fa4uL)


#reset-options " --max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val ws_part_1_core:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
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

#reset-options " --max_fuel 0 --z3rlimit 100"

[@ "substitute"]
let ws_part_1_core ws_w block_w t =
  (**) let h0 = ST.get() in
  (**) let h = ST.get() in
  ws_w.(t) <- block_w.(t);
  (**) let h1 = ST.get() in
  (**) let h' = ST.get() in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
  (**) Lemmas.lemma_spec_ws_def (reveal_h64s (as_seq h block_w)) (UInt32.v t);
  (**) assert(Seq.index (reveal_h64s (as_seq h1 ws_w)) (UInt32.v t) == Seq.index (reveal_h64s(as_seq h block_w)) (UInt32.v t))


#reset-options " --max_fuel 0 --z3rlimit 500"

[@"substitute"]
private val ws_part_1:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --max_fuel 0 --z3rlimit 200"

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


#reset-options " --max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val ws_part_2_core:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
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

#reset-options " --max_fuel 0 --z3rlimit 100"

[@ "substitute"]
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


#reset-options " --max_fuel 0 --z3rlimit 20"

[@"substitute"]
private val ws_part_2:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
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

#reset-options " --max_fuel 0 --z3rlimit 200"

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


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val ws:
  ws_w    :uint64_p {length ws_w = v size_ws_w} ->
  block_w :uint64_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h64s (as_seq h1 ws_w) in
                  let b = reveal_h64s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
let ws ws_w block_w =
  ws_part_1 ws_w block_w;
  ws_part_2 ws_w block_w


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w} ->
  k_w    :uint64_p {length k_w = v size_k_w} ->
  t      :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          reveal_h64s (as_seq h k_w) == Spec.k /\
          (let w = reveal_h64s (as_seq h ws_w) in
           let b = reveal_h64s (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
          /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = reveal_h64s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h64s (as_seq h1 hash_w) in
                  let seq_block = reveal_h64s (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle_core seq_block seq_hash_0 (U32.v t))))

#reset-options "--max_fuel 0  --z3rlimit 100"

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
  hupd64_8 hash H64.(t1 +%^ t2) a b c H64.(d +%^ t1) e f g


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  block_w:uint64_p {length block_w = v size_block_w /\ disjoint block_w hash_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          reveal_h64s (as_seq h k_w) == Spec.k /\
          (let w = reveal_h64s (as_seq h ws_w) in
           let b = reveal_h64s (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h1 hash_w /\ modifies_1 hash_w h0 h1 /\ live h0 block_w
                  /\ live h0 hash_w
                  /\ (let seq_hash_0 = reveal_h64s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h64s (as_seq h1 hash_w) in
                  let seq_block = reveal_h64s (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle seq_hash_0 seq_block)))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let shuffle hash block ws k =
  let h0 = ST.get() in
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
    C.Loops.lemma_repeat_range_spec 0 (UInt32.v t + 1) (Spec.shuffle_core (reveal_h64s (as_seq h0 block))) (reveal_h64s (as_seq h0 hash))
  in
  C.Loops.lemma_repeat_range_0 0 0 (Spec.shuffle_core (reveal_h64s (as_seq h0 block))) (reveal_h64s (as_seq h0 hash));
  for 0ul size_ws_w inv f'


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val sum_hash:
  hash_0:uint64_p{length hash_0 = v size_hash_w} ->
  hash_1:uint64_p{length hash_1 = v size_hash_w /\ disjoint hash_0 hash_1} ->
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
  let h0 = ST.get() in
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> H64.(x +%^ y));
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) (reveal_h64s (as_seq h0 hash_0)) (reveal_h64s (as_seq  h0 hash_1))) (reveal_h64s (as_seq h1 hash_0))



#reset-options "--max_fuel 0  --z3rlimit 20"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint64_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> ~(contains h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"c_inline"]
let alloc () = Buffer.create (u32_to_h64 0ul) size_state


#reset-options "--max_fuel 0  --z3rlimit 50"

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


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val update_core:
  hash_w :uint64_p {length hash_w = v size_hash_w} ->
  data   :uint8_p  {length data = v size_block /\ disjoint data hash_w} ->
  data_w :uint64_p {length data_w = v size_block_w /\ disjoint data_w hash_w} ->
  ws_w   :uint64_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint64_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w
                  /\ reveal_h64s (as_seq h0 k_w) == Spec.k
                  /\ (reveal_h64s (as_seq h0 data_w) = Spec.Lib.uint64s_from_be (v size_block_w) (reveal_sbytes (as_seq h0 data)))
                  /\ (let w = reveal_h64s (as_seq h0 ws_w) in
                  let b = reveal_h64s (as_seq h0 data_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 80 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = reveal_h64s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h64s (as_seq h1 hash_w) in
                  let seq_block = reveal_sbytes (as_seq h0 data) in
                  let res = Spec.update seq_hash_0 seq_block in
                  seq_hash_1 == res)))

#reset-options "--max_fuel 0  --z3rlimit 500"

[@"substitute"]
let update_core hash_w data data_w ws_w k_w =
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 125 = 42535295865117307932921825928971026432);

  let h0 = ST.get() in

  (* Push a new frame *)
  (**) push_frame();

  let h1 = ST.get() in

  assert(  let b = Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
           reveal_h64s (as_seq h0 data_w) == b);

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
  
  lemma_modifies_0_1' hash_0 h1 h2 h3;
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
  assert(let b = Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
         let ha = Spec.shuffle (reveal_h64s (as_seq h0 hash_w)) b in
         as_seq h4 hash_w == as_seq h0 hash_w /\
         reveal_h64s (as_seq h4 hash_0) == ha);

  lemma_modifies_0_1' hash_0 h1 h3 h4;
  no_upd_lemma_1 h3 h4 hash_0 data;
  no_upd_lemma_1 h3 h4 hash_0 data_w;
  no_upd_lemma_1 h3 h4 hash_0 ws_w;
  no_upd_lemma_1 h3 h4 hash_0 k_w;
  no_upd_lemma_1 h3 h4 hash_0 hash_w;

  (* Use the previous one to update it inplace *)
  sum_hash hash_w hash_0;

  let h5 = ST.get() in

  assert(let x = reveal_h64s (as_seq h4 hash_w) in
          let y = reveal_h64s (as_seq h4 hash_0) in
          x == reveal_h64s (as_seq h0 hash_w) /\
          y == Spec.shuffle (reveal_h64s (as_seq h0 hash_w)) (Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data))));

  assert(let x = reveal_h64s (as_seq h0 hash_w) in
         let y = Spec.shuffle (reveal_h64s (as_seq h0 hash_w)) (Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data))) in
         let z = reveal_h64s (as_seq h5 hash_w) in
         let z' = Spec.Loops.seq_map2 (fun x y -> FStar.UInt64.(x +%^ y)) x y in
         z == z');

  lemma_modifies_0_1 hash_w h1 h4 h5;
  no_upd_lemma_1 h4 h5 hash_w data;
  no_upd_lemma_1 h4 h5 hash_w data_w;
  no_upd_lemma_1 h4 h5 hash_w ws_w;
  no_upd_lemma_1 h4 h5 hash_w k_w;

  (* Pop the frame *)
  (**) pop_frame();
  let h6 = ST.get() in
  modifies_popped_1 hash_w h0 h1 h5 h6

#reset-options "--max_fuel 0  --z3rlimit 20"

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

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
let counter_increment counter_w =
  let c0 = counter_w.(0ul) in
  let one = u32_to_h64 1ul in
  counter_w.(0ul) <- H64.(c0 +%^ one)


#reset-options "--max_fuel 0  --z3rlimit 75"

val update:
  state :uint64_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
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

#reset-options "--max_fuel 0  --z3rlimit 250"

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
  let data_w = Buffer.create (u32_to_h64 0ul) size_block_w in
  (**) let h2 = ST.get () in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_count_w size_count_w);

  (* Cast the data bytes into a uint32_t buffer *)
  uint64s_from_be_bytes data_w data size_block_w;
  (**) let h3 = ST.get () in
  (**) lemma_modifies_0_1' data_w h1 h2 h3;
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_count_w size_count_w);
  (**) no_upd_lemma_1 h2 h3 data_w data;
  (**) assert(reveal_h64s (as_seq h3 data_w) == Spec.Lib.uint64s_from_be (U32.v size_block_w) (reveal_sbytes (as_seq h3 data)));

  (* Retreive values from the state *)
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  let ws_w = Buffer.sub state pos_ws_w size_ws_w in
  let k_w = Buffer.sub state pos_k_w size_k_w in
  let counter_w = Buffer.sub state pos_count_w size_count_w in

  (* Step 1 : Scheduling function for sixty-four 32 bit words *)
  ws ws_w data_w;
  (**) let h4 = ST.get () in
  (**) modifies_subbuffer_1 h3 h4 ws_w state;
  (**) no_upd_lemma_1 h3 h4 ws_w data;
  (**) no_upd_lemma_1 h3 h4 ws_w k_w;
  (**) no_upd_lemma_1 h3 h4 ws_w hash_w;
  (**) no_upd_lemma_1 h3 h4 ws_w counter_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  (**) assert(reveal_h64s (as_seq h4 k_w) == Spec.k);
  update_core hash_w data data_w ws_w k_w;
  (**) let h5 = ST.get () in
  (**) modifies_subbuffer_1 h4 h5 hash_w state;
  (**) lemma_modifies_1_trans state h3 h4 h5;
  (**) no_upd_lemma_1 h4 h5 hash_w data;
  (**) no_upd_lemma_1 h4 h5 hash_w k_w;
  (**) no_upd_lemma_1 h4 h5 hash_w counter_w;
  (**) Lemmas.lemma_eq_state_k_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_counter_sub_slice h5 state;
  (**) Lemmas.lemma_eq_state_hash_sub_slice h5 state;
  (**) Seq.lemma_eq_intro (as_seq h1 hash_w) (as_seq h4 hash_w);
  (**) Seq.lemma_eq_intro (as_seq h1 data) (as_seq h4 data);
  (**) assert(reveal_h64s (as_seq h5 hash_w) == Spec.update (reveal_h64s (as_seq h0 hash_w)) (reveal_sbytes (as_seq h0 data)));

  (* Increment the total number of blocks processed *)
  counter_increment counter_w;
  (**) let h6 = ST.get () in
  (**) modifies_subbuffer_1 h5 h6 counter_w state;
  (**) lemma_modifies_1_trans state h3 h5 h6;
  (**) lemma_modifies_0_1 state h1 h3 h6;
  (**) no_upd_lemma_1 h5 h6 counter_w data;
  (**) no_upd_lemma_1 h5 h6 counter_w k_w;
  (**) no_upd_lemma_1 h5 h6 counter_w hash_w;
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
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
                          (Seq.slice (as_seq h7 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)));
  (**) modifies_popped_1 state h0 h1 h6 h7


#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

val update_multi:
  state :uint64_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < pow2 64 - (v n))))
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
                  H64.v counter1 = H64.v counter0 + (v n) /\
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
     let blocks = as_seq h (Buffer.sub data 0ul (U32.uint_to_t i *^ size_block)) in
     reveal_h64s seq_k == Spec.k /\
     H64.v counter < pow2 64 - v n + i /\
     H64.v counter = H64.v counter0 + i /\
     reveal_h64s seq_hash ==
     Spec.update_multi (reveal_h64s hash0) (reveal_sbytes blocks) )
  in
  let empty = Buffer.sub data 0ul (0ul *^ size_block) in
  Spec.update_multi_empty (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))) (reveal_sbytes (as_seq h0 empty));
  Lemmas.lemma_modifies_0_is_modifies_1 h0 state;

  let f (i:uint32_t{0 <= v i /\ v i < v n}) : Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures  (fun h0 _ h1 -> inv h0 (v i) /\ inv h1 (v i + 1)))
  =
    let h = ST.get() in
    let blocks = Buffer.sub data 0ul (i *^ size_block) in
    let b      = Buffer.sub data (i *^ size_block) size_block in
    Spec.update_update_multi_append
      (reveal_h64s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))))
      (reveal_sbytes (as_seq h blocks))
      (reveal_sbytes (as_seq h b));
    let blocks1 = Buffer.sub data 0ul ((i +^ 1ul) *^ size_block) in
    Seq.lemma_eq_intro (Seq.append (as_seq h blocks) (as_seq h b)) (as_seq h blocks1);
    lemma_disjoint_sub data b state;
    lemma_disjoint_sub data blocks state;
    lemma_disjoint_sub data blocks1 state;
    update state b
  in
  for 0ul n inv f


#reset-options "--max_fuel 0  --z3rlimit 50"

inline_for_extraction
let pad0_length (len:uint32_t{v len + 1 + v size_len_8 < pow2 32}) : Tot (n:uint32_t{v n = Spec.pad0_length (v len)}) =
  (size_block -^ (len +^ size_len_8 +^ 1ul) %^ size_block) %^ size_block


#reset-options "--max_fuel 0  --z3rlimit 50"

inline_for_extraction
let encode_length (count:uint64_ht) (len:uint64_t{H64.v count * v size_block + U64.v len < Spec.max_input_len_8}) : Tot (l:uint128_ht{H128.v l = (H64.v count * v size_block + U64.v len) * 8}) =
  let l0 = H128.mul_wide count (u32_to_h64 size_block) in
  let l1 = u64_to_h128 len in
  assert(H128.v l0 + H128.v l1 < pow2 125);
  assert_norm(pow2 3 = 8);
  Math.Lemmas.modulo_lemma Hacl.UInt128.(v (shift_left (l0 +^ l1) 3ul)) (pow2 128);
  H128.(H128.shift_left (l0 +^ l1) 3ul) // Multiplication by 2^3; Call modulo_lemma


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part1:
  buf1 :uint8_p {length buf1 = 1} ->
  Stack unit
        (requires (fun h0 -> live h0 buf1))
        (ensures  (fun h0 _ h1 -> live h0 buf1 /\ live h1 buf1 /\ modifies_1 buf1 h0 h1
                             /\ (let seq_buf1 = reveal_sbytes (as_seq h1 buf1) in
                             seq_buf1 = Seq.create 1 0x80uy)))

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"substitute"]
let set_pad_part1 buf1 =
  Buffer.upd buf1 0ul (u8_to_h8 0x80uy);
  let h = ST.get () in
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h buf1)) (Seq.create 1 0x80uy)


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part2:
  buf2       :uint8_p{length buf2 = v size_len_8} ->
  encodedlen :uint128_ht ->
  Stack unit
        (requires (fun h0 -> live h0 buf2))
        (ensures  (fun h0 _ h1 -> live h0 buf2 /\ live h1 buf2 /\ modifies_1 buf2 h0 h1
                  /\ (let seq_buf2 = reveal_sbytes (as_seq h1 buf2) in
                  seq_buf2 == Endianness.big_bytes size_len_8 (H128.v encodedlen))))

#reset-options "--max_fuel 0  --z3rlimit 30"

[@"substitute"]
let set_pad_part2 buf2 encodedlen =
  Hacl.Endianness.hstore128_be buf2 encodedlen;
  let h = ST.get () in
  Lemmas.lemma_eq_endianness h buf2 encodedlen

#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_downcast: (len:uint64_t) -> Lemma
  (requires (UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block))
  (ensures ((UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block) ==> (UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block) ))
let lemma_downcast len =
  (**) assert(UInt64.v len + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block);
  (**) assert(UInt32.v (Int.Cast.uint64_to_uint32 len) + 1 + UInt32.v size_len_8 <= 2 * UInt32.v size_block)


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 50"

val lemma_padding_bounds:
  padding :uint8_p ->
  len     :uint32_t {U32.v len + 1 + v size_len_8 <= 2 * v size_block
                     /\ length padding = (1 + v size_len_8 + Spec.pad0_length (U32.v len))}
  -> Lemma
  (ensures (let p0 = pad0_length len in
    1 <= length padding
    /\ 1 + UInt32.v p0 <= length padding
    /\ 1 + UInt32.v p0 + UInt32.v size_len_8 <= length padding))
let lemma_padding_bounds padding len = ()


#reset-options "--z3refresh --max_fuel 0 --z3rlimit 100"

val lemma_eq_pad0_downcast: len:UInt64.t -> Lemma (ensures (Spec.pad0_length (UInt32.v (u64_to_u32 len)) = Spec.pad0_length (U64.v len)))
let lemma_eq_pad0_downcast len = ()


#reset-options "--max_fuel 0  --z3rlimit 100"

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
                  /\ (let seq_padding = reveal_sbytes (as_seq h0 padding) in
                  seq_padding == Seq.create (1 + Spec.pad0_length (U64.v len) + v size_len_8) 0uy )))
        (ensures  (fun h0 _ h1 -> live h0 padding /\ live h1 padding /\ modifies_1 padding h0 h1
                  /\ (let seq_padding = reveal_sbytes (as_seq h1 padding) in
                  seq_padding == Spec.pad (H64.v n * v size_block) (U64.v len))))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let pad padding n len =


  (* Compute and encode the total length *)
  let encodedlen = encode_length n len in
  assert(H128.v encodedlen = ((H64.v n * v size_block + U64.v len) * 8));

  (* Get the memory *)
  (**) let h0 = ST.get () in

  (* Compute the length of zeros *)
  (**) assert(U64.v len + 1 + v size_len_8 <= 2 * v size_block);
  (**) lemma_downcast len;
  (**) assert(U32.v (u64_to_u32 len) + 1 + v size_len_8 <= 2 * v size_block);
  let pad0len = pad0_length (u64_to_u32 len) in
  (**) assert(UInt32.v pad0len = Spec.pad0_length (UInt32.v (u64_to_u32 len)));
  (**) lemma_eq_pad0_downcast len;
  (**) assert(UInt32.v pad0len = Spec.pad0_length (UInt64.v len));

  (* Retreive the different parts of the padding *)
  (**) assert(length padding = (1 + v size_len_8 + Spec.pad0_length (U64.v len)));
  (**) assert(1 <= length padding);
  let buf1 = Buffer.sub padding 0ul 1ul in
  (**) let h1 = ST.get () in
  (**) assert(length padding = (1 + v size_len_8 + Spec.pad0_length (U64.v len)));
  (**) lemma_eq_pad0_downcast len;
  (**) assert(1 + UInt32.v pad0len <= length padding);
  let zeros = Buffer.sub padding 1ul pad0len in
  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(v (1ul +^ pad0len) + v size_len_8 <= length padding);
  let buf2 = Buffer.sub padding (1ul +^ pad0len) size_len_8 in

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
  (**) assert(reveal_sbytes (as_seq h3 buf2) == Endianness.big_bytes size_len_8 (H128.v encodedlen));
  (**) Lemmas.lemma_sub_append_3 h3 padding 0ul buf1 1ul zeros (1ul +^ pad0len) buf2 (1ul +^ pad0len +^ size_len_8);
  (**) Lemmas.lemma_pad_aux h3 n len buf1 zeros buf2


#reset-options "--max_fuel 0  --z3rlimit 100"

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
                  reveal_h64s seq_k == Spec.k /\ H64.v counter < (pow2 64 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = H64.((H64.v (Seq.index count 0)) * (U32.v size_block)) in
                  reveal_h64s seq_hash_1 == Spec.update_last (reveal_h64s seq_hash_0) prevlen seq_data)))

#reset-options "--max_fuel 0  --z3rlimit 200"

let update_last state data len =
  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame();
  (**) let h00 = ST.get() in

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ size_block) in

  (**) let h0 = ST.get () in
  // (**) assert(reveal_sbytes (as_seq h0 blocks) == Seq.create (2 * v size_block) 0uy);

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length is public ! *)
  let nb = if U64.(len <^ 112uL) then 1ul else 2ul in
  let final_blocks =
    (**) let h1 = ST.get () in
    if U64.(len <^ 112uL) then begin
      (**) assert(v size_block <= length blocks);
      (**) assert(live h1 blocks);
      Buffer.offset blocks size_block end
    else begin
      (**) assert(live h1 blocks);
      blocks end in

  (**) assert(blocks `includes` final_blocks);

  (**) let h2 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks))
                          (if U64.(len <^ 112uL) then
                              Seq.create (v size_block) 0uy
                           else Seq.create (2 * v size_block) 0uy);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 final_blocks)) (Seq.create (v nb * v size_block) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 final_blocks) == Seq.create (v nb * v size_block) 0uy);

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
  Buffer.blit data 0ul final_blocks 0ul (u64_to_u32 len);
  (**) let h3 = ST.get () in
  (**) modifies_subbuffer_1 h2 h3 final_blocks blocks;
  (**) lemma_modifies_0_1' blocks h00 h0 h3;
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h3 data) 0 (U64.v len));
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));
  (**) assert(as_seq h3 data == Seq.slice (as_seq h3 final_blocks) 0 (U64.v len));

  (* Compute the final length of the data *)
  let n = state.(pos_count_w) in

  (* Set the padding *)
  let padding = Buffer.offset final_blocks (u64_to_u32 len) in
  (**) assert(U64.v len + v size_len_8 + 1 < 2 * v size_block);
  (**) assert(H64.v n * v size_block + U64.v len < Spec.max_input_len_8);
  (**) assert(length padding = (1 + (Spec.pad0_length (U64.v len)) + v size_len_8));
  (**) assert((length padding + U64.v len) % v size_block = 0);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h3 padding)) (Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  (**) assert(reveal_sbytes (as_seq h3 padding) == Seq.create (1 + (Spec.pad0_length (U64.v len)) + v size_len_8) 0uy);
  pad padding n len;

  (* Proof that final_blocks = data @| padding *)
  (**) let h4 = ST.get () in
  (**) assert(blocks `includes` padding);
  (**) modifies_subbuffer_1 h3 h4 padding blocks;
  (**) lemma_modifies_0_1' blocks h00 h3 h4;
  (**) lemma_disjoint_sub blocks padding data;
  (**) assert(disjoint padding data);
  (**) no_upd_lemma_1 h3 h4 padding data;
  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.sub final_blocks 0ul (u64_to_u32 len))) (Seq.slice (as_seq h4 final_blocks) 0 (U64.v len));
  (**) no_upd_lemma_1 h3 h4 padding (Buffer.sub final_blocks 0ul (u64_to_u32 len));
  (**) assert(reveal_sbytes (as_seq h4 data) == Seq.slice (reveal_sbytes (as_seq h4 final_blocks)) 0 (U64.v len));

  (**) Seq.lemma_eq_intro (as_seq h4 (Buffer.offset final_blocks (u64_to_u32 len))) (Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Seq.lemma_eq_intro (as_seq h4 padding) (Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) assert(as_seq h4 padding == Seq.slice (as_seq h4 final_blocks) (U64.v len) (v nb * v size_block));
  (**) Lemmas.lemma_sub_append_2 h4 final_blocks 0ul data (u64_to_u32 len) padding (nb *^ size_block);
  (**) assert(as_seq h4 final_blocks == Seq.append (as_seq h4 data) (as_seq h4 padding));

  (* Call the update function on one or two blocks *)
  (**) assert(length final_blocks % v size_block = 0 /\ disjoint state data);
  (**) assert(v nb * v size_block = length final_blocks);
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
  (**) modifies_popped_1 state hinit h00 h5 hfin

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val finish_core:
  hash_w :uint64_p {length hash_w = v size_hash_final_w} ->
  hash   :uint8_p  {length hash = v size_hash_final /\ disjoint hash_w hash} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 hash_w /\ live h0 hash_w
                  /\ live h1 hash /\ live h0 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = reveal_h64s (as_seq h0 hash_w) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.words_to_be (U32.v size_hash_final_w) seq_hash_w)))

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
let finish_core hash_w hash = uint64s_to_be_bytes hash hash_w size_hash_final_w


#reset-options "--max_fuel 0  --z3rlimit 20"

val finish:
  state :uint64_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash_final /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h1 state /\ live h0 state
                  /\ live h1 hash /\ live h0 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.finish (reveal_h64s seq_hash_w))))

#reset-options "--max_fuel 0  --z3rlimit 100"

let finish state hash =
  let hash_w = Buffer.sub state pos_whash_w size_hash_final_w in
  (**) let h0 = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h0 (Buffer.sub state pos_whash_w size_hash_final_w))
                          ((Seq.slice (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))) 0 (v size_hash_final_w)));
  finish_core hash_w hash


#reset-options "--max_fuel 0  --z3rlimit 20"

val hash:
  hash :uint8_p {length hash = v size_hash_final} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = reveal_sbytes (as_seq h0 input) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

#reset-options "--max_fuel 0  --z3rlimit 200"

let hash hash input len =

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get() in

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h64 0ul) size_state in
  (**) let h1 = ST.get() in

  (* Compute the number of blocks to process *)
  let n = U32.div len size_block in
  let r = U32.rem len size_block in

  (* Get all full blocks the last block *)
  let input_blocks = Buffer.sub input 0ul (n *%^ size_block) in
  let input_last = Buffer.sub input (n *%^ size_block) r in

  (* Initialize the hash function *)
  init state;
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' state h0 h1 h2;

  (* Update the state with input blocks *)
  update_multi state input_blocks n;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' state h0 h2 h3;

  (* Process the last block of input *)
  update_last state input_last (u32_to_u64 r);
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
