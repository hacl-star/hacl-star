module Hacl.Hash.SHA2_256

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

module HS = FStar.HyperStack
module Cast = Hacl.Cast

module Spec = Spec.SHA2_256
module Lemmas = Hacl.Hash.SHA2_256.Lemmas


(* Definition of base types *)
private let uint8_t   = FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t
private let uint64_t  = FStar.UInt64.t

private let uint8_ht  = Hacl.UInt8.t
private let uint32_ht = Hacl.UInt32.t
private let uint64_ht = Hacl.UInt64.t

private let uint32_p = Buffer.buffer uint32_ht
private let uint8_p  = Buffer.buffer uint8_ht


(* Definitions of aliases for functions *)
inline_for_extraction let u8_to_h8 = Cast.uint8_to_sint8
inline_for_extraction let u32_to_h32 = Cast.uint32_to_sint32
inline_for_extraction let u32_to_h64 = Cast.uint32_to_sint64
inline_for_extraction let h32_to_h8  = Cast.sint32_to_sint8
inline_for_extraction let h32_to_h64 = Cast.sint32_to_sint64
inline_for_extraction let u64_to_h64 = Cast.uint64_to_sint64


#reset-options "--max_fuel 0  --z3rlimit 10"

//
// SHA-256
//

(* Define word size *)
inline_for_extraction let size_word = 4ul // Size of the word in bytes

(* Define algorithm parameters *)
inline_for_extraction let size_hash_w   = 8ul // 8 words (Final hash output size)
inline_for_extraction let size_block_w  = 16ul  // 16 words (Working data block size)
inline_for_extraction let size_hash     = size_word *^ size_hash_w
inline_for_extraction let size_block    = size_word *^ size_block_w
inline_for_extraction let max_input_len = 2305843009213693952uL // 2^61 Bytes

(* Sizes of objects in the state *)
inline_for_extraction let size_k_w     = 64ul  // 2048 bits = 64 words of 32 bits (size_block)
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
let rotate_right (a:uint32_ht) (b:uint32_t{0 < v b && v b < 32}) : Tot uint32_ht =
  H32.logor (H32.shift_right a b) (H32.shift_left a (U32.sub 32ul b))

[@"substitute"]
private val _Ch: x:uint32_ht -> y:uint32_ht -> z:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _Ch x y z = H32.logxor (H32.logand x y) (H32.logand (H32.lognot x) z)

[@"substitute"]
private val _Maj: x:uint32_ht -> y:uint32_ht -> z:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _Maj x y z = H32.logxor (H32.logand x y) (H32.logxor (H32.logand x z) (H32.logand y z))

[@"substitute"]
private val _Sigma0: x:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _Sigma0 x = H32.logxor (rotate_right x 2ul) (H32.logxor (rotate_right x 13ul) (rotate_right x 22ul))

[@"substitute"]
private val _Sigma1: x:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _Sigma1 x = H32.logxor (rotate_right x 6ul) (H32.logxor (rotate_right x 11ul) (rotate_right x 25ul))

[@"substitute"]
private val _sigma0: x:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _sigma0 x = H32.logxor (rotate_right x 7ul) (H32.logxor (rotate_right x 18ul) (H32.shift_right x 3ul))

[@"substitute"]
private val _sigma1: x:uint32_ht -> Tot uint32_ht
[@"substitute"]
let _sigma1 x = H32.logxor (rotate_right x 17ul) (H32.logxor (rotate_right x 19ul) (H32.shift_right x 10ul))


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
private val constants_set_k:
  k:uint32_p{length k = v size_k_w} ->
  Stack unit
        (requires (fun h -> live h k))
        (ensures (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1
                 /\ (let seq_k = Hacl.Spec.Endianness.reveal_h32s (as_seq h1 k) in
                   seq_k == Spec.k)))

[@"substitute"]
let constants_set_k k = hupd_64 k
  (u32_to_h32 0x428a2f98ul) (u32_to_h32 0x71374491ul) (u32_to_h32 0xb5c0fbcful) (u32_to_h32 0xe9b5dba5ul)
  (u32_to_h32 0x3956c25bul) (u32_to_h32 0x59f111f1ul) (u32_to_h32 0x923f82a4ul) (u32_to_h32 0xab1c5ed5ul)
  (u32_to_h32 0xd807aa98ul) (u32_to_h32 0x12835b01ul) (u32_to_h32 0x243185beul) (u32_to_h32 0x550c7dc3ul)
  (u32_to_h32 0x72be5d74ul) (u32_to_h32 0x80deb1feul) (u32_to_h32 0x9bdc06a7ul) (u32_to_h32 0xc19bf174ul)
  (u32_to_h32 0xe49b69c1ul) (u32_to_h32 0xefbe4786ul) (u32_to_h32 0x0fc19dc6ul) (u32_to_h32 0x240ca1ccul)
  (u32_to_h32 0x2de92c6ful) (u32_to_h32 0x4a7484aaul) (u32_to_h32 0x5cb0a9dcul) (u32_to_h32 0x76f988daul)
  (u32_to_h32 0x983e5152ul) (u32_to_h32 0xa831c66dul) (u32_to_h32 0xb00327c8ul) (u32_to_h32 0xbf597fc7ul)
  (u32_to_h32 0xc6e00bf3ul) (u32_to_h32 0xd5a79147ul) (u32_to_h32 0x06ca6351ul) (u32_to_h32 0x14292967ul)
  (u32_to_h32 0x27b70a85ul) (u32_to_h32 0x2e1b2138ul) (u32_to_h32 0x4d2c6dfcul) (u32_to_h32 0x53380d13ul)
  (u32_to_h32 0x650a7354ul) (u32_to_h32 0x766a0abbul) (u32_to_h32 0x81c2c92eul) (u32_to_h32 0x92722c85ul)
  (u32_to_h32 0xa2bfe8a1ul) (u32_to_h32 0xa81a664bul) (u32_to_h32 0xc24b8b70ul) (u32_to_h32 0xc76c51a3ul)
  (u32_to_h32 0xd192e819ul) (u32_to_h32 0xd6990624ul) (u32_to_h32 0xf40e3585ul) (u32_to_h32 0x106aa070ul)
  (u32_to_h32 0x19a4c116ul) (u32_to_h32 0x1e376c08ul) (u32_to_h32 0x2748774cul) (u32_to_h32 0x34b0bcb5ul)
  (u32_to_h32 0x391c0cb3ul) (u32_to_h32 0x4ed8aa4aul) (u32_to_h32 0x5b9cca4ful) (u32_to_h32 0x682e6ff3ul)
  (u32_to_h32 0x748f82eeul) (u32_to_h32 0x78a5636ful) (u32_to_h32 0x84c87814ul) (u32_to_h32 0x8cc70208ul)
  (u32_to_h32 0x90befffaul) (u32_to_h32 0xa4506cebul) (u32_to_h32 0xbef9a3f7ul) (u32_to_h32 0xc67178f2ul)


#reset-options " --max_fuel 0 --z3rlimit 10"

[@"substitute"]
val constants_set_h_0:
  hash:uint32_p{length hash = v size_hash_w} ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1
             /\ (let seq_h_0 = Hacl.Spec.Endianness.reveal_h32s (as_seq h1 hash) in
                seq_h_0 == Spec.h_0)))

[@"substitute"]
let constants_set_h_0 hash = hupd_8 hash
  (u32_to_h32 0x6a09e667ul) (u32_to_h32 0xbb67ae85ul) (u32_to_h32 0x3c6ef372ul) (u32_to_h32 0xa54ff53aul)
  (u32_to_h32 0x510e527ful) (u32_to_h32 0x9b05688cul) (u32_to_h32 0x1f83d9abul) (u32_to_h32 0x5be0cd19ul)


#reset-options " --max_fuel 0 --z3rlimit 20"

[@ "substitute"]
private
val ws_part_1_core:
  ws_w    :uint32_p {length ws_w = v size_ws_w} ->
  block_w :uint32_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  i:UInt32.t{UInt32.v i < 16} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w /\
                  (let seq_ws = reveal_h32s (as_seq h ws_w) in
                  let seq_block = reveal_h32s (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index seq_ws j)} j < UInt32.v i ==> Seq.index seq_ws j == Spec.ws seq_block j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  as_seq h1 block_w == as_seq h0 block_w
                  /\ (let w = reveal_h32s (as_seq h1 ws_w) in
                  let b = reveal_h32s (as_seq h0 block_w) in
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
  (**) Lemmas.lemma_spec_ws_def (reveal_h32s (as_seq h block_w)) (UInt32.v t);
  (**) assert(Seq.index (as_seq h1 ws_w) (UInt32.v t) == Seq.index (as_seq h block_w) (UInt32.v t))

[@"substitute"]
private val ws_part_1:
  ws_w    :uint32_p {length ws_w = v size_ws_w} ->
  block_w :uint32_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h32s (as_seq h1 ws_w) in
                  let b = reveal_h32s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --max_fuel 0 --z3rlimit 200"

[@"substitute"]
let ws_part_1 ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    i <= 16 /\ live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\
    as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_block = reveal_h32s (as_seq h0 block_w) in
       let w = reveal_h32s (as_seq h1 ws_w) in
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
  ws_w    :uint32_p {length ws_w = v size_ws_w} ->
  block_w :uint32_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  i:UInt32.t{16 <= UInt32.v i /\ UInt32.v i < 64} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w /\
                  (let w = reveal_h32s (as_seq h ws_w) in
                  let b = reveal_h32s (as_seq h block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i ==> Seq.index w j == Spec.ws b j))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1 /\
                  as_seq h1 block_w == as_seq h0 block_w
                  /\ (let w = reveal_h32s (as_seq h1 ws_w) in
                  let b = reveal_h32s (as_seq h0 block_w) in
                  (forall (j:nat). {:pattern (Seq.index w j)} j < UInt32.v i+1 ==> Seq.index w j == Spec.ws b j))))

#reset-options " --max_fuel 0 --z3rlimit 100"

[@ "substitute"]
let ws_part_2_core ws_w block_w t =
  (**) let h0 = ST.get () in
  let t16 = ws_w.(t -^ 16ul) in
  let t15 = ws_w.(t -^ 15ul) in
  let t7  = ws_w.(t -^ 7ul) in
  let t2  = ws_w.(t -^ 2ul) in
  ws_w.(t) <- H32.((_sigma1 t2) +%^ (t7 +%^ ((_sigma0 t15) +%^ t16)));
  (**) let h1 = ST.get () in
  (**) no_upd_lemma_1 h0 h1 ws_w block_w;
  (**) Lemmas.lemma_spec_ws_def2 (reveal_h32s (as_seq h0 block_w)) (UInt32.v t);
  (**) assert(Seq.index (reveal_h32s (as_seq h1 ws_w)) (UInt32.v t) == Spec.ws (reveal_h32s (as_seq h0 block_w)) (UInt32.v t))


#reset-options " --max_fuel 0 --z3rlimit 20"

[@"substitute"]
private val ws_part_2:
  ws_w    :uint32_p {length ws_w = v size_ws_w} ->
  block_w :uint32_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w
                  /\ (let w = reveal_h32s (as_seq h ws_w) in
                  let b = reveal_h32s (as_seq h block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 16 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w
                  /\ live h1 block_w /\ live h0 block_w /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h32s (as_seq h1 ws_w) in
                  let b = reveal_h32s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 64 ==> Seq.index w i == Spec.ws b i))))

#reset-options " --max_fuel 0 --z3rlimit 200"

[@"substitute"]
let ws_part_2 ws_w block_w =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 ws_w /\ live h1 block_w /\ modifies_1 ws_w h0 h1 /\ 16 <= i /\ i <= 64
    /\ as_seq h1 block_w == as_seq h0 block_w
    /\ (let seq_block = reveal_h32s (as_seq h0 block_w) in
       let w = reveal_h32s (as_seq h1 ws_w) in
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
  for 16ul 64ul inv f';
  (**) let h1 = ST.get() in ()


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val ws:
  ws_w    :uint32_p {length ws_w = v size_ws_w} ->
  block_w :uint32_p {length block_w = v size_block_w /\ disjoint ws_w block_w} ->
  Stack unit
        (requires (fun h -> live h ws_w /\ live h block_w))
        (ensures  (fun h0 r h1 -> live h1 ws_w /\ live h0 ws_w /\ live h1 block_w /\ live h0 block_w
                  /\ modifies_1 ws_w h0 h1
                  /\ (let w = reveal_h32s (as_seq h1 ws_w) in
                  let b = reveal_h32s (as_seq h0 block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 64 ==> Seq.index w i == Spec.ws b i))))

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
let ws ws_w block_w =
  ws_part_1 ws_w block_w;
  ws_part_2 ws_w block_w


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle_core:
  hash_w :uint32_p {length hash_w = v size_hash_w} ->
  block_w:uint32_p {length block_w = v size_block_w} ->
  ws_w   :uint32_p {length ws_w = v size_ws_w} ->
  k_w    :uint32_p {length k_w = v size_k_w} ->
  t      :uint32_t {v t < v size_k_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
          reveal_h32s (as_seq h k_w) == Spec.k /\
          (let w = reveal_h32s (as_seq h ws_w) in
           let b = reveal_h32s (as_seq h block_w) in
           (forall (i:nat). {:pattern (Seq.index w i)} i < 64 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 ws_w /\ live h0 k_w /\ live h0 block_w
          /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = reveal_h32s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h32s (as_seq h1 hash_w) in
                  let seq_block = reveal_h32s (as_seq h0 block_w) in
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
  let kt = k.(t) in
  let wst = ws.(t) in
  let t1 = H32.(h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ kt +%^ wst) in
  let t2 = H32.((_Sigma0 a) +%^ (_Maj a b c)) in

  (* Store the new working hash in the state *)
  hupd_8 hash H32.(t1 +%^ t2) a b c H32.(d +%^ t1) e f g


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val shuffle:
  hash_w :uint32_p {length hash_w = v size_hash_w} ->
  block_w:uint32_p {length block_w = v size_block_w /\ disjoint block_w hash_w} ->
  ws_w   :uint32_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint32_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h -> live h hash_w /\ live h ws_w /\ live h k_w /\ live h block_w /\
                  reveal_h32s (as_seq h k_w) == Spec.k /\
                  (let w = reveal_h32s (as_seq h ws_w) in
                  let b = reveal_h32s (as_seq h block_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 64 ==> Seq.index w i == Spec.ws b i)) ))
        (ensures  (fun h0 r h1 -> live h1 hash_w /\ modifies_1 hash_w h0 h1 /\ live h0 block_w
                  /\ live h0 hash_w
                  /\ (let seq_hash_0 = reveal_h32s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h32s (as_seq h1 hash_w) in
                  let seq_block = reveal_h32s (as_seq h0 block_w) in
                  seq_hash_1 == Spec.shuffle seq_hash_0 seq_block)))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let shuffle hash block ws k =
  (**) let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat) : Type0 =
    live h1 hash /\ modifies_1 hash h0 h1 /\ i <= v size_ws_w
    /\ (let seq_block = reveal_h32s (as_seq h0 block) in
    reveal_h32s (as_seq h1 hash) == repeat_range_spec 0 i (Spec.shuffle_core seq_block) (reveal_h32s (as_seq h0 hash)))
  in
  let f' (t:uint32_t {v t < v size_ws_w}) :
    Stack unit
      (requires (fun h -> inv h (UInt32.v t)))
      (ensures (fun h_1 _ h_2 -> inv h_2 (UInt32.v t + 1)))
    =
    shuffle_core hash block ws k t;
    (**) C.Loops.lemma_repeat_range_spec 0 (UInt32.v t + 1) (Spec.shuffle_core (reveal_h32s (as_seq h0 block))) (reveal_h32s (as_seq h0 hash))
  in
  (**) C.Loops.lemma_repeat_range_0 0 0 (Spec.shuffle_core (reveal_h32s (as_seq h0 block))) (reveal_h32s (as_seq h0 hash));
  for 0ul size_ws_w inv f'


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val sum_hash:
  hash_0:uint32_p{length hash_0 = v size_hash_w} ->
  hash_1:uint32_p{length hash_1 = v size_hash_w /\ disjoint hash_0 hash_1} ->
  Stack unit
    (requires (fun h -> live h hash_0 /\ live h hash_1))
    (ensures  (fun h0 _ h1 -> live h0 hash_0 /\ live h1 hash_0 /\ live h0 hash_1 /\ modifies_1 hash_0 h0 h1
              /\ (let new_seq_hash_0 = as_seq h1 hash_0 in
              let seq_hash_0 = as_seq h0 hash_0 in
              let seq_hash_1 = as_seq h0 hash_1 in
              new_seq_hash_0 == Spec.Lib.map2 (fun x y -> H32.(x +%^ y)) seq_hash_0 seq_hash_1 )))

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
let sum_hash hash_0 hash_1 =
  C.Loops.in_place_map2 hash_0 hash_1 size_hash_w (fun x y -> H32.(x +%^ y))


#reset-options "--max_fuel 0 --z3rlimit 20"

[@"c_inline"]
val alloc:
  unit ->
  StackInline (state:uint32_p{length state = v size_state})
    (requires (fun h0 -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
             /\ Map.domain h1.h == Map.domain h0.h))

[@"c_inline"]
let alloc () = Buffer.create (u32_to_h32 0ul) size_state


#reset-options "--max_fuel 0  --z3rlimit 50"

val init:
  state:uint32_p{length state = v size_state} ->
  Stack unit
    (requires (fun h0 -> live h0 state
              /\ (let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              H32.v counter = 0)))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1
              /\ (let slice_k = Seq.slice (as_seq h1 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let slice_h_0 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
              let seq_counter = Seq.slice (as_seq h1 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              let seq_k = Hacl.Spec.Endianness.reveal_h32s slice_k in
              let seq_h_0 = Hacl.Spec.Endianness.reveal_h32s slice_h_0 in
              seq_k == Spec.k /\ seq_h_0 == Spec.h_0 /\ H32.v counter = 0)))

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


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val copy_hash:
  hash_w_1 :uint32_p {length hash_w_1 = v size_hash_w} ->
  hash_w_2 :uint32_p {length hash_w_2 = v size_hash_w /\ disjoint hash_w_1 hash_w_2} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w_1 /\ live h0 hash_w_2))
        (ensures  (fun h0 _ h1 -> live h0 hash_w_1 /\ live h0 hash_w_2 /\ live h1 hash_w_1 /\ modifies_1 hash_w_1 h0 h1
                  /\ (as_seq h1 hash_w_1 == as_seq h0 hash_w_2)))

#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
let copy_hash hash_w_1 hash_w_2 =
  (**) let h0 = ST.get () in
  Buffer.blit hash_w_2 0ul hash_w_1 0ul size_hash_w;
  (**) let h1 = ST.get () in
  (**) assert(Seq.slice (as_seq h1 hash_w_1) 0 (v size_hash_w) == Seq.slice (as_seq h0 hash_w_2) 0 (v size_hash_w));
  (**) Lemmas.lemma_blit_slices_eq h0 h1 hash_w_1 hash_w_2 (v size_hash_w)


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
private val update_core:
  hash_w :uint32_p {length hash_w = v size_hash_w} ->
  data   :uint8_p  {length data = v size_block /\ disjoint data hash_w} ->
  data_w :uint32_p {length data_w = v size_block_w /\ disjoint data_w hash_w} ->
  ws_w   :uint32_p {length ws_w = v size_ws_w /\ disjoint ws_w hash_w} ->
  k_w    :uint32_p {length k_w = v size_k_w /\ disjoint k_w hash_w} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h0 ws_w /\ live h0 k_w
                  /\ reveal_h32s (as_seq h0 k_w) == Spec.k
                  /\ (reveal_h32s (as_seq h0 data_w) = Spec.Lib.uint32s_from_be (v size_block_w) (reveal_sbytes (as_seq h0 data)))
                  /\ (let w = reveal_h32s (as_seq h0 ws_w) in
                  let b = reveal_h32s (as_seq h0 data_w) in
                  (forall (i:nat). {:pattern (Seq.index w i)} i < 64 ==> Seq.index w i == Spec.ws b i))))
        (ensures  (fun h0 r h1 -> live h0 hash_w /\ live h0 data /\ live h0 data_w /\ live h1 hash_w /\ modifies_1 hash_w h0 h1
                  /\ (let seq_hash_0 = reveal_h32s (as_seq h0 hash_w) in
                  let seq_hash_1 = reveal_h32s (as_seq h1 hash_w) in
                  let seq_block = reveal_sbytes (as_seq h0 data) in
                  seq_hash_1 == Spec.update seq_hash_0 seq_block)))

#reset-options "--max_fuel 0  --z3rlimit 400"

[@"substitute"]
let update_core hash_w data data_w ws_w k_w =
  (**) assert_norm(pow2 32 = 0x100000000);
  (**) assert_norm(pow2 61 = 2305843009213693952);
  (**) let h0 = ST.get() in

  (* Push a new frame *)
  (**) push_frame();
  (**) let h1 = ST.get() in
  (**) assert(let b = Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
              reveal_h32s (as_seq h0 data_w) == b);

  (* Allocate space for converting the data block *)
  let hash_0 = Buffer.create (u32_to_h32 0ul) size_hash_w in
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 data_w;
  (**) no_upd_lemma_0 h1 h2 ws_w;
  (**) no_upd_lemma_0 h1 h2 k_w;
  (**) no_upd_lemma_0 h1 h2 hash_w;

  (* Keep track of the the current working hash from the state *)
  copy_hash hash_0 hash_w;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' hash_0 h1 h2 h3;
  (**) no_upd_lemma_1 h2 h3 hash_0 data;
  (**) no_upd_lemma_1 h2 h3 hash_0 data_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 ws_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 k_w;
  (**) no_upd_lemma_1 h2 h3 hash_0 hash_w;

  (* Step 2 : Initialize the eight working variables *)
  (* Step 3 : Perform logical operations on the working variables *)
  (* Step 4 : Compute the ith intermediate hash value *)
  shuffle hash_0 data_w ws_w k_w;
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1' hash_0 h1 h3 h4;
  (**) assert(let b = Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data)) in
              let ha = Spec.shuffle (reveal_h32s (as_seq h0 hash_w)) b in
              as_seq h4 hash_w == as_seq h0 hash_w /\
              reveal_h32s (as_seq h4 hash_0) == ha);
  (**) no_upd_lemma_1 h3 h4 hash_0 data;
  (**) no_upd_lemma_1 h3 h4 hash_0 data_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 ws_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 k_w;
  (**) no_upd_lemma_1 h3 h4 hash_0 hash_w;

  (* Use the previous one to update it inplace *)
  sum_hash hash_w hash_0;
  (**) let h5 = ST.get() in
  (**) lemma_modifies_0_1 hash_w h1 h4 h5;
  (**) assert(let x = reveal_h32s (as_seq h4 hash_w) in
          let y = reveal_h32s (as_seq h4 hash_0) in
          x == reveal_h32s (as_seq h0 hash_w) /\
          y == Spec.shuffle (reveal_h32s (as_seq h0 hash_w)) (Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data))));
  (**) assert(let x = reveal_h32s (as_seq h0 hash_w) in
         let y = Spec.shuffle (reveal_h32s (as_seq h0 hash_w)) (Spec.words_from_be Spec.size_block_w (reveal_sbytes (as_seq h0 data))) in
         let z = reveal_h32s (as_seq h5 hash_w) in
         let z' = Spec.Loops.seq_map2 (fun x y -> FStar.UInt32.(x +%^ y)) x y in
         z == z');
  (**) no_upd_lemma_1 h4 h5 hash_w data;
  (**) no_upd_lemma_1 h4 h5 hash_w data_w;
  (**) no_upd_lemma_1 h4 h5 hash_w ws_w;
  (**) no_upd_lemma_1 h4 h5 hash_w k_w;

  (* Pop the frame *)
  (**) pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 hash_w h0 h1 h5 hfin


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val counter_increment:
  counter_w :uint32_p{length counter_w = v size_count_w} ->
  Stack unit
        (requires (fun h -> live h counter_w
                  /\ (let counter = Seq.index (as_seq h counter_w) 0 in
                  H32.v counter < (pow2 32 - 1))))
        (ensures  (fun h0 _ h1 -> live h1 counter_w /\ live h0 counter_w /\ modifies_1 counter_w h0 h1
                  /\ (let counter_0 = Seq.index (as_seq h0 counter_w) 0 in
                  let counter_1 = Seq.index (as_seq h1 counter_w) 0 in
                  H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32)))

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
let counter_increment counter_w =
  let c0 = counter_w.(0ul) in
  let one = u32_to_h32 1ul in
  counter_w.(0ul) <- H32.(c0 +%^ one)


#reset-options "--max_fuel 0  --z3rlimit 50"

val update:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {length data = v size_block /\ disjoint state data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 1))))
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
                  /\ H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32
                  /\ (reveal_h32s seq_hash_1 == Spec.update (reveal_h32s seq_hash_0) (reveal_sbytes seq_block)))))

#reset-options "--max_fuel 0  --z3rlimit 500"

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
  let data_w = Buffer.create (u32_to_h32 0ul) size_block_w in
  (**) let h2 = ST.get () in
  (**) no_upd_lemma_0 h1 h2 data;
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_0 h1 h2 (Buffer.sub state pos_count_w size_count_w);

  (* Cast the data bytes into a uint32_t buffer *)
  uint32s_from_be_bytes data_w data size_block_w;
  (**) let h3 = ST.get () in
  (**) lemma_modifies_0_1' data_w h1 h2 h3;
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_k_w size_k_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_whash_w size_whash_w);
  (**) no_upd_lemma_1 h2 h3 data_w (Buffer.sub state pos_count_w size_count_w);
  (**) no_upd_lemma_1 h2 h3 data_w data;
  (**) assert(reveal_h32s (as_seq h3 data_w) == Spec.Lib.uint32s_from_be (U32.v size_block_w) (reveal_sbytes (as_seq h3 data)));

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
  (**) assert(reveal_h32s (as_seq h4 k_w) == Spec.k);
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
  (**) assert(reveal_h32s (as_seq h5 hash_w) == Spec.update (reveal_h32s (as_seq h0 hash_w)) (reveal_sbytes (as_seq h0 data)));

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
                  H32.v counter_1 = H32.v counter_0 + 1 /\ H32.v counter_1 < pow2 32);
  (**) assert(let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h6 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_block = as_seq h0 data in
                  reveal_h32s seq_hash_1 == Spec.update (reveal_h32s seq_hash_0) (reveal_sbytes seq_block));

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
  state :uint32_p{length state = v size_state} ->
  data  :uint8_p {length data % v size_block = 0 /\ disjoint state data} ->
  n     :uint32_t{v n * v size_block = length data} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data /\
                 (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  reveal_h32s seq_k == Spec.k /\ H32.v counter < pow2 32 - (v n))))
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
                  H32.v counter1 = H32.v counter0 + (v n) /\
                  H32.v counter1 < pow2 32 /\
                  reveal_h32s seq_hash1 ==
                  Spec.update_multi (reveal_h32s seq_hash0) (reveal_sbytes seq_blocks) )))

let update_multi state data n =
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
     reveal_h32s seq_k == Spec.k /\ 
     H32.v counter < pow2 32 - v n + i /\
     H32.v counter = H32.v counter0 + i /\
     reveal_h32s seq_hash ==
     Spec.update_multi (reveal_h32s hash0) (reveal_sbytes blocks) )
  in
  let empty = Buffer.sub data 0ul (0ul *^ size_block) in
  Spec.lemma_update_multi_empty (reveal_h32s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))) (reveal_sbytes (as_seq h0 empty));
  Lemmas.lemma_modifies_0_is_modifies_1 h0 state;

  let f (i:uint32_t{0 <= v i /\ v i < v n}) : Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures  (fun h0 _ h1 -> inv h0 (v i) /\ inv h1 (v i + 1)))
  = 
    let h = ST.get() in
    let blocks = Buffer.sub data 0ul (i *^ size_block) in
    let b      = Buffer.sub data (i *^ size_block) size_block in
    Spec.update_update_multi_append
      (reveal_h32s (Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))))
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
let encode_length (count:uint32_ht) (len:uint32_t) : Tot (l:uint64_ht{H64.v l = (H32.v count * v size_block + v len) * 8}) =
  let l_0 = H64.((h32_to_h64 count) *%^ (u32_to_h64 size_block)) in
  let l_1 = u32_to_h64 len in
  H64.((l_0 +^ l_1) *%^ (u32_to_h64 8ul))


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val set_pad_part1:
  buf1 :uint8_p {length buf1 = 1} ->
  Stack unit
        (requires (fun h0 -> live h0 buf1))
        (ensures  (fun h0 _ h1 -> live h0 buf1 /\ live h1 buf1 /\ modifies_1 buf1 h0 h1
                             /\ (let seq_buf1 = reveal_sbytes (as_seq h1 buf1) in
                             seq_buf1 = Seq.create 1 0x80uy)))

#reset-options "--max_fuel 0 --z3rlimit 50"

[@"substitute"]
let set_pad_part1 buf1 =
  Buffer.upd buf1 0ul (u8_to_h8 0x80uy);
  (**) let h = ST.get () in
  (**) Seq.lemma_eq_intro (as_seq h buf1) (Seq.create 1 (u8_to_h8 0x80uy))

#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
val set_pad_part2:
  buf2       :uint8_p{length buf2 = v size_len_8} ->
  encodedlen :uint64_ht ->
  Stack unit
        (requires (fun h0 -> live h0 buf2))
        (ensures  (fun h0 _ h1 -> live h0 buf2 /\ live h1 buf2 /\ modifies_1 buf2 h0 h1
                  /\ (let seq_buf2 = reveal_sbytes (as_seq h1 buf2) in
                  seq_buf2 == Endianness.big_bytes size_len_8 (H64.v encodedlen))))

#reset-options "--max_fuel 0  --z3rlimit 30"

[@"substitute"]
let set_pad_part2 buf2 encodedlen =
  Hacl.Endianness.hstore64_be buf2 encodedlen;
  (**) let h = ST.get () in
  (**) Lemmas.lemma_eq_endianness h buf2 encodedlen


#reset-options "--max_fuel 0  --z3rlimit 50"

[@"substitute"]
val pad:
  padding :uint8_p ->
  n       :uint32_ht ->
  len     :uint32_t {(v len + v size_len_8 + 1) < (2 * v size_block)
                     /\ H32.v n * v size_block + v len < U64.v max_input_len
                     /\ length padding = (1 + v (pad0_length len) + v size_len_8)
                     /\ (length padding + v len) % v size_block = 0} ->
  Stack unit
        (requires (fun h0 -> live h0 padding
                  /\ (let seq_padding = reveal_sbytes (as_seq h0 padding) in
                  seq_padding == Seq.create (1 + v (pad0_length len) + v size_len_8) 0uy )))
        (ensures  (fun h0 _ h1 -> live h0 padding /\ live h1 padding /\ modifies_1 padding h0 h1
                  /\ (let seq_padding = reveal_sbytes (as_seq h1 padding) in
                  seq_padding == Spec.pad (H32.v n * v size_block) (v len))))

#reset-options "--max_fuel 0  --z3rlimit 100"

[@"substitute"]
let pad padding n len =

  (* Compute the length of zeros *)
  let pad0len = pad0_length len in

  (* Retreive the different parts of the padding *)
  let buf1 = Buffer.sub padding 0ul 1ul in
  let zeros = Buffer.sub padding 1ul pad0len in
  let buf2 = Buffer.sub padding (1ul +^ pad0len) size_len_8 in

  (* Compute and encode the total length *)
  let encodedlen = encode_length n len in

  let h0 = ST.get () in
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h0 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h0 zeros) == Seq.create (v pad0len) 0uy);

  (* Set the first byte of the padding *)
  set_pad_part1 buf1;

  (* Encode the total length at the end of the padding *)
  set_pad_part2 buf2 encodedlen;

  (* Proof that this is the concatenation of the three parts *)
  let h1 = ST.get () in
  (**) Buffer.no_upd_lemma_2 h0 h1 buf1 buf2 zeros;
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 zeros)) (Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h1 zeros) == Seq.create (v pad0len) 0uy);
  (**) assert(reveal_sbytes (as_seq h1 buf1) == Seq.create 1 0x80uy);
  (**) assert(reveal_sbytes (as_seq h1 zeros) == Seq.create (v (pad0_length len)) 0uy);
  (**) assert(reveal_sbytes (as_seq h1 buf2) == Endianness.big_bytes size_len_8 (H64.v encodedlen));
  (**) Lemmas.lemma_sub_append_3 h1 padding 0ul buf1 1ul zeros (1ul +^ pad0len) buf2 (1ul +^ pad0len +^ size_len_8);
  (**) Lemmas.lemma_pad_aux h1 n len buf1 zeros buf2


#reset-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 50"

val update_last:
  state :uint32_p {length state = v size_state} ->
  data  :uint8_p  {disjoint state data} ->
  len   :uint32_t {v len = length data /\ (length data + v size_len_8 + 1) < 2 * v size_block} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 data
                  /\ (let seq_k = Seq.slice (as_seq h0 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
                  let seq_counter = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
                  let counter = Seq.index seq_counter 0 in
                  let nb = U32.div len size_block in
                  reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 2))))
        (ensures  (fun h0 r h1 -> live h0 state /\ live h0 data /\ live h1 state /\ modifies_1 state h0 h1
                  /\ (let seq_hash_0 = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash_1 = Seq.slice (as_seq h1 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_data = reveal_sbytes (as_seq h0 data) in
                  let count = Seq.slice (as_seq h0 state) (U32.v pos_count_w) (U32.v pos_count_w + 1) in
                  let prevlen = U32.(H32.v (Seq.index count 0) * (v size_block)) in
                  (reveal_h32s seq_hash_1) == Spec.update_last (reveal_h32s seq_hash_0) prevlen seq_data)))

#reset-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 200"

let update_last state data len =

  (**) let hinit = ST.get() in
  
  (* Push a new memory frame *)
  (**) push_frame();

  (**) let h00 = ST.get() in

  (* Alocate memory set to zeros for the last two blocks of data *)
  let blocks = Buffer.create (uint8_to_sint8 0uy) (2ul *^ size_block) in

  (**) let h0 = ST.get () in
  (**) assert(reveal_sbytes (as_seq h0 blocks) == Seq.create (2 * v size_block) 0uy);

  (* Verification of how many blocks are necessary *)
  (* Threat model. The length are considered public here ! *)
  let (nb, final_blocks) =
    if U32.(len <^ 56ul) then (1ul, Buffer.offset blocks size_block)
    else (2ul, blocks)
  in
  (**) assert(blocks `includes` final_blocks);

  (**) let h1 = ST.get () in

  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 final_blocks))
                          (if U32.(len <^ 56ul) then
                              Seq.create (v size_block) 0uy
                           else Seq.create (2 * v size_block) 0uy);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 final_blocks)) (Seq.create (v nb * v size_block) 0uy);
  (**) assert(reveal_sbytes (as_seq h1 final_blocks) == Seq.create (v nb * v size_block) 0uy);

  (* Copy the data to the final construct *)
  (* Leakage model : allowed because the length is public *)
  Buffer.blit data 0ul final_blocks 0ul len;

  (**) let h2 = ST.get () in
  (**) modifies_subbuffer_1 h1 h2 final_blocks blocks;
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h2 data) 0 (v len));
  (**) Seq.lemma_eq_intro (as_seq h2 data) (Seq.slice (as_seq h2 final_blocks) 0 (v len));
  (**) assert(as_seq h2 data == Seq.slice (as_seq h2 final_blocks) 0 (v len));

  (* Compute the final length of the data *)
  let n = state.(pos_count_w) in

  (* Set the padding *)
  let padding = Buffer.offset final_blocks len in
  (**) assert(v len + v size_len_8 + 1 < 2 * v size_block);
  (**) assert(H32.v n * v size_block + v len < U64.v max_input_len);
  (**) assert(length padding = (1 + v (pad0_length len) + v size_len_8));
  (**) assert((length padding + v len) % v size_block = 0);
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 padding)) (Seq.create (1 + v (pad0_length len) + v size_len_8) 0uy);
  (**) assert(reveal_sbytes (as_seq h2 padding) == Seq.create (1 + v (pad0_length len) + v size_len_8) 0uy);
  pad padding n len;

  (* Proof that final_blocks = data @| padding *)
  (**) let h3 = ST.get () in
  (**) modifies_subbuffer_1 h2 h3 padding blocks;
  (**) lemma_modifies_1_trans blocks h1 h2 h3;
  (**) assert(disjoint padding data);
  (**) no_upd_lemma_1 h2 h3 padding data;
  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.sub final_blocks 0ul len)) (Seq.slice (as_seq h3 final_blocks) 0 (v len));
  (**) no_upd_lemma_1 h2 h3 padding (Buffer.sub final_blocks 0ul len);
  (**) assert(reveal_sbytes (as_seq h3 data) == Seq.slice (reveal_sbytes (as_seq h3 final_blocks)) 0 (v len));

  (**) Seq.lemma_eq_intro (as_seq h3 (Buffer.offset final_blocks len)) (Seq.slice (as_seq h3 final_blocks) (v len) (v nb * v size_block));
  (**) Seq.lemma_eq_intro (as_seq h3 padding) (Seq.slice (as_seq h3 final_blocks) (v len) (v nb * v size_block));
  (**) assert(as_seq h3 padding == Seq.slice (as_seq h3 final_blocks) (v len) (v nb * v size_block));
  (**) Lemmas.lemma_sub_append_2 h3 final_blocks 0ul data len padding (nb *^ size_block);
  (**) assert(as_seq h3 final_blocks == Seq.append (as_seq h3 data) (as_seq h3 padding));

  (* Call the update function on one or two blocks *)
  (**) assert(length final_blocks % v size_block = 0 /\ disjoint state data);
  (**) assert(v nb * v size_block = length final_blocks);
  (**) assert(live h3 state /\ live h3 final_blocks);
  (**) assert(let seq_k = Seq.slice (as_seq h3 state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)) in
              let seq_counter = Seq.slice (as_seq h3 state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)) in
              let counter = Seq.index seq_counter 0 in
              reveal_h32s seq_k == Spec.k /\ H32.v counter < (pow2 32 - 2));

  update_multi state final_blocks nb;

  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1' blocks h00 h1 h3;
  (**) lemma_modifies_0_1 state h00 h3 h4;

  (* Pop the memory frame *)
  (**) pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 state hinit h00 h4 hfin


#reset-options "--max_fuel 0  --z3rlimit 20"

[@"substitute"]
val finish_core:
  hash_w :uint32_p {length hash_w = v size_hash_w} ->
  hash   :uint8_p  {length hash = v size_hash /\ disjoint hash_w hash} ->
  Stack unit
        (requires (fun h0 -> live h0 hash_w /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 hash_w /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = reveal_h32s (as_seq h0 hash_w) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.words_to_be (U32.v size_hash_w) seq_hash_w)))

[@"substitute"]
let finish_core hash_w hash = uint32s_to_be_bytes hash hash_w size_hash_w


#reset-options "--max_fuel 0  --z3rlimit 20"

val finish:
  state :uint32_p{length state = v size_state} ->
  hash  :uint8_p{length hash = v size_hash /\ disjoint state hash} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 hash))
        (ensures  (fun h0 _ h1 -> live h0 state /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_hash_w = Seq.slice (as_seq h0 state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash = Spec.finish (reveal_h32s seq_hash_w))))

let finish state hash =
  let hash_w = Buffer.sub state pos_whash_w size_whash_w in
  finish_core hash_w hash


#reset-options "--max_fuel 0  --z3rlimit 20"

val hash:
  hash :uint8_p {length hash = v size_hash} ->
  input:uint8_p {length input < Spec.max_input_len_8 /\ disjoint hash input} ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1
                  /\ (let seq_input = reveal_sbytes (as_seq h0 input) in
                  let seq_hash = reveal_sbytes (as_seq h1 hash) in
                  seq_hash == Spec.hash seq_input)))

#reset-options "--max_fuel 0  --z3rlimit 50"

let hash hash input len =

  (**) let hinit = ST.get() in

  (* Push a new memory frame *)
  (**) push_frame ();
  (**) let h0 = ST.get() in

  (* Allocate memory for the hash state *)
  let state = Buffer.create (u32_to_h32 0ul) size_state in
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
