module Hacl.Impl.SHA2_512.Lemmas

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
module Buffer = FStar.Buffer
module Cast = Hacl.Cast

module Spec = Spec.SHA2_512


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


#reset-options "--max_fuel 0  --z3rlimit 200"

let lemma_aux_0 (t:UInt32.t{UInt32.v t >= 16 /\ UInt32.v t < 80}) : Lemma
  (UInt32.v (t -^ 16ul) >= 0 /\ UInt32.v (t -^ 15ul) >= 0
   /\ UInt32.v (t -^ 7ul) >= 0 /\ UInt32.v (t -^ 2ul) >= 0
   /\ UInt32.v (t -^ 16ul) < 80 /\ UInt32.v (t -^ 15ul) < 80
   /\ UInt32.v (t -^ 7ul) < 80 /\ UInt32.v (t -^ 2ul) < 80)
  = ()


#reset-options "--max_fuel 0  --z3rlimit 20"

let lemma_aux_1 (a:nat) (b:nat) : Lemma (requires (a = 0)) (ensures (a * b = 0)) = ()


#reset-options "--max_fuel 0  --z3rlimit 100"

let lemma_aux_2 (a:nat) (b:pos) : Lemma (requires (a > 0)) (ensures (a * b > 0)) = ()


#reset-options "--max_fuel 0  --z3rlimit 200"

val lemma_ws_def_0: (b:Spec.block_w) -> (t:Spec.counter{t < 16}) -> Lemma
  (Spec.ws b t = Seq.index b t)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"
let lemma_ws_def_0 b t = ()


#reset-options "--max_fuel 0  --z3rlimit 200"

val lemma_ws_def_1: (b:Spec.block_w) -> (t:Spec.counter{16 <= t /\ t < 80}) -> Lemma
  (Spec.ws b t =
    (let open Spec in
     let t16 = ws b (t - 16) in
     let t15 = ws b (t - 15) in
     let t7  = ws b (t - 7) in
     let t2  = ws b (t - 2) in
     let s1 = _sigma1 t2 in
     let s0 = _sigma0 t15 in
     FStar.UInt64.(s1 +%^ (t7 +%^ (s0 +%^ t16)))))

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let lemma_ws_def_1 b t = ()


#reset-options " --max_fuel 1 --z3rlimit 20"

val lemma_spec_ws_def2:
  b:Seq.seq UInt64.t{Seq.length b = Spec.block_word_length} ->
  t:nat{16 <= t /\ t < 80} ->
  Lemma(let t16 = Spec.ws b (t - 16) in
        let t15 = Spec.ws b (t - 15) in
        let t7  = Spec.ws b (t - 7) in
        let t2  = Spec.ws b (t - 2) in
        let s1 = Spec._sigma1 t2 in
        let s0 = Spec._sigma0 t15 in
        Spec.ws b t == FStar.UInt64.(s1 +%^ (t7 +%^ (s0 +%^ t16))))

#reset-options " --max_fuel 1 --z3rlimit 20"

let lemma_spec_ws_def2 b i = ()

#reset-options "--max_fuel 0  --z3rlimit 200"


let lemma_modifies_0_is_modifies_1 (#a:Type) (h:HyperStack.mem) (b:buffer a{live h b}) : Lemma
  (modifies_1 b h h) =
  lemma_modifies_sub_1 h h b


let lemma_blit_slices_eq (#t:Type) (h0:HyperStack.mem) (h1:HyperStack.mem) (a:buffer t{live h1 a}) (b:buffer t{live h0 b}) (len:nat{len = length a /\ len = length b}): Lemma
  (requires (let slice_a = Seq.slice (as_seq h1 a) 0 len in
             let slice_b = Seq.slice (as_seq h0 b) 0 len in
             slice_a == slice_b))
  (ensures  (as_seq h1 a == as_seq h0 b)) =
  Seq.lemma_eq_intro (as_seq h1 a) (Seq.slice (as_seq h1 a) 0 len);
  Seq.lemma_eq_intro (as_seq h0 b) (Seq.slice (as_seq h0 b) 0 len)


#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_update_multi_def0: (hash:Spec.words_state) -> (blocks:Spec.bytes{Seq.length blocks = 0}) -> Lemma
  (Spec.update_multi hash blocks = hash)

#reset-options "--max_fuel 1 --z3rlimit 20"

let lemma_update_multi_def0 hash blocks = ()


#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_update_multi_def: (hash:Spec.words_state) -> (blocks:Spec.bytes{Seq.length blocks % Spec.block_length = 0}) -> Lemma
  (Spec.update_multi hash blocks = (
    if Seq.length blocks = 0 then hash
    else (
      let (block,rem) = Seq.split blocks Spec.block_length in
      let hash = Spec.update hash block in
      Spec.update_multi hash rem)))

#reset-options "--max_fuel 1 --z3rlimit 20"

let lemma_update_multi_def hash blocks = ()


#reset-options "--max_fuel 0  --z3rlimit 100"

let lemma_eq_endianness (h:HyperStack.mem) (buf:uint8_p{length buf = 16}) (n:uint128_ht) : Lemma
  (requires (live h buf /\
            (let seq_buf = as_seq h buf in
             Hacl.Spec.Endianness.hbig_endian seq_buf = (H128.v n))))
  (ensures  (live h buf /\
            (let seq_buf = reveal_sbytes (as_seq h buf) in
            seq_buf == FStar.Old.Endianness.big_bytes 16ul (H128.v n)))) =
  FStar.Old.Endianness.lemma_big_endian_inj (FStar.Old.Endianness.big_bytes 16ul (H128.v n)) (reveal_sbytes (as_seq h buf));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h buf)) (FStar.Old.Endianness.big_bytes 16ul (H128.v n))


#reset-options "--max_fuel 0  --z3rlimit 100"

let lemma_sub_append_2 (h:HyperStack.mem) (g:uint8_p) (p0:uint32_t{v p0 = 0}) (a:uint8_p) (p1:uint32_t{v p0 <= v p1 /\ v p1 <= length g}) (b:uint8_p) (p2:uint32_t{v p1 <= v p2 /\ v p2 = length g}) : Lemma
  (requires (live h g /\ live h a /\ live h b
            /\ (let seq_g = as_seq h g in
               let seq_a = as_seq h a in
               let seq_b = as_seq h b in
               seq_a == Seq.slice seq_g (v p0) (v p1)
               /\ seq_b == Seq.slice seq_g (v p1) (v p2))))
  (ensures  (live h g /\ live h a /\ live h b
            /\ (let seq_g = as_seq h g in
               let seq_a = as_seq h a in
               let seq_b = as_seq h b in
               seq_g == Seq.append seq_a seq_b))) =
let seq_g = as_seq h g in
let seq_a = as_seq h a in
let seq_b = as_seq h b in
Seq.lemma_eq_intro (as_seq h g) (Seq.append seq_a seq_b)


#reset-options "--max_fuel 0  --z3rlimit 100"

let lemma_sub_append_3 (h:HyperStack.mem) (g:uint8_p) (p0:uint32_t{v p0 = 0}) (a:uint8_p) (p1:uint32_t{v p0 <= v p1 /\ v p1 <= length g}) (b:uint8_p) (p2:uint32_t{v p1 <= v p2 /\ v p2 <= length g}) (c:uint8_p) (p3:uint32_t{v p2 <= v p3 /\ v p3 = length g}): Lemma
  (requires (live h g /\ live h a /\ live h b /\ live h c
            /\ (let seq_g = as_seq h g in
               let seq_a = as_seq h a in
               let seq_b = as_seq h b in
               let seq_c = as_seq h c in
               seq_a == Seq.slice seq_g (v p0) (v p1)
               /\ seq_b == Seq.slice seq_g (v p1) (v p2)
               /\ seq_c == Seq.slice seq_g (v p2) (v p3))))
  (ensures  (live h g /\ live h a /\ live h b /\ live h c
            /\ (let seq_g = as_seq h g in
               let seq_a = as_seq h a in
               let seq_b = as_seq h b in
               let seq_c = as_seq h c in
               seq_g == Seq.append (Seq.append seq_a seq_b) seq_c))) =
let seq_g = as_seq h g in
let seq_a = as_seq h a in
let seq_b = as_seq h b in
let seq_c = as_seq h c in
Seq.lemma_eq_intro (as_seq h g) (Seq.append (Seq.append seq_a seq_b) seq_c)


#reset-options "--max_fuel 0  --z3rlimit 50"

let lemma_pad_aux_seq (n:uint64_ht) (len:uint64_t {(U64.v len + v len_length + 1) <= (2 * v block_length) /\ H64.v n * v block_length + U64.v len < Spec.max_input_len_8}) (a:Seq.seq UInt8.t) (b:Seq.seq UInt8.t) (c:Seq.seq UInt8.t) : Lemma
  (requires (a == Seq.create 1 0x80uy
            /\ (b == Seq.create (Spec.pad0_length (U64.v len)) 0uy)
            /\ (c == FStar.Old.Endianness.big_bytes len_length ((H64.v n * v block_length + U64.v len) * 8))))
  (ensures  (Seq.append (Seq.append a b) c == Spec.pad (H64.v n * v block_length) (U64.v len))) =
Seq.lemma_eq_intro (Seq.append (Seq.append a b) c) (Seq.append a (Seq.append b c))


#reset-options "--max_fuel 0  --z3rlimit 200"

let lemma_pad_aux (h:HyperStack.mem) (n:uint64_ht) (len:uint64_t {(U64.v len + v len_length + 1) <= (2 * v block_length) /\ H64.v n * v block_length + U64.v len < Spec.max_input_len_8}) (a:uint8_p) (b:uint8_p) (c:uint8_p) : Lemma
  (requires (live h a /\ live h b /\ live h c
            /\ (let seq_a = reveal_sbytes (as_seq h a) in
            let seq_b = reveal_sbytes (as_seq h b) in
            let seq_c = reveal_sbytes (as_seq h c) in
            seq_a == Seq.create 1 0x80uy
            /\ (seq_b == Seq.create (Spec.pad0_length (U64.v len)) 0uy)
            /\ (seq_c == FStar.Old.Endianness.big_bytes len_length ((H64.v n * v block_length + U64.v len) * 8)))))
  (ensures  (live h a /\ live h b /\ live h c
            /\ (let seq_a = reveal_sbytes (as_seq h a) in
            let seq_b = reveal_sbytes (as_seq h b) in
            let seq_c = reveal_sbytes (as_seq h c) in
            (Seq.append (Seq.append seq_a seq_b) seq_c == Spec.pad (H64.v n * v block_length) (U64.v len))))) =
let seq_a = reveal_sbytes (as_seq h a) in
let seq_b = reveal_sbytes (as_seq h b) in
let seq_c = reveal_sbytes (as_seq h c) in
lemma_pad_aux_seq n len seq_a seq_b seq_c


#reset-options " --max_fuel 0 --z3rlimit 20"

val lemma_spec_ws_def:
  b:Seq.seq UInt64.t{Seq.length b = Spec.block_word_length} ->
  i:nat{i < 16} ->
  Lemma (Spec.ws b i == Seq.index b i)

#reset-options " --max_fuel 1 --z3rlimit 20"

let lemma_spec_ws_def b i = ()


#reset-options "--max_fuel 0  --z3rlimit 50"

val lemma_eq_state_k_sub_slice:
  h: HyperStack.mem ->
  state :uint64_p {length state = v size_state /\ live h state} ->
  Lemma (as_seq h (Buffer.sub state pos_k_w size_k_w) == (Seq.slice (as_seq h state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w))))

#reset-options "--max_fuel 0  --z3rlimit 150"

let lemma_eq_state_k_sub_slice h state =
  Seq.lemma_eq_intro (as_seq h (Buffer.sub state pos_k_w size_k_w))
                      (Seq.slice (as_seq h state) (U32.v pos_k_w) (U32.(v pos_k_w + v size_k_w)))


#reset-options "--max_fuel 0  --z3rlimit 50"

val lemma_eq_state_counter_sub_slice:
  h: HyperStack.mem ->
  state :uint64_p {length state = v size_state /\ live h state} ->
  Lemma (as_seq h (Buffer.sub state pos_count_w size_count_w) == (Seq.slice (as_seq h state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w))))

#reset-options "--max_fuel 0  --z3rlimit 150"

let lemma_eq_state_counter_sub_slice h state =
  Seq.lemma_eq_intro (as_seq h (Buffer.sub state pos_count_w size_count_w))
                      (Seq.slice (as_seq h state) (U32.v pos_count_w) (U32.(v pos_count_w + v size_count_w)))


#reset-options "--max_fuel 0  --z3rlimit 50"

val lemma_eq_state_hash_sub_slice:
  h: HyperStack.mem ->
  state :uint64_p {length state = v size_state /\ live h state} ->
  Lemma (as_seq h (Buffer.sub state pos_whash_w size_whash_w) == (Seq.slice (as_seq h state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w))))

#reset-options "--max_fuel 0  --z3rlimit 150"

let lemma_eq_state_hash_sub_slice h state =
  Seq.lemma_eq_intro (as_seq h (Buffer.sub state pos_whash_w size_whash_w))
                      (Seq.slice (as_seq h state) (U32.v pos_whash_w) (U32.(v pos_whash_w + v size_whash_w)))
