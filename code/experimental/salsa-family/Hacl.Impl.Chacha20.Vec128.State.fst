module Hacl.Impl.Chacha20.Vec128.State

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20_vec
open C.Loops

module Spec = Spec.Chacha20
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

open Hacl.UInt32x4

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer vec{length b = 4}
let blocks = U32.(vec_size /^ 4ul)
let vecsizebytes = U32.(vec_size *^ 4ul)

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "c_inline"]
val state_alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h))
[@ "c_inline"]
let state_alloc () =
  create zero 4ul


[@ "c_inline"]
val state_incr:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1 /\ live h0 k /\
        (let st0 = as_seq h0 k in
         let st1 = as_seq h1 k in
         let op_String_Access = Seq.index in
         st1.[0] == st0.[0] /\
         st1.[1] == st0.[1] /\
         st1.[2] == st0.[2] /\
         vec_as_seq st1.[3] == (Spec.Chacha20_vec.op_Plus_Percent_Hat (vec_as_seq st0.[3])) (vec_as_seq one_le))))
[@ "c_inline"]
let state_incr k =
    let k3 = k.(3ul) in
    k.(3ul) <- vec_add k3 one_le

[@ "c_inline"]
val state_to_key:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> h0 == h1))
[@ "c_inline"]
let state_to_key k = ()


[@ "c_inline"]
val state_to_key_block:
    stream_block:uint8_p{length stream_block = 64 * U32.v blocks} ->
    k:state{disjoint k stream_block} ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h0 k /\ modifies_1 k h0 h1 /\ live h1 stream_block /\
        (let stream_block = as_seq h1 stream_block in
         let k = as_seq h0 k in
         let op_String_Access = Seq.index in
         stream_block == FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[0]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[1]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[2]) @|
                                    Spec.Lib.uint32s_to_le 4 (vec_as_seq k.[3])))))
[@ "c_inline"]
let state_to_key_block stream_block k =
  admit();
  state_to_key k;
  let bb = U32.(blocks *^ 16ul) in
  let bb2 = U32.(bb *^ 2ul) in
  let bb3 = U32.(bb *^ 3ul) in
  let k0 = k.(0ul) in
  let k1 = k.(1ul) in
  let k2 = k.(2ul) in
  let k3 = k.(3ul) in
  vec_store_le (Buffer.sub stream_block 0ul bb) k.(0ul);
  vec_store_le (Buffer.sub stream_block bb  16ul) k.(1ul);
  vec_store_le (Buffer.sub stream_block bb2 16ul) k.(2ul);
  vec_store_le (Buffer.sub stream_block bb3 16ul) k.(3ul)


[@ "substitute"]
val constant_setup_:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c /\
      (let st0 = as_seq h0 c in let st1 = as_seq h1 c in let op_String_Access = Seq.index in
       let open Spec.Chacha20_vec in let open FStar.Seq in
       vec_as_seq st1.[0] == Seq.Create.create_4 c0 c1 c2 c3 /\
       st0.[1] == st1.[1] /\ st0.[2] == st1.[2] /\ st0.[3] == st1.[3])))
[@ "substitute"]
let constant_setup_ st =
  st.(0ul)  <- vec_load_32x4 (uint32_to_sint32 0x61707865ul)
  	       		     (uint32_to_sint32 0x3320646eul)
			     (uint32_to_sint32 0x79622d32ul)
			     (uint32_to_sint32 0x6b206574ul)


[@ "substitute"]
val constant_setup:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c /\
      (let st0 = as_seq h0 c in let st1 = as_seq h1 c in let op_String_Access = Seq.index in
       let open Spec.Chacha20_vec in let open FStar.Seq in
       vec_as_seq st1.[0] == Seq.Create.create_4 c0 c1 c2 c3 /\
       st0.[1] == st1.[1] /\ st0.[2] == st1.[2] /\ st0.[3] == st1.[3])))
[@ "substitute"]
let constant_setup st =
  constant_setup_ st


[@ "substitute"]
val keysetup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1 /\
      (let st0 = as_seq h0 st in let st1 = as_seq h1 st in let op_String_Access = Seq.index in
       st1.[0] == st0.[0] /\
       st1.[3] == st0.[3] /\
       vec_as_seq st1.[1] == Spec.Lib.uint32s_from_le 4 (Seq.slice (as_seq h0 k) 0 16) /\
       vec_as_seq st1.[2] == Spec.Lib.uint32s_from_le 4 (Seq.slice (as_seq h0 k) 16 32)
       )))
[@ "substitute"]
let keysetup st k =
  let k0 = vec_load128_le (Buffer.sub k 0ul 16ul) in
  let k1 = vec_load128_le (Buffer.sub k 16ul 16ul) in
  st.(1ul) <- k0;
  st.(2ul) <- k1


[@ "substitute"]
val ctr_ivsetup:
  st:state ->
  ctr:U32.t ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  Stack unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv /\ live h0 st /\
      (let st0 = as_seq h0 st in let st1 = as_seq h1 st in let op_String_Access = Seq.index in
       st1.[0] == st0.[0] /\
       st1.[1] == st0.[1] /\
       st1.[2] == st0.[2] /\
       vec_as_seq st1.[3] == Seq.cons ctr (Spec.Lib.uint32s_from_le 3 (as_seq h0 iv))) ))
[@ "substitute"]
let ctr_ivsetup st ctr iv =
  let n0 = load32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = load32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = load32_le (Buffer.sub iv 8ul 4ul) in
  let h = ST.get() in
  assume (Seq.index (Spec.Lib.uint32s_from_le 3 (as_seq h iv)) 0 == n0);
  assume (Seq.index (Spec.Lib.uint32s_from_le 3 (as_seq h iv)) 1 == n1);
  assume (Seq.index (Spec.Lib.uint32s_from_le 3 (as_seq h iv)) 2 == n2);
  let v =  vec_load_32x4 ctr n0 n1 n2 in
  Seq.lemma_eq_intro (Seq.slice (vec_as_seq v) 1 4) (Spec.Lib.uint32s_from_le 3 (as_seq h iv));
  Seq.lemma_eq_intro (vec_as_seq v) (Seq.cons ctr (Spec.Lib.uint32s_from_le 3 (as_seq h iv)));
  st.(3ul) <- v


[@ "c_inline"]
val state_setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1 /\
      (let st = as_seq h1 st in
       let op_String_Access = Seq.index in
       Seq.Create.create_4 (vec_as_seq st.[0]) (vec_as_seq st.[1]) (vec_as_seq st.[2]) (vec_as_seq st.[3])
       == Spec.Chacha20_vec.setup (as_seq h0 k) (as_seq h0 n) (U32.v c))))
[@ "c_inline"]
let state_setup st k n c =
  let h0 = ST.get() in
  constant_setup st;
  keysetup st k;
  ctr_ivsetup st c n;
  let h = ST.get() in
  Seq.lemma_eq_intro (let st = as_seq h st in
                     let op_String_Access = Seq.index in
                     Seq.Create.create_4 (vec_as_seq st.[0]) (vec_as_seq st.[1])
                                         (vec_as_seq st.[2]) (vec_as_seq st.[3]))
                     (Spec.Chacha20_vec.setup (as_seq h0 k) (as_seq h0 n) (U32.v c))
