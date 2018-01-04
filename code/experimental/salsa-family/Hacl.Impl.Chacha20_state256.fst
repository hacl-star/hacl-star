module Hacl.Impl.Chacha20_state256

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20_vec256
open C.Loops
open Vec256

module Spec = Spec.Chacha20_vec256
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer vec{length b = 4}

let blocks = 2ul
let vecsizebytes = 8ul

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

[@ CInline]
val state_alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h
      /\ (let s = as_seq h1 st in
         Seq.index s 0 == zero /\ Seq.index s 1 == zero
         /\ Seq.index s 2 == zero /\ Seq.index s 3 == zero)
      ))
[@ CInline]
let state_alloc () =
  create zero 4ul


[@ CInline]
val state_incr:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1 /\ live h0 k /\
        (let k0 = as_seq h0 k in let k1 = as_seq h1 k in
         k1 == Seq.upd k0 3 (vec_add (Seq.index k0 3) two_le))))
[@ CInline]
let state_incr k =
    let k3 = k.(3ul) in
    k.(3ul) <- vec_add k3 two_le


[@ CInline]
val state_to_key:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_to_key k =
    let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    k.(0ul) <- vec_choose_128 k0 k1 0ul 2ul;
    k.(1ul) <- vec_choose_128 k2 k3 0ul 2ul;
    k.(2ul) <- vec_choose_128 k0 k1 1ul 3ul;
    k.(3ul) <- vec_choose_128 k2 k3 1ul 3ul




[@ CInline]
val state_to_key_block:
    stream_block:uint8_p{length stream_block = 128} ->
    k:state ->
    Stack unit
      (requires (fun h -> live h k /\ live h stream_block))
      (ensures  (fun h0 _ h1 -> live h0 k /\ live h0 stream_block
        /\ live h1 k /\ modifies_1 k h0 h1 /\ live h1 stream_block
        /\ (as_seq h1 stream_block == Spec.flush (as_seq h0 k))))
[@ CInline]
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


[@ Substitute]
val constant_setup_:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c
      /\ Seq.index (as_seq h1 c) 0 == vec_load_32x4 0x61707865ul 0x3320646eul 0x79622d32ul 0x6b206574ul
      /\ Seq.index (as_seq h1 c) 1 == Seq.index (as_seq h0 c) 1
      /\ Seq.index (as_seq h1 c) 2 == Seq.index (as_seq h0 c) 2
      /\ Seq.index (as_seq h1 c) 3 == Seq.index (as_seq h0 c) 3
    ))
[@ Substitute]
let constant_setup_ st =
  st.(0ul)  <- vec_load_32x4 (uint32_to_sint32 0x61707865ul)
  	       		     (uint32_to_sint32 0x3320646eul)
			     (uint32_to_sint32 0x79622d32ul)
			     (uint32_to_sint32 0x6b206574ul)


[@ Substitute]
val constant_setup:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1 /\ live h0 c
      /\ Seq.index (as_seq h1 c) 0 == vec_load_32x4 0x61707865ul 0x3320646eul 0x79622d32ul 0x6b206574ul
      /\ Seq.index (as_seq h1 c) 1 == Seq.index (as_seq h0 c) 1
      /\ Seq.index (as_seq h1 c) 2 == Seq.index (as_seq h0 c) 2
      /\ Seq.index (as_seq h1 c) 3 == Seq.index (as_seq h0 c) 3
    ))
[@ Substitute]
let constant_setup st =
  constant_setup_ st


[@ Substitute]
val keysetup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1 /\
      (let k0 = Seq.slice (as_seq h0 k) 0 16 in
       let k1 = Seq.slice (as_seq h0 k) 16 32 in
       let v0 = Spec.Lib.uint32s_from_le 4 k0 in
       let v1 = Spec.Lib.uint32s_from_le 4 k1 in
       (vec_as_seq (Seq.index (as_seq h1 st) 1) == Seq.append v0 v0
       /\ vec_as_seq (Seq.index (as_seq h1 st) 2) == Seq.append v1 v1
       /\ Seq.index (as_seq h1 st) 0 == Seq.index (as_seq h0 st) 0
       /\ Seq.index (as_seq h1 st) 3 == Seq.index (as_seq h0 st) 3)
    )))
[@ Substitute]
let keysetup st k =
  let k0 = vec_load128_le (Buffer.sub k 0ul 16ul) in
  let k1 = vec_load128_le (Buffer.sub k 16ul 16ul) in
  st.(1ul) <- k0;
  st.(2ul) <- k1


[@ Substitute]
val ctr_ivsetup:
  st:state ->
  ctr:U32.t ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  Stack unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv /\ live h0 st
      /\ (let n0 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub iv 0ul 4ul)) in
         let n1 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub iv 4ul 4ul)) in
         let n2 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub iv 8ul 4ul)) in
         Seq.index (as_seq h1 st) 3 == vec_load_32x8 ctr n0 n1 n2 FStar.UInt32.(ctr +%^ 1ul) n0 n1 n2
         /\ Seq.index (as_seq h1 st) 0 == Seq.index (as_seq h0 st) 0
         /\ Seq.index (as_seq h1 st) 1 == Seq.index (as_seq h0 st) 1
         /\ Seq.index (as_seq h1 st) 2 == Seq.index (as_seq h0 st) 2
         )
    ))
[@ Substitute]
let ctr_ivsetup st ctr iv =
  let n0 = load32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = load32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = load32_le (Buffer.sub iv 8ul 4ul) in
  let v =  vec_load_32x8 ctr n0 n1 n2 U32.(ctr +%^ 1ul) n0 n1 n2 in
  st.(3ul) <- v


[@ CInline]
val state_setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let n0 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub n 0ul 4ul)) in
         let n1 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub n 4ul 4ul)) in
         let n2 = Spec.Lib.uint32_from_le (as_seq h0 (Buffer.sub n 8ul 4ul)) in
         let k0 = Seq.slice (as_seq h0 k) 0 16 in
         let k1 = Seq.slice (as_seq h0 k) 16 32 in
         let v0 = Spec.Lib.uint32s_from_le 4 k0 in
         let v1 = Spec.Lib.uint32s_from_le 4 k1 in
       Seq.index (as_seq h1 st) 0 == vec_load_32x4 0x61707865ul 0x3320646eul 0x79622d32ul 0x6b206574ul
       /\ vec_as_seq (Seq.index (as_seq h1 st) 1) == Seq.append v0 v0
       /\ vec_as_seq (Seq.index (as_seq h1 st) 2) == Seq.append v1 v1
       /\ Seq.index (as_seq h1 st) 3 == vec_load_32x8 c n0 n1 n2 FStar.UInt32.(c +%^ 1ul) n0 n1 n2)
    ))
[@ CInline]
let state_setup st k n c =
  constant_setup st;
  keysetup st k;
  ctr_ivsetup st c n
