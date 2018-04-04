module Hacl.Impl.Chacha20_state

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Chacha20
open C.Loops

module Spec = Spec.Chacha20
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
open Hacl.UInt32x4N

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer vec{length b = 4}
unfold let blocks = U32.(vec_size /^ 4ul)
unfold let vecsizebytes = U32.(vec_size *^ 4ul)

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

[@ CInline]
val state_alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unused_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip
      /\ Map.domain h1.h == Map.domain h0.h))
[@ CInline]
let state_alloc () =
  create zero 4ul


[@ CInline]
val state_incr:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_incr k =
    let k3 = k.(3ul) in
    if (blocks = 2ul) then (
    k.(3ul) <- vec_add k3 two_le
    )
    else (
    k.(3ul) <- vec_add k3 one_le
    )

[@ CInline]
val state_to_key:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_to_key k =
    if (blocks = 2ul) then (
    let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    k.(0ul) <- vec_choose_128 k0 k1 0ul 2ul;
    k.(1ul) <- vec_choose_128 k2 k3 0ul 2ul;
    k.(2ul) <- vec_choose_128 k0 k1 1ul 3ul;
    k.(3ul) <- vec_choose_128 k2 k3 1ul 3ul)
    else ()

[@ CInline]
val state_to_key_block:
    stream_block:uint8_p{length stream_block = 64 * U32.v blocks} ->
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_to_key_block stream_block k =
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
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
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
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@ Substitute]
let constant_setup st =
  constant_setup_ st

[@ Substitute]
val keysetup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  Stack unit
    (requires (fun h -> live h st /\ live h k))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h0 k /\ live h1 st /\ modifies_1 st h0 h1))
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
  StackInline unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv))
[@ Substitute]
let ctr_ivsetup st ctr iv =
  let n0 = load32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = load32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = load32_le (Buffer.sub iv 8ul 4ul) in
  let v =  vec_load_32x8 ctr n0 n1 n2 U32.(ctr +^ 1ul) n0 n1 n2 in

(*      if (vec_size = 8ul) then
        else vec_load_32x4 ctr n0 n1 n2  *)

  st.(3ul) <- v

[@ CInline]
val state_setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  c:U32.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1))
[@ CInline]
let state_setup st k n c =
  constant_setup st;
  keysetup st k;
  ctr_ivsetup st c n


