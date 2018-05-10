module Hacl.Impl.Chacha20_state2

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

type state = b:Buffer.buffer vec{length b = 16}
unfold let blocks = vec_size
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
  create zero 16ul


[@ CInline]
val state_incr:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_incr k =
    let k12 = k.(12ul) in
    let step = vec_load_32 blocks in
    k.(12ul) <- vec_add k12 step

[@ CInline]
val state_to_key:
    k:state ->
    Stack unit
      (requires (fun h -> live h k))
      (ensures  (fun h0 _ h1 -> live h1 k /\ modifies_1 k h0 h1))
[@ CInline]
let state_to_key k =
  if (vec_size = 8ul) then (
    let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    let k4 = k.(4ul) in
    let k5 = k.(5ul) in
    let k6 = k.(6ul) in
    let k7 = k.(7ul) in
    let k8 = k.(8ul) in
    let k9 = k.(9ul) in
    let k10 = k.(10ul) in
    let k11 = k.(11ul) in
    let k12 = k.(12ul) in
    let k13 = k.(13ul) in
    let k14 = k.(14ul) in
    let k15 = k.(15ul) in

    let k01l = vec_interleave32_low k0 k1 in
    let k23l = vec_interleave32_low k2 k3 in
    let k45l = vec_interleave32_low k4 k5 in
    let k67l = vec_interleave32_low k6 k7 in
    let k89l = vec_interleave32_low k8 k9 in
    let k1011l = vec_interleave32_low k10 k11 in
    let k1213l = vec_interleave32_low k12 k13 in
    let k1415l = vec_interleave32_low k14 k15 in

    let k03_1 = vec_interleave64_low k01l k23l in
    let k47_1 = vec_interleave64_low k45l k67l in
    let k07_0 = vec_choose_128 k03_1 k47_1 0ul 2ul in
    let k07_4 = vec_choose_128 k03_1 k47_1 1ul 3ul in

    let k03_2 = vec_interleave64_high k01l k23l in
    let k47_2 = vec_interleave64_high k45l k67l in
    let k07_1 = vec_choose_128 k03_2 k47_2 0ul 2ul in
    let k07_5 = vec_choose_128 k03_2 k47_2 1ul 3ul in

    let k811_1 = vec_interleave64_low k89l k1011l in
    let k1215_1 = vec_interleave64_low k1213l k1415l in
    let k815_0 = vec_choose_128 k811_1 k1215_1 0ul 2ul in
    let k815_4 = vec_choose_128 k811_1 k1215_1 1ul 3ul in

    let k811_2 = vec_interleave64_high k89l k1011l in
    let k1215_2 = vec_interleave64_high k1213l k1415l in
    let k815_1 = vec_choose_128 k811_2 k1215_2 0ul 2ul in
    let k815_5 = vec_choose_128 k811_2 k1215_2 1ul 3ul in

    let k01h = vec_interleave32_high k0 k1 in
    let k23h = vec_interleave32_high k2 k3 in
    let k45h = vec_interleave32_high k4 k5 in
    let k67h = vec_interleave32_high k6 k7 in
    let k89h = vec_interleave32_high k8 k9 in
    let k1011h = vec_interleave32_high k10 k11 in
    let k1213h = vec_interleave32_high k12 k13 in
    let k1415h = vec_interleave32_high k14 k15 in

    let k03_3 = vec_interleave64_low k01h k23h in
    let k47_3 = vec_interleave64_low k45h k67h in
    let k07_2 = vec_choose_128 k03_3 k47_3 0ul 2ul in
    let k07_6 = vec_choose_128 k03_3 k47_3 1ul 3ul in

    let k03_4 = vec_interleave64_high k01h k23h in
    let k47_4 = vec_interleave64_high k45h k67h in
    let k07_3 = vec_choose_128 k03_4 k47_4 0ul 2ul in
    let k07_7 = vec_choose_128 k03_4 k47_4 1ul 3ul in

    let k811_3 = vec_interleave64_low k89h k1011h in
    let k1215_3 = vec_interleave64_low k1213h k1415h in
    let k815_2 = vec_choose_128 k811_3 k1215_3 0ul 2ul in
    let k815_6 = vec_choose_128 k811_3 k1215_3 1ul 3ul in

    let k811_4 = vec_interleave64_high k89h k1011h in
    let k1215_4 = vec_interleave64_high k1213h k1415h in
    let k815_3 = vec_choose_128 k811_4 k1215_4 0ul 2ul in
    let k815_7 = vec_choose_128 k811_4 k1215_4 1ul 3ul in

    k.(0ul) <- k07_0;
    k.(1ul) <- k815_0;
    k.(2ul) <- k07_1;
    k.(3ul) <- k815_1;
    k.(4ul) <- k07_2;
    k.(5ul) <- k815_2;
    k.(6ul) <- k07_3;
    k.(7ul) <- k815_3;
    k.(8ul) <- k07_4;
    k.(9ul) <- k815_4;
    k.(10ul) <- k07_5;
    k.(11ul) <- k815_5;
    k.(12ul) <- k07_6;
    k.(13ul) <- k815_6;
    k.(14ul) <- k07_7;
    k.(15ul) <- k815_7
  ) else
  if (vec_size = 4ul) then  (
   let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    let k4 = k.(4ul) in
    let k5 = k.(5ul) in
    let k6 = k.(6ul) in
    let k7 = k.(7ul) in
    let k8 = k.(8ul) in
    let k9 = k.(9ul) in
    let k10 = k.(10ul) in
    let k11 = k.(11ul) in
    let k12 = k.(12ul) in
    let k13 = k.(13ul) in
    let k14 = k.(14ul) in
    let k15 = k.(15ul) in

    let k01l = vec_interleave32_low k0 k1 in
    let k23l = vec_interleave32_low k2 k3 in
    let k45l = vec_interleave32_low k4 k5 in
    let k67l = vec_interleave32_low k6 k7 in
    let k89l = vec_interleave32_low k8 k9 in
    let k1011l = vec_interleave32_low k10 k11 in
    let k1213l = vec_interleave32_low k12 k13 in
    let k1415l = vec_interleave32_low k14 k15 in

    let k03_0 = vec_interleave64_low k01l k23l in
    let k47_0 = vec_interleave64_low k45l k67l in
    let k03_1 = vec_interleave64_high k01l k23l in
    let k47_1 = vec_interleave64_high k45l k67l in

    let k811_0 = vec_interleave64_low k89l k1011l in
    let k1215_0 = vec_interleave64_low k1213l k1415l in
    let k811_1 = vec_interleave64_high k89l k1011l in
    let k1215_1 = vec_interleave64_high k1213l k1415l in

    let k01h = vec_interleave32_high k0 k1 in
    let k23h = vec_interleave32_high k2 k3 in
    let k45h = vec_interleave32_high k4 k5 in
    let k67h = vec_interleave32_high k6 k7 in
    let k89h = vec_interleave32_high k8 k9 in
    let k1011h = vec_interleave32_high k10 k11 in
    let k1213h = vec_interleave32_high k12 k13 in
    let k1415h = vec_interleave32_high k14 k15 in

    let k03_2 = vec_interleave64_low k01h k23h in
    let k47_2 = vec_interleave64_low k45h k67h in
    let k03_3 = vec_interleave64_high k01h k23h in
    let k47_3 = vec_interleave64_high k45h k67h in

    let k811_2 = vec_interleave64_low k89h k1011h in
    let k1215_2 = vec_interleave64_low k1213h k1415h in
    let k811_3 = vec_interleave64_high k89h k1011h in
    let k1215_3 = vec_interleave64_high k1213h k1415h in

    k.(0ul) <- k03_0;
    k.(1ul) <- k47_0;
    k.(2ul) <- k811_0;
    k.(3ul) <- k1215_0;

    k.(4ul) <- k03_1;
    k.(5ul) <- k47_1;
    k.(6ul) <- k811_1;
    k.(7ul) <- k1215_1;

    k.(8ul) <- k03_2;
    k.(9ul) <- k47_2;
    k.(10ul) <- k811_2;
    k.(11ul) <- k1215_2;

    k.(12ul) <- k03_3;
    k.(13ul) <- k47_3;
    k.(14ul) <- k811_3;
    k.(15ul) <- k1215_3
  ) else ()

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
    Loops_vec.vec_store16 stream_block k vecsizebytes

[@ Substitute]
val constant_setup_:
  c:state ->
  Stack unit
    (requires (fun h -> live h c))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@ Substitute]
let constant_setup_ st =
  st.(0ul)  <- vec_load_32 (uint32_to_sint32 0x61707865ul);
  st.(1ul)  <- vec_load_32 (uint32_to_sint32 0x3320646eul);
  st.(2ul)  <- vec_load_32 (uint32_to_sint32 0x79622d32ul);
  st.(3ul)  <- vec_load_32 (uint32_to_sint32 0x6b206574ul)


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
  st.(4ul) <- vec_load_32 (load32_le (Buffer.sub k 0ul 4ul));
  st.(5ul) <- vec_load_32 (load32_le (Buffer.sub k 4ul 4ul));
  st.(6ul) <- vec_load_32 (load32_le (Buffer.sub k 8ul 4ul));
  st.(7ul) <- vec_load_32 (load32_le (Buffer.sub k 12ul 4ul));
  st.(8ul) <- vec_load_32 (load32_le (Buffer.sub k 16ul 4ul));
  st.(9ul) <- vec_load_32 (load32_le (Buffer.sub k 20ul 4ul));
  st.(10ul) <- vec_load_32 (load32_le (Buffer.sub k 24ul 4ul));
  st.(11ul) <- vec_load_32 (load32_le (Buffer.sub k 28ul 4ul))

[@ Substitute]
val ctrsetup:
  st:state ->
  ctr:U32.t ->
  StackInline unit
    (requires (fun h -> live h st))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let ctrsetup st ctr =
  let ctr = uint32_to_sint32 ctr in
  if (vec_size = 8ul) then
     st.(12ul) <- H32.(vec_load_32x8 ctr (ctr +^ 1ul) (ctr +^ 2ul) (ctr +^ 3ul) (ctr +^ 4ul) (ctr +^ 5ul) (ctr +^ 6ul) (ctr +^ 7ul))
  else if (vec_size = 4ul) then
     st.(12ul) <- H32.(vec_load_32x4 ctr (ctr +^ 1ul) (ctr +^ 2ul) (ctr +^ 3ul))
  else st.(12ul) <- vec_load_32 ctr


[@ Substitute]
val ivsetup:
  st:state ->
  iv:uint8_p{length iv = 12 /\ disjoint st iv} ->
  StackInline unit
    (requires (fun h -> live h st /\ live h iv))
    (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 iv))
[@ Substitute]
let ivsetup st iv =
  let n0 = load32_le (Buffer.sub iv 0ul 4ul) in
  let n1 = load32_le (Buffer.sub iv 4ul 4ul) in
  let n2 = load32_le (Buffer.sub iv 8ul 4ul) in
  st.(13ul) <- vec_load_32 n0;
  st.(14ul) <- vec_load_32 n1;
  st.(15ul) <- vec_load_32 n2

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
  ctrsetup st c;
  ivsetup st n


