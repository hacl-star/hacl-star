module Hacl.Impl.Chacha20_vec2

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
open Hacl.Impl.Chacha20_state2

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

let idx = a:U32.t{U32.v a < 4}

[@ CInline]
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st))
[@ CInline]
let line st a b d s =
  let sa = st.(a) in
  let sb = st.(b) in
  let sd = st.(d) in
  let sa = sa +%^ sb in
  let sd = (sd ^^ sa) <<< s in
  st.(a) <- sa;
  st.(d) <- sd


[@ CInline]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ CInline]
let column_round st =
  line st 0ul 4ul 12ul 16ul;
  line st 1ul 5ul 13ul 16ul;
  line st 2ul 6ul 14ul 16ul;
  line st 3ul 7ul 15ul 16ul;

  line st 8ul 12ul 4ul 12ul;
  line st 9ul 13ul 5ul 12ul;
  line st 10ul 14ul 6ul 12ul;
  line st 11ul 15ul 7ul 12ul;

  line st 0ul 4ul 12ul 8ul;
  line st 1ul 5ul 13ul 8ul;
  line st 2ul 6ul 14ul 8ul;
  line st 3ul 7ul 15ul 8ul;

  line st 8ul 12ul 4ul 7ul;
  line st 9ul 13ul 5ul 7ul;
  line st 10ul 14ul 6ul 7ul;
  line st 11ul 15ul 7ul 7ul

[@ Substitute]
val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let diagonal_round st =
  line st 0ul 5ul 15ul 16ul;
  line st 1ul 6ul 12ul 16ul;
  line st 2ul 7ul 13ul 16ul;
  line st 3ul 4ul 14ul 16ul;

  line st 10ul 15ul 5ul 12ul;
  line st 11ul 12ul 6ul 12ul;
  line st 8ul 13ul 7ul 12ul;
  line st 9ul 14ul 4ul 12ul;

  line st 0ul 5ul 15ul 8ul;
  line st 1ul 6ul 12ul 8ul;
  line st 2ul 7ul 13ul 8ul;
  line st 3ul 4ul 14ul 8ul;

  line st 10ul 15ul 5ul 7ul;
  line st 11ul 12ul 6ul 7ul;
  line st 8ul 13ul 7ul 7ul;
  line st 9ul 14ul 4ul 7ul

[@ CInline]
val double_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ CInline]
let double_round st =
    column_round st;
    diagonal_round st

#reset-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 100"

[@ Substitute]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let rounds st = Loops_vec.rounds16 st
// Real implementation bellow
  (* Combinators.iter #H32.t #16 #(double_round') 10ul double_round st 16ul *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


[@ CInline]
val sum_states:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h1 st' /\ live h1 st /\ modifies_1 st' h0 h1))
[@ CInline]
let sum_states st' st =
    Loops_vec.sum_states16 st' st

[@ CInline]
val copy_state:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st' h0 h1))
[@ CInline]
let copy_state st' st =
    Loops_vec.copy_state16 st' st


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> (* c:Spec.counter -> *) log_t_
type log_t = Ghost.erased log_t_



[@ CInline]
val chacha20_core:
  k:state ->
  st:state ->
  Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k /\ live h1 st /\ modifies_1 k h0 h1))
[@ CInline]
let chacha20_core k st =
  copy_state k st;
  rounds k;
  sum_states k st


[@ CInline]
val chacha20_block:
  stream_block:uint8_p{length stream_block = 16 * U32.v vecsizebytes} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ modifies_1 stream_block h0 h1))
[@ CInline]
let chacha20_block stream_block st =
  push_frame();
  let k = state_alloc() in
  chacha20_core k st;
  state_to_key_block stream_block k;
  pop_frame()


[@ CInline]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  Stack unit
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1))
[@ CInline]
let init st k n =
  state_setup st k n 0ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 16 * U32.v vecsizebytes /\ U32.v len > 0} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update_last output plain len st =
  push_frame();
  let block = create (uint8_to_sint8 0uy) U32.(16ul *^ vecsizebytes) in
  chacha20_block block st;
  let mask = Buffer.sub block 0ul len in
  Loops_vec.xor_bytes output plain mask len;
  pop_frame()

val xor_block:
  output:uint8_p{length output = 16 * U32.v vecsizebytes} ->
  plain:uint8_p{disjoint output plain /\ length plain = 16 * U32.v vecsizebytes} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_2 st output h0 h1))
let xor_block output plain st =
  state_to_key st;
  Loops_vec.vec_xor16 output plain st vecsizebytes

val update:
  output:uint8_p{length output = 16 * U32.v vecsizebytes} ->
  plain:uint8_p{disjoint output plain /\ length plain = 16 * U32.v vecsizebytes} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update output plain st =
  let h0 = ST.get() in
  push_frame();
  let k = state_alloc() in
  chacha20_core k st;
  xor_block output plain k;
  state_incr st;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 300"

val chacha20_counter_mode_:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 16 * U32.v vecsizebytes} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1))
let rec chacha20_counter_mode_ output plain len st =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
     ()
  ) else  (
     update_last output plain len st
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val chacha20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let rec chacha20_counter_mode output plain len st ctr =
  let h0 = ST.get() in
  let bs = U32.(16ul *^ vecsizebytes) in
  if U32.(len <^ bs) then chacha20_counter_mode_ output plain len st
  else (
    let b  = Buffer.sub plain 0ul bs in
    let b' = Buffer.offset plain bs in
    let o  = Buffer.sub output 0ul bs in
    let o' = Buffer.offset output bs in
    update o b st;
    let h = ST.get() in
    let l = chacha20_counter_mode o' b' U32.(len -^ bs) st U32.(ctr +^ blocks) in
    let h' = ST.get() in
    ())

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val chacha20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 12} ->
  ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1))
let chacha20 output plain len k n ctr =
  push_frame();
  let st = state_alloc () in
  state_setup st k n ctr;
  chacha20_counter_mode output plain len st ctr;
  pop_frame()(* ; *)
