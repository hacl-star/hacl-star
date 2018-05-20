module Hacl.Impl.Chacha20_vec

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness
(* open Spec.Chacha20 *)
open C.Loops

module Spec = Spec.Chacha20_vec256
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
open Hacl.UInt32x4N
open Hacl.Impl.Chacha20_state

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

unfold let vecsizebytes2 = U32.(vecsizebytes *^ 2ul)
unfold let vecsizebytes3 = U32.(vecsizebytes *^ 3ul)
unfold let vecsizebytes4 = U32.(vecsizebytes *^ 4ul)
unfold let vecsizebytes8 = U32.(vecsizebytes *^ 8ul)
unfold let vecsizebytes12 = U32.(vecsizebytes *^ 12ul)

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
val round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ CInline]
let round st =
  line st 0ul 1ul 3ul 16ul;
  line st 2ul 3ul 1ul 12ul;
  line st 0ul 1ul 3ul 8ul ;
  line st 2ul 3ul 1ul 7ul


[@ Substitute]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let column_round st = round st

[@ Substitute]
val shuffle_rows_0123:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let shuffle_rows_0123 st =
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 1ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 3ul

[@ Substitute]
val shuffle_rows_0321:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let shuffle_rows_0321 st =
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 3ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 1ul

[@ Substitute]
val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1))
[@ Substitute]
let diagonal_round st =
  shuffle_rows_0123 st;
  round st;
  shuffle_rows_0321 st


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
let rounds st =
  repeat #vec 16ul (Spec.Chacha20_vec256.double_round) st 10ul double_round

[@ Substitute]
val rounds2:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st'
      /\ live h1 st /\ live h1 st' /\ modifies_2 st st' h0 h1))
[@ Substitute]
let rounds2 st st' =
  let h0 = ST.get() in
  let inv (h1:mem) (i:nat) : Type0 =
    live h1 st /\ live h1 st' /\ i <= 10
    /\ as_seq h1 st == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st)
    /\ as_seq h1 st' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st') in
  let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < 10)}) : Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h0 _ h1 -> FStar.UInt32.(inv h1 (v i + 1)))) =
      double_round st;
      double_round st' in
  for 0ul 10ul inv f

[@ Substitute]
val rounds3:
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st'' /\ disjoint st' st''} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st' /\ live h st''))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st' /\ live h0 st''
      /\ live h1 st /\ live h1 st' /\ live h1 st'' /\ modifies_3 st st' st'' h0 h1))
[@ Substitute]
let rounds3 st st' st'' =
  let h0 = ST.get() in
  let inv (h1:mem) (i:nat) : Type0 =
    live h1 st /\ live h1 st' /\ live h1 st'' /\ i <= 10
    /\ as_seq h1 st == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st)
    /\ as_seq h1 st' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st')
    /\ as_seq h1 st'' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st'') in
  let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < 10)}) : Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h0 _ h1 -> FStar.UInt32.(inv h1 (v i + 1)))) =
      double_round st;
      double_round st';
      double_round st'' in
  for 0ul 10ul inv f


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
  let s0 = st.(0ul) in
  let s1 = st.(1ul) in
  let s2 = st.(2ul) in
  let s3 = st.(3ul) in
  let s0' = st'.(0ul) in
  let s1' = st'.(1ul) in
  let s2' = st'.(2ul) in
  let s3' = st'.(3ul) in
  st'.(0ul) <- s0' +%^ s0;
  st'.(1ul) <- s1' +%^ s1;
  st'.(2ul) <- s2' +%^ s2;
  st'.(3ul) <- s3' +%^ s3


[@ CInline]
val copy_state:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st' h0 h1))
[@ CInline]
let copy_state st' st =
  st'.(0ul) <- st.(0ul);
  st'.(1ul) <- st.(1ul);
  st'.(2ul) <- st.(2ul);
  st'.(3ul) <- st.(3ul)


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
val chacha20_core2:
  k0:state ->
  k1:state ->
  st:state ->
  Stack unit
    (requires (fun h -> live h k0 /\ live h k1 /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 st /\ modifies_3 st k0 k1 h0 h1))
[@ CInline]
let chacha20_core2 k0 k1 st =
  copy_state k0 st;
  copy_state k1 st;
  state_incr k1;
  rounds2 k0 k1;
  sum_states k0 st;
  state_incr st;
  sum_states k1 st

[@ CInline]
val chacha20_core3:
  k0:state ->
  k1:state ->
  k2:state ->
  st:state ->
  Stack unit
    (requires (fun h -> live h k0 /\ live h k1 /\ live h k2 /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 k2 /\ live h1 st /\ modifies_3 st k0 k1 h0 h1 ))
[@ CInline]
let chacha20_core3 k0 k1 k2 st =
  copy_state k0 st;
  copy_state k1 st;
  state_incr k1;
  copy_state k2 k1;
  state_incr k2;
  rounds3 k0 k1 k2;
  sum_states k0 st;
  state_incr st;
  sum_states k1 st;
  state_incr st;
  sum_states k2 st

[@ CInline]
val chacha20_block:
  stream_block:uint8_p{length stream_block = U32.v vecsizebytes4} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ modifies_1 stream_block h0 h1))
[@ CInline]
let chacha20_block stream_block st =
  push_frame();
  let k = Buffer.create zero 4ul in
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
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= U32.v vecsizebytes4 /\ U32.v len > 0} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update_last output plain len st =
  push_frame();
  let block = create (uint8_to_sint8 0uy) vecsizebytes4 in
  chacha20_block block st;
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (Hacl.UInt8.logxor);
  (* Loops_vec.xor_bytes output plain mask len; *)
  pop_frame()

val xor_block:
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_2 st output h0 h1))
let xor_block output plain st =
  state_to_key st;
  let p0 = vec_load_le (Buffer.sub plain 0ul vecsizebytes) in
  let p1 = vec_load_le (Buffer.sub plain vecsizebytes vecsizebytes) in
  let p2 = vec_load_le (Buffer.sub plain vecsizebytes2 vecsizebytes) in
  let p3 = vec_load_le (Buffer.sub plain vecsizebytes3 vecsizebytes) in
  let k0 = st.(0ul) in
  let k1 = st.(1ul) in
  let k2 = st.(2ul) in
  let k3 = st.(3ul) in
  let o0 = vec_xor p0 k0 in
  let o1 = vec_xor p1 k1 in
  let o2 = vec_xor p2 k2 in
  let o3 = vec_xor p3 k3 in
  vec_store_le (Buffer.sub output 0ul  vecsizebytes) o0;
  vec_store_le (Buffer.sub output vecsizebytes vecsizebytes) o1;
  vec_store_le (Buffer.sub output vecsizebytes2 vecsizebytes) o2;
  vec_store_le (Buffer.sub output vecsizebytes3 vecsizebytes) o3

val update:
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update output plain st =
  let h0 = ST.get() in
  push_frame();
  let k = Buffer.create zero 4ul in
  chacha20_core k st;
  xor_block output plain k;
  state_incr st;
  pop_frame()

val update2:
  output:uint8_p{length output = U32.v vecsizebytes8} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes8} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update2 output plain st =
  let h0 = ST.get() in
  push_frame();
  let k = Buffer.create zero 4ul in
  let k' = Buffer.create zero 4ul in
  chacha20_core2 k k' st;
  xor_block output plain k;
  xor_block (Buffer.offset output vecsizebytes4) (Buffer.offset plain vecsizebytes4) k';
  state_incr st;
  pop_frame()

val update3:
  output:uint8_p{length output = U32.v vecsizebytes12} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes12} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update3 output plain st =
  let h0 = ST.get() in
  push_frame();
  let k0 = Buffer.create zero 4ul in
  let k1 = Buffer.create zero 4ul in
  let k2 = Buffer.create zero 4ul in
  chacha20_core3 k0 k1 k2 st;
  xor_block output plain k0;
  xor_block (Buffer.offset output vecsizebytes4) (Buffer.offset plain vecsizebytes4) k1;
  xor_block (Buffer.offset output vecsizebytes8) (Buffer.offset plain vecsizebytes8) k2;
  state_incr st;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 300"

val chacha20_counter_mode_:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= U32.v vecsizebytes4} ->
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
  let bs = vecsizebytes4 in
  let bs2 = U32.(bs *^ 2ul) in
  let bs3 = U32.(bs *^ 3ul) in
  if U32.(len <^ bs) then chacha20_counter_mode_ output plain len st
  else
  if U32.(len <^ bs2) then (
    let b  = Buffer.sub plain 0ul bs in
    let b' = Buffer.offset plain bs in
    let o  = Buffer.sub output 0ul bs in
    let o' = Buffer.offset output bs in
    update o b st;
    let h = ST.get() in
    let l = chacha20_counter_mode o' b' U32.(len -^ bs) st U32.(ctr +^ blocks) in
    let h' = ST.get() in
    ())
  else
  if U32.(len <^ bs3) then (
    let b  = Buffer.sub plain 0ul bs2 in
    let b' = Buffer.offset plain bs2 in
    let o  = Buffer.sub output 0ul bs2 in
    let o' = Buffer.offset output bs2 in
    update2 o b st;
    let h = ST.get() in
    let l = chacha20_counter_mode o' b' U32.(len -^ bs2) st U32.(ctr +^ (2ul *^ blocks)) in
    let h' = ST.get() in
    ())
  else (
    let b  = Buffer.sub plain 0ul bs3 in
    let b' = Buffer.offset plain bs3 in
    let o  = Buffer.sub output 0ul bs3 in
    let o' = Buffer.offset output bs3 in
    update3 o b st;
    let h = ST.get() in
    let l = chacha20_counter_mode o' b' U32.(len -^ bs3) st U32.(ctr +^ (3ul *^ blocks)) in
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
