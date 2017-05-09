module Hacl.Impl.Chacha20.Vec128

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness

open C.Loops

module Spec = Spec.Chacha20_vec
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
open Hacl.UInt32x4
open Hacl.Impl.Chacha20.Vec128.State

#reset-options "--max_fuel 0 --z3rlimit 100"

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

unfold let vecsizebytes2 = U32.(vecsizebytes *^ 2ul)
unfold let vecsizebytes3 = U32.(vecsizebytes *^ 3ul)
unfold let vecsizebytes4 = U32.(vecsizebytes *^ 4ul)
unfold let vecsizebytes8 = U32.(vecsizebytes *^ 8ul)
unfold let vecsizebytes12 = U32.(vecsizebytes *^ 12ul)

let idx = a:U32.t{U32.v a < 4}

val as_state: h:HyperStack.mem -> st:state{live h st} -> GTot Spec.state
let as_state h st =
  let st = as_seq h st in let op_String_Access = Seq.index in
  Seq.Create.create_4 (vec_as_seq (st.[0])) (vec_as_seq (st.[1])) (vec_as_seq (st.[2])) (vec_as_seq (st.[3]))

[@ "c_inline"]
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st /\
      as_state h1 st == Spec.line (U32.v a) (U32.v b) (U32.v d) s (as_state h0 st)
      ))
[@ "c_inline"]
let line st a b d s =
  let h0 = ST.get() in
  let sa = st.(a) in
  let sb = st.(b) in
  let sd = st.(d) in
  let sa = sa +%^ sb in
  let sd = (sd ^^ sa) <<< s in
  st.(a) <- sa;
  st.(d) <- sd;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st) (Spec.line (U32.v a) (U32.v b) (U32.v d) s (as_state h0 st))


[@ "c_inline"]
val round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.round (as_state h0 st)))
[@ "c_inline"]
let round st =
  let h0 = ST.get() in
  line st 0ul 1ul 3ul 16ul;
  line st 2ul 3ul 1ul 12ul;
  line st 0ul 1ul 3ul 8ul ;
  line st 2ul 3ul 1ul 7ul;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st) (Spec.round (as_state h0 st))


[@ "substitute"]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.column_round (as_state h0 st)))
[@ "substitute"]
let column_round st = round st

[@ "substitute"]
val shuffle_rows_0123:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.shuffle_rows_0123 (as_state h0 st)))
[@ "substitute"]
let shuffle_rows_0123 st =
  let h0 = ST.get() in
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 1ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 3ul;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st) (Spec.shuffle_rows_0123 (as_state h0 st))

[@ "substitute"]
val shuffle_rows_0321:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.shuffle_rows_0321 (as_state h0 st)))
[@ "substitute"]
let shuffle_rows_0321 st =
  let h0 = ST.get() in
    let r1 = st.(1ul) in
    let r2 = st.(2ul) in
    let r3 = st.(3ul) in
    st.(1ul) <-  vec_shuffle_right r1 3ul;
    st.(2ul) <-  vec_shuffle_right r2 2ul;
    st.(3ul) <-  vec_shuffle_right r3 1ul;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st) (Spec.shuffle_rows_0321 (as_state h0 st))

[@ "substitute"]
val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.diagonal_round (as_state h0 st)))
[@ "substitute"]
let diagonal_round st =
  shuffle_rows_0123 st;
  round st;
  shuffle_rows_0321 st


[@ "c_inline"]
val double_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.double_round (as_state h0 st)))
[@ "c_inline"]
let double_round st =
    column_round st;
    diagonal_round st

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "substitute"]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.rounds (as_state h0 st)))
[@ "substitute"]
let rounds st =
  let h0 = ST.get() in
  let inv (h1: HyperStack.mem) (i: nat): Type0 =
    live h1 st /\ modifies_1 st h0 h1 /\ i <= 10
    /\ as_state h1 st == repeat_spec i Spec.double_round (as_state h0 st)
  in
  let f' (i:UInt32.t{ U32.( 0 <= v i /\ v i < 10 ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> U32.(inv h_2 (v i + 1))))
  =
    double_round st;
    lemma_repeat (UInt32.v i + 1) Spec.double_round (as_state h0 st)
  in
  lemma_repeat_0 0 Spec.double_round (as_state h0 st);
  for 0ul 10ul inv f'


(* [@ "substitute"] *)
(* val rounds2: *)
(*   st:state -> *)
(*   st':state{disjoint st st'} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h st /\ live h st')) *)
(*     (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st' *)
(*       /\ live h1 st /\ live h1 st' /\ modifies_2 st st' h0 h1)) *)
(* [@ "substitute"] *)
(* let rounds2 st st' = *)
(*   let h0 = ST.get() in *)
(*   let inv (h1:mem) (i:nat) : Type0 = *)
(*     live h1 st /\ live h1 st' /\ i <= 10 *)
(*     /\ as_seq h1 st == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st) *)
(*     /\ as_seq h1 st' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st') in *)
(*   let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < 10)}) : Stack unit *)
(*     (requires (fun h -> inv h (UInt32.v i))) *)
(*     (ensures (fun h0 _ h1 -> FStar.UInt32.(inv h1 (v i + 1)))) = *)
(*       double_round st; *)
(*       double_round st' in *)
(*   for 0ul 10ul inv f *)

(* [@ "substitute"] *)
(* val rounds3: *)
(*   st:state -> *)
(*   st':state{disjoint st st'} -> *)
(*   st'':state{disjoint st st'' /\ disjoint st' st''} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h st /\ live h st' /\ live h st'')) *)
(*     (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st' /\ live h0 st'' *)
(*       /\ live h1 st /\ live h1 st' /\ live h1 st'' /\ modifies_3 st st' st'' h0 h1)) *)
(* [@ "substitute"] *)
(* let rounds3 st st' st'' = *)
(*   let h0 = ST.get() in *)
(*   let inv (h1:mem) (i:nat) : Type0 = *)
(*     live h1 st /\ live h1 st' /\ live h1 st'' /\ i <= 10 *)
(*     /\ as_seq h1 st == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st) *)
(*     /\ as_seq h1 st' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st') *)
(*     /\ as_seq h1 st'' == repeat_spec i Spec.Chacha20_vec256.double_round (as_seq h0 st'') in *)
(*   let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < 10)}) : Stack unit *)
(*     (requires (fun h -> inv h (UInt32.v i))) *)
(*     (ensures (fun h0 _ h1 -> FStar.UInt32.(inv h1 (v i + 1)))) = *)
(*       double_round st; *)
(*       double_round st'; *)
(*       double_round st'' in *)
(*   for 0ul 10ul inv f *)


#reset-options "--max_fuel 0 --z3rlimit 100"


[@ "c_inline"]
val sum_states:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h1 st' /\ live h1 st /\ modifies_1 st' h0 h1 /\ live h0 st /\
      live h0 st' /\
      (let st1' = as_state h1 st' in let st0' = as_state h0 st' in let st0 = as_state h0 st in
       st1' == Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat st0' st0)))
[@ "c_inline"]
let sum_states st' st =
  let h0 = ST.get() in
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
  st'.(3ul) <- s3' +%^ s3;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st') (let st0' = as_state h0 st' in let st0 = as_state h0 st in
                                      Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat st0' st0)


[@ "c_inline"]
val copy_state:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st' /\ live h0 st /\ modifies_1 st' h0 h1 /\
      as_state h1 st' == as_state h0 st))
[@ "c_inline"]
let copy_state st' st =
  let h0 = ST.get() in
  st'.(0ul) <- st.(0ul);
  st'.(1ul) <- st.(1ul);
  st'.(2ul) <- st.(2ul);
  st'.(3ul) <- st.(3ul);
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st') (as_state h0 st)


#reset-options "--max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t -> log_t_
type log_t = Ghost.erased log_t_

let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s = as_state h st in
  match log with | MkLog key nonce ctr -> s == Spec.setup key nonce (UInt32.v ctr))


[@ "c_inline"]
val chacha20_core:
  k:state ->
  st:state{disjoint k st} ->
  Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k /\ live h1 st /\ modifies_1 k h0 h1 /\ live h0 st /\
      as_state h1 k == Spec.chacha20_core (as_state h0 st)))
[@ "c_inline"]
let chacha20_core k st =
  let h0 = ST.get() in
  copy_state k st;
  let h1 = ST.get() in
  rounds k;
  let h2 = ST.get() in
  sum_states k st;
  let h3 = ST.get() in
  Seq.lemma_eq_intro (as_state h3 k) (Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat (as_state h2 k) (as_state h2 st))
  


(* [@ "c_inline"] *)
(* val chacha20_core: *)
(*   log:log_t -> *)
(*   k:state -> *)
(*   st:state{disjoint k st} -> *)
(*   ctr:UInt32.t -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h k /\ live h st /\ invariant log h st)) *)
(*     (ensures  (fun h0 updated_log h1 -> live h1 k /\ live h1 st /\ modifies_2 k st h0 h1 /\ live h0 st /\ *)
(*       invariant log h1 st /\ invariant log h0 st /\ *)
(*       as_seq h1 k == Spec.chacha20_core (as_seq h0 st) /\ ke == ke' /\ n == n')) *)
(* [@ "c_inline"] *)
(* let chacha20_core log k st ctr =   *)
(*   let h0 = ST.get() in *)
(*   copy_state k st; *)
(*   let h1 = ST.get() in *)
(*   rounds k; *)
(*   let h2 = ST.get() in *)
(*   sum_states k st; *)
(*   let h3 = ST.get() in *)
(*   Seq.lemma_eq_intro (as_seq h3 k) (Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat (as_seq h2 k) (as_seq h2 st)) *)


(* [@ "c_inline"] *)
(* val chacha20_core2: *)
(*   k0:state -> *)
(*   k1:state -> *)
(*   st:state -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h k0 /\ live h k1 /\ live h st)) *)
(*     (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 st /\ modifies_3 st k0 k1 h0 h1)) *)
(* [@ "c_inline"] *)
(* let chacha20_core2 k0 k1 st = *)
(*   copy_state k0 st; *)
(*   copy_state k1 st; *)
(*   state_incr k1; *)
(*   rounds2 k0 k1; *)
(*   sum_states k0 st; *)
(*   state_incr st; *)
(*   sum_states k1 st *)

(* [@ "c_inline"] *)
(* val chacha20_core3: *)
(*   k0:state -> *)
(*   k1:state -> *)
(*   k2:state -> *)
(*   st:state -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h k0 /\ live h k1 /\ live h k2 /\ live h st)) *)
(*     (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 k2 /\ live h1 st /\ modifies_3 st k0 k1 h0 h1 )) *)
(* [@ "c_inline"] *)
(* let chacha20_core3 k0 k1 k2 st = *)
(*   copy_state k0 st; *)
(*   copy_state k1 st; *)
(*   state_incr k1; *)
(*   copy_state k2 k1; *)
(*   state_incr k2; *)
(*   rounds3 k0 k1 k2; *)
(*   sum_states k0 st; *)
(*   state_incr st; *)
(*   sum_states k1 st; *)
(*   state_incr st; *)
(*   sum_states k2 st *)


(* [@ "c_inline"] *)
(* val chacha20_block: *)
(*   log:log_t -> *)
(*   stream_block:uint8_p{length stream_block = 64} -> *)
(*   st:state{disjoint st stream_block} -> *)
(*   ctr:UInt32.t -> *)
(*   Stack log_t *)
(*     (requires (fun h -> live h stream_block /\ invariant log h st)) *)
(*     (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ modifies_1 stream_block h0 h1 /\ *)
(*       invariant updated_log h1 st /\ modifies_2 stream_block st h0 h1 *)
(*       /\ (let block = reveal_sbytes (as_seq h1 stream_block) in *)
(*          match Ghost.reveal log, Ghost.reveal updated_log with *)
(*          | MkLog k n, MkLog k' n' -> *)
(*              block == Spec.chacha20_block k n (U32.v ctr) /\ k == k' /\ n == n'))) *)
(* [@ "c_inline"] *)
(* let chacha20_block log stream_block st = *)
(*   push_frame(); *)
(*   let h0 = ST.get() in *)
(*   let k = Buffer.create zero 4ul in *)
(*   let h1 = ST.get() in *)
(*   no_upd_lemma_0 h0 h1 stream_block; *)
(*   no_upd_lemma_0 h0 h1 st; *)
(*   chacha20_core k st; *)
(*   let h2 = ST.get() in *)
(*   no_upd_lemma_1 h1 h2 k stream_block; *)
(*   no_upd_lemma_1 h1 h2 k st; *)
(*   state_to_key_block stream_block k; *)
(*   let h3 = ST.get() in *)
(*   pop_frame(); *)
(*   Ghost.elift1 (fun l -> match l with | MkLog k n -> MkLog k n) log'   *)

[@ "c_inline"]
val chacha20_block:
  log:log_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  Stack unit
    (requires (fun h -> live h stream_block /\ invariant log h st))
    (ensures  (fun h0 _ h1 -> live h1 stream_block /\ modifies_1 stream_block h0 h1 /\
      invariant log h1 st /\ invariant log h0 st /\
      (let block = reveal_sbytes (as_seq h1 stream_block) in
       match Ghost.reveal log with
       | MkLog k n ctr ->
           block == Spec.chacha20_block k n (U32.v ctr)) ))
[@ "c_inline"]
let chacha20_block log stream_block st =
  push_frame();
  let h0 = ST.get() in
  let k = Buffer.create zero 4ul in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 stream_block;
  no_upd_lemma_0 h0 h1 st;
  chacha20_core k st;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 k stream_block;
  no_upd_lemma_1 h1 h2 k st;
  state_to_key_block stream_block k;
  let h3 = ST.get() in
  assert(modifies_2_1 stream_block h0 h3);
  pop_frame()


[@ "c_inline"]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  ctr:UInt32.t ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1 /\
      invariant log h1 st /\
      Ghost.reveal log == MkLog (as_seq h0 k) (as_seq h0 n) ctr))
[@ "c_inline"]
let init st k n ctr =
  let h = ST.get() in
  state_setup st k n ctr;
  Ghost.elift2 (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 12 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n)) ctr) (Ghost.hide k) (Ghost.hide n)


#reset-options "--max_fuel 0 --z3rlimit 100"

val update_last:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= U32.v vecsizebytes4 /\ U32.v len > 0} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1 /\
      invariant log h1 st /\ invariant log h0 st /\
      (match Ghost.reveal log with | MkLog k n ctr ->
        let o = as_seq h1 output in
        let plain = as_seq h0 plain in
         o == (let mask = Spec.chacha20_cipher k n (U32.v ctr) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask)) ))
let update_last log output plain len st =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let block = create (uint8_to_sint8 0uy) vecsizebytes4 in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 plain;
  no_upd_lemma_0 h1 h2 st;
  chacha20_block log block st;
  let h3 = ST.get() in
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (Hacl.UInt8.logxor);
  let h4 = ST.get() in
  pop_frame();
  let h5 = ST.get() in
  ()


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
  log:log_t ->
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1))
let update log output plain st =
  let h0 = ST.get() in
  push_frame();
  let k = Buffer.create zero 4ul in
  chacha20_core k st;
  xor_block output plain k;
  (* state_incr st; *)
  pop_frame()

(* val update2: *)
(*   output:uint8_p{length output = U32.v vecsizebytes8} -> *)
(*   plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes8} -> *)
(*   st:state{disjoint st output /\ disjoint st plain} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h output /\ live h plain)) *)
(*     (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1)) *)
(* let update2 output plain st = *)
(*   let h0 = ST.get() in *)
(*   push_frame(); *)
(*   let k = Buffer.create zero 4ul in *)
(*   let k' = Buffer.create zero 4ul in *)
(*   chacha20_core2 k k' st; *)
(*   xor_block output plain k; *)
(*   xor_block (Buffer.offset output vecsizebytes4) (Buffer.offset plain vecsizebytes4) k'; *)
(*   state_incr st; *)
(*   pop_frame() *)

(* val update3: *)
(*   output:uint8_p{length output = U32.v vecsizebytes12} -> *)
(*   plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes12} -> *)
(*   st:state{disjoint st output /\ disjoint st plain} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h output /\ live h plain)) *)
(*     (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1)) *)
(* let update3 output plain st = *)
(*   let h0 = ST.get() in *)
(*   push_frame(); *)
(*   let k0 = Buffer.create zero 4ul in *)
(*   let k1 = Buffer.create zero 4ul in *)
(*   let k2 = Buffer.create zero 4ul in *)
(*   chacha20_core3 k0 k1 k2 st; *)
(*   xor_block output plain k0; *)
(*   xor_block (Buffer.offset output vecsizebytes4) (Buffer.offset plain vecsizebytes4) k1; *)
(*   xor_block (Buffer.offset output vecsizebytes8) (Buffer.offset plain vecsizebytes8) k2; *)
(*   state_incr st; *)
(*   pop_frame() *)

#reset-options "--max_fuel 0 --z3rlimit 300"


val chacha20_counter_mode_blocks:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p ->
  len:UInt32.t{64 * UInt32.v len = length output /\ length output == length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st /\
      (match Ghost.reveal log with | MkLog _ _ ctr -> (U32.v ctr + U32.v len < pow2 32))))
    (ensures (fun h0 updated_log h1 -> live h0 plain /\ live h0 st /\ invariant log h0 st /\
      live h1 st /\ invariant updated_log h1 st /\ live h1 output /\ modifies_2 output st h0 h1 /\
      (match Ghost.reveal log, Ghost.reveal updated_log with
       | MkLog k n ctr, MkLog k' n' ctr' ->
         let output = as_seq h1 output in let plain = as_seq h0 plain in
         k' == k /\ n' == n /\ (U32.v ctr + U32.v len < pow2 32) /\
         ctr' = U32.(ctr +^ len) /\
         output == Spec.CTR.counter_mode_blocks Spec.chacha20_ctx Spec.chacha20_cipher k n (U32.v ctr) plain)))
let chacha20_counter_mode_blocks log output plain len st =
  let h0 = ST.get() in
  let inv (h1:HyperStack.mem) (i:nat) : Type0 = True in
  let f' (i:UInt32.t{0 <= U32.v i /\ U32.v i < U32.v len}) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
  =
    let out_sub = Buffer.sub output 0ul U32.(64ul *^ i +^ 64ul) in
    let plain_sub = Buffer.sub plain 0ul U32.(64ul *^ i +^ 64ul) in
    let out_block = Buffer.sub output U32.(64ul *^ i) 64ul in
    let plain_block = Buffer.sub plain U32.(64ul *^ i) 64ul in
    let out_prefix = Buffer.sub output 0ul U32.(64ul *^ i) in
    let plain_prefix = Buffer.sub plain 0ul U32.(64ul *^ i) in
    update log out_block plain_block st;
    state_incr st in
  C.Loops.for 0ul len inv f';
  log


val chacha20_counter_mode:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ctr ->
         o == Spec.CTR.counter_mode Spec.chacha20_ctx Spec.chacha20_cipher k n (UInt32.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let chacha20_counter_mode log output plain len st =
  assert_norm(pow2 6 = 64);
  let open FStar.UInt32 in
  let blocks_len = (len >>^ 6ul) in
  let part_len   = len &^ 0x3ful in
  UInt.logand_mask (UInt32.v len) 6;
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  let h0 = ST.get() in
  let output' = Buffer.sub output 0ul (64ul *^ blocks_len) in
  let plain'  = Buffer.sub plain  0ul (64ul *^ blocks_len) in
  let output'' = Buffer.sub output (64ul *^ blocks_len) part_len in
  let plain''  = Buffer.sub plain  (64ul *^ blocks_len) part_len in
  let log' = chacha20_counter_mode_blocks log output' plain' blocks_len st (* ctr *) in
  if FStar.UInt32.(part_len >^ 0ul) then (
    let _ = update_last log' output'' plain'' part_len (* log *) st (* FStar.UInt32.(ctr +^ blocks_len) *) in
    ())
  else ();
  let h = ST.get() in
  (* Seq.lemma_eq_intro (Seq.append (as_seq h output') Seq.createEmpty) (as_seq h output'); *)
  (* Seq.lemma_eq_intro (as_seq h output) (Seq.append (as_seq h output') (as_seq h output'')); *)
  (* Seq.lemma_eq_intro (as_seq h0 plain) (Seq.append (as_seq h0 plain') (as_seq h0 plain'')); *)
  (* Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.CTR.counter_mode chacha20_ctx chacha20_cipher (Ghost.reveal log).k (Ghost.reveal log).n (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain))); *)
  ()


(* val chacha20_counter_mode_: *)
(*   output:uint8_p -> *)
(*   plain:uint8_p{disjoint output plain} -> *)
(*   len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= U32.v vecsizebytes4} -> *)
(*   st:state{disjoint st output /\ disjoint st plain} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h output /\ live h plain)) *)
(*     (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st *)
(*       /\ modifies_2 output st h0 h1)) *)
(* let rec chacha20_counter_mode_ output plain len st = *)
(*   let h0 = ST.get() in *)
(*   if U32.(len =^ 0ul) then ( *)
(*      () *)
(*   ) else  ( *)
(*      update_last output plain len st  *)
(*   ) *)

(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100" *)

(* val chacha20_counter_mode: *)
(*   output:uint8_p -> *)
(*   plain:uint8_p{disjoint output plain} -> *)
(*   len:U32.t{U32.v len = length output /\ U32.v len = length plain} -> *)
(*   st:state{disjoint st output /\ disjoint st plain} -> *)
(*   ctr:U32.t{U32.v ctr + (length plain / 64) < pow2 32} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h output /\ live h plain)) *)
(*     (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st *)
(*       /\ modifies_2 output st h0 h1)) *)
(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500" *)
(* let rec chacha20_counter_mode output plain len st ctr = *)
(*   let h0 = ST.get() in *)
(*   let bs = vecsizebytes4 in *)
(*   let bs2 = U32.(bs *^ 2ul) in *)
(*   let bs3 = U32.(bs *^ 3ul) in *)
(*   if U32.(len <^ bs) then chacha20_counter_mode_ output plain len st *)
(*   else  *)
(*   if U32.(len <^ bs2) then ( *)
(*     let b  = Buffer.sub plain 0ul bs in *)
(*     let b' = Buffer.offset plain bs in *)
(*     let o  = Buffer.sub output 0ul bs in *)
(*     let o' = Buffer.offset output bs in *)
(*     update o b st; *)
(*     let h = ST.get() in *)
(*     let l = chacha20_counter_mode o' b' U32.(len -^ bs) st U32.(ctr +^ blocks) in *)
(*     let h' = ST.get() in *)
(*     ()) *)
(*   else  *)
(*   if U32.(len <^ bs3) then ( *)
(*     let b  = Buffer.sub plain 0ul bs2 in *)
(*     let b' = Buffer.offset plain bs2 in *)
(*     let o  = Buffer.sub output 0ul bs2 in *)
(*     let o' = Buffer.offset output bs2 in *)
(*     update2 o b st; *)
(*     let h = ST.get() in *)
(*     let l = chacha20_counter_mode o' b' U32.(len -^ bs2) st U32.(ctr +^ (2ul *^ blocks)) in *)
(*     let h' = ST.get() in *)
(*     ()) *)
(*   else ( *)
(*     let b  = Buffer.sub plain 0ul bs3 in *)
(*     let b' = Buffer.offset plain bs3 in *)
(*     let o  = Buffer.sub output 0ul bs3 in *)
(*     let o' = Buffer.offset output bs3 in *)
(*     update3 o b st; *)
(*     let h = ST.get() in *)
(*     let l = chacha20_counter_mode o' b' U32.(len -^ bs3) st U32.(ctr +^ (3ul *^ blocks)) in *)
(*     let h' = ST.get() in *)
(*     ()) *)

#reset-options "--max_fuel 0 --z3rlimit 20"

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
  let log = init st k n ctr in
  chacha20_counter_mode log output plain len st (* ctr *);
  pop_frame()(* ; *)
