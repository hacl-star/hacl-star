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

unfold let vecsizebytes2 = 32ul
unfold let vecsizebytes3 = 48ul
unfold let vecsizebytes4 = 64ul
unfold let vecsizebytes8 = 128ul
unfold let vecsizebytes12 = 192ul

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


#reset-options "--max_fuel 0 --z3rlimit 10"

[@ "c_inline"]
val double_round3:
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st'' /\ disjoint st' st''} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st' /\ live h st''))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st' /\ live h0 st'' /\
      live h1 st /\ live h1 st' /\ live h1 st'' /\ modifies_3 st st' st'' h0 h1 /\
      as_state h1 st == Spec.double_round (as_state h0 st) /\
      as_state h1 st' == Spec.double_round (as_state h0 st') /\
      as_state h1 st'' == Spec.double_round (as_state h0 st'')
    ))

#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_modifies_double_round3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st' /\ disjoint st' st''} ->
  Lemma (requires (live h0 st /\ live h0 st' /\ live h0 st'' /\ HyperStack.equal_domains h0 h1 /\ 
    HyperStack.equal_domains h1 h2 /\ HyperStack.equal_domains h2 h3 /\
    modifies_1 st h0 h1 /\ modifies_1 st' h1 h2 /\ modifies_1 st'' h2 h3))
        (ensures (modifies_3 st st' st'' h0 h3))

#reset-options "--max_fuel 0 --z3rlimit 100"

let lemma_modifies_double_round3 h0 h1 h2 h3 st st' st'' =
  lemma_reveal_modifies_1 st   h0 h1;
  lemma_reveal_modifies_1 st'  h1 h2;
  lemma_reveal_modifies_1 st'' h2 h3;
  lemma_intro_modifies_3 st st' st'' h0 h3


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "c_inline"]
let double_round3 st st' st'' =
  let h0 = ST.get() in
  double_round st;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 st st';
  no_upd_lemma_1 h0 h1 st st'';
  assert(as_state h1 st' == as_state h0 st');
  assert(as_state h1 st'' == as_state h0 st'');
  assert(as_state h1 st == Spec.double_round (as_state h0 st));
  double_round st';
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 st' st;
  no_upd_lemma_1 h1 h2 st' st'';
  assert(as_state h2 st'' == as_state h0 st'');
  assert(as_state h2 st == as_state h1 st);
  assert(as_state h2 st == Spec.double_round (as_state h0 st));
  assert(as_state h2 st' == Spec.double_round (as_state h0 st'));
  double_round st'';
  let h3 = ST.get() in
  assert(as_state h3 st'' == Spec.double_round (as_state h0 st''));
  assert(as_state h3 st == Spec.double_round (as_state h0 st));
  assert(as_state h3 st' == Spec.double_round (as_state h0 st'));
  lemma_modifies_double_round3 h0 h1 h2 h3 st st' st''


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


#reset-options "--max_fuel 0 --z3rlimit 100"


[@ "substitute"]
val rounds3:
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st'' /\ disjoint st' st''} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st' /\ live h st''))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h0 st' /\ live h0 st''
      /\ live h1 st /\ live h1 st' /\ live h1 st'' /\ modifies_3 st st' st'' h0 h1 /\
      as_state h1 st == Spec.rounds (as_state h0 st) /\
      as_state h1 st' == Spec.rounds (as_state h0 st') /\
      as_state h1 st'' == Spec.rounds (as_state h0 st'') ))

#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_helper_rounds:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  st:state ->
  i:nat ->
  Lemma (requires (live h0 st /\ live h1 st /\ live h2 st /\
    as_state h1 st == repeat_spec i Spec.double_round (as_state h0 st) /\
    as_state h2 st == Spec.double_round (as_state h1 st) ))
        (ensures (live h0 st /\ live h2 st /\
    as_state h2 st == repeat_spec (i+1) Spec.double_round (as_state h0 st) ))
let lemma_helper_rounds h0 h1 h2 st i =
  lemma_repeat (i + 1) Spec.double_round (as_state h0 st)

val lemma_helper_rounds':
  h0:HyperStack.mem ->
  st:state ->
  Lemma (requires (live h0 st))
        (ensures (live h0 st /\ as_state h0 st == repeat_spec 0 Spec.double_round (as_state h0 st) ))
let lemma_helper_rounds' h0 st =
  lemma_repeat_0 0 Spec.double_round (as_state h0 st)


val lemma_helper_rounds3':
  h0:HyperStack.mem ->
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st'' /\ disjoint st' st''} ->
  Lemma (requires (live h0 st /\ live h0 st' /\ live h0 st''))
        (ensures (live h0 st /\ live h0 st' /\ live h0 st'' /\
          as_state h0 st == repeat_spec 0 Spec.double_round (as_state h0 st) /\
          as_state h0 st' == repeat_spec 0 Spec.double_round (as_state h0 st') /\
          as_state h0 st'' == repeat_spec 0 Spec.double_round (as_state h0 st'') ))
let lemma_helper_rounds3' h0 st st' st'' =
  lemma_helper_rounds' h0 st;
  lemma_helper_rounds' h0 st';
  lemma_helper_rounds' h0 st''

let lemma_eq_is_modifies_3 h (st:state) (st':state) (st'':state) : Lemma (modifies_3 st st' st'' h h)
  = lemma_intro_modifies_3 st st' st'' h h


val lemma_helper_rounds3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  st:state ->
  st':state{disjoint st st'} ->
  st'':state{disjoint st st'' /\ disjoint st' st''} ->
  i:nat ->
  Lemma (requires (live h0 st /\ live h0 st' /\ live h0 st'' /\
    live h1 st' /\ live h1 st'' /\ live h1 st /\
    live h2 st' /\ live h2 st'' /\ live h2 st /\
    as_state h1 st == repeat_spec i Spec.double_round (as_state h0 st) /\
    as_state h1 st' == repeat_spec i Spec.double_round (as_state h0 st') /\
    as_state h1 st'' == repeat_spec i Spec.double_round (as_state h0 st'') /\
    as_state h2 st == Spec.double_round (as_state h1 st) /\
    as_state h2 st' == Spec.double_round (as_state h1 st') /\
    as_state h2 st'' == Spec.double_round (as_state h1 st'') ))
        (ensures (live h0 st /\ live h0 st' /\ live h0 st'' /\ live h2 st' /\ live h2 st'' /\ live h2 st /\
    as_state h2 st == repeat_spec (i+1) Spec.double_round (as_state h0 st) /\
    as_state h2 st' == repeat_spec (i+1) Spec.double_round (as_state h0 st') /\
    as_state h2 st'' == repeat_spec (i+1) Spec.double_round (as_state h0 st'') ))
let lemma_helper_rounds3 h0 h1 h2 st st' st'' i =
  lemma_helper_rounds h0 h1 h2 st i;
  lemma_helper_rounds h0 h1 h2 st' i;
  lemma_helper_rounds h0 h1 h2 st'' i


#reset-options "--max_fuel 0 --z3rlimit 200"

[@ "substitute"]
let rounds3 st st' st'' =
  let h0 = ST.get() in
  let inv (h1:mem) (i:nat) : Type0 =
    live h1 st /\ live h1 st' /\ live h1 st'' /\ i <= 10 /\ modifies_3 st st' st'' h0 h1 /\
    as_state h1 st == repeat_spec i Spec.double_round (as_state h0 st) /\
    as_state h1 st' == repeat_spec i Spec.double_round (as_state h0 st') /\
    as_state h1 st'' == repeat_spec i Spec.double_round (as_state h0 st'') in
  let f (i:UInt32.t{FStar.UInt32.(0 <= v i /\ v i < 10)}) : Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h0 _ h1 -> FStar.UInt32.(inv h1 (v i + 1)))) =
      let h1 = ST.get() in
      double_round3 st st' st'';
      let h2 = ST.get() in
      lemma_helper_rounds3 h0 h1 h2 st st' st'' (UInt32.v i);
      () in
  lemma_helper_rounds3' h0 st st' st'';
  lemma_eq_is_modifies_3 h0 st st' st'';
  for 0ul 10ul inv f


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
  log:log_t ->
  k:state ->
  st:state{disjoint k st} ->
  Stack unit
    (requires (fun h -> live h k /\ live h st /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h1 k /\ live h1 st /\ modifies_1 k h0 h1 /\ live h0 st /\
      invariant log h0 st /\ (
      match Ghost.reveal log with | MkLog k' n ctr ->
        as_state h1 k == Spec.(chacha20_core (setup k' n (UInt32.v ctr)))) ))
[@ "c_inline"]
let chacha20_core log k st =
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
(* let chacha20_core log k st ctr = *)
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
(*   (\* state_incr k1; *\) *)
(*   rounds2 k0 k1; *)
(*   sum_states k0 st; *)
(*   (\* state_incr st; *\) *)
(*   sum_states k1 st *)

#reset-options "--max_fuel 0 --z3rlimit 10"

val state_incr:
  log:log_t ->
  st:state ->
  Stack unit
    (requires (fun h -> live h st /\ invariant log h st /\ (match Ghost.reveal log with
      | MkLog k n c -> UInt32.v c < pow2 32 - 1)))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ invariant log h0 st /\ modifies_1 st h0 h1 /\ (
      match Ghost.reveal log with
      | MkLog k n c -> UInt32.v c < pow2 32 - 1 /\ as_state h1 st == Spec.setup k n (UInt32.v c + 1))))
#reset-options "--max_fuel 0 --z3rlimit 100"
let state_incr log st =
  let h0 = ST.get() in
  assert(as_state h0 st == (match Ghost.reveal log with | MkLog k n c -> Spec.setup k n (UInt32.v c )));
  assert(let vec = vec_as_seq (Seq.index (as_seq h0 st) 3) in
         match Ghost.reveal log with
         | MkLog k n c -> vec == Seq.cons (c) (Spec.Lib.uint32s_from_le 3 n));
  state_incr st;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (vec_as_seq (Seq.index (as_seq h0 st) 3)) 1 4)
                     (Seq.slice (vec_as_seq (Seq.index (as_seq h1 st) 3)) 1 4);
  assert(match Ghost.reveal log with
        | MkLog k n c ->
          Seq.index (vec_as_seq (Seq.index (as_seq h1 st) 3)) 0 = FStar.UInt32.(c +^ 1ul));
  Seq.lemma_eq_intro (match Ghost.reveal log with
                     | MkLog k n c -> Seq.cons FStar.UInt32.(c+^1ul) (Spec.Lib.uint32s_from_le 3 n))
                     (vec_as_seq (Seq.index (as_seq h1 st) 3));
  Seq.lemma_eq_intro (as_state h1 st) (match Ghost.reveal log with | MkLog k n c ->
                                       Spec.setup k n (UInt32.v c + 1))

#reset-options "--max_fuel 0 --z3rlimit 10"

val log_incr:
  log:log_t -> Tot (log':log_t{match Ghost.reveal log, Ghost.reveal log' with
    | MkLog k n c, MkLog k' n' c' -> k == k' /\ n == n' /\ UInt32.v c' == (UInt32.v c + 1) % (pow2 32)})
let log_incr log =
  Ghost.elift1 (fun l -> match l with | MkLog k n c -> MkLog k n FStar.UInt32.(c +%^ 1ul)) log


#reset-options "--max_fuel 0 --z3rlimit 10"

[@ "c_inline"]
val chacha20_incr3:
  log:log_t ->
  k0:state ->
  k1:state{disjoint k0 k1} ->
  k2:state{disjoint k0 k2 /\ disjoint k1 k2} ->
  st:state{disjoint k0 st /\ disjoint k1 st /\ disjoint k2 st} ->
  Stack unit
    (requires (fun h -> live h k0 /\ live h k1 /\ live h k2 /\ live h st /\ invariant log h st /\
      (match Ghost.reveal log with
      | MkLog k n ctr -> UInt32.v ctr < pow2 32 - 2)))
    (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 k2 /\ live h1 st /\
      invariant log h0 st /\
      modifies_3 k0 k1 k2 h0 h1 /\ (
      match Ghost.reveal log with | MkLog k n ctr ->
      UInt32.v ctr < pow2 32 - 2 /\
      as_state h1 k0 == Spec.(setup k n (UInt32.v ctr)) /\
      as_state h1 k1 == Spec.(setup k n (UInt32.v ctr + 1)) /\
      as_state h1 k2 == Spec.(setup k n (UInt32.v ctr + 2)) ) ))

#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_chacha_incr3_modifies:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  st0:state -> st1:state{disjoint st0 st1} -> st2:state{disjoint st2 st1 /\ disjoint st2 st0} ->
  Lemma (requires (live h0 st0 /\ live h0 st1 /\ live h0 st2 /\ modifies_1 st0 h0 h1 /\ modifies_1 st1 h1 h2 /\ modifies_1 st2 h2 h3 /\ HyperStack.equal_domains h0 h1 /\ HyperStack.equal_domains h1 h2 /\ HyperStack.equal_domains h2 h3))
        (ensures (modifies_3 st0 st1 st2 h0 h3))
let lemma_chacha_incr3_modifies h0 h1 h2 h3 st0 st1 st2 =
  lemma_reveal_modifies_1 st0 h0 h1;
  lemma_reveal_modifies_1 st1 h1 h2;
  lemma_reveal_modifies_1 st2 h2 h3;
  lemma_intro_modifies_3 st0 st1 st2 h0 h3

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ "c_inline"]
let chacha20_incr3 log k0 k1 k2 st =
  let h0 = ST.get() in
  copy_state k0 st;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 k0 st;
  no_upd_lemma_1 h0 h1 k0 k1;
  no_upd_lemma_1 h0 h1 k0 k2;
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h1 k0 == Spec.setup k n (UInt32.v c));
  copy_state k1 st;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 k1 st;
  no_upd_lemma_1 h1 h2 k1 k0;
  no_upd_lemma_1 h1 h2 k1 k2;
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h2 k0 == Spec.setup k n (UInt32.v c));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h2 k1 == Spec.setup k n (UInt32.v c));
  state_incr log k1;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 k1 st;
  no_upd_lemma_1 h2 h3 k1 k0;
  no_upd_lemma_1 h2 h3 k1 k2;
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h3 k1 == Spec.setup k n (UInt32.v c + 1));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h3 k0 == Spec.setup k n (UInt32.v c));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h3 st == Spec.setup k n (UInt32.v c));
  copy_state k2 k1;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 k2 st;
  no_upd_lemma_1 h3 h4 k2 k0;
  no_upd_lemma_1 h3 h4 k2 k1;
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h4 k2 == Spec.setup k n (UInt32.v c + 1));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h4 k1 == Spec.setup k n (UInt32.v c + 1));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h4 k0 == Spec.setup k n (UInt32.v c));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h4 st == Spec.setup k n (UInt32.v c));
  let log' = log_incr log in
  Math.Lemmas.modulo_lemma (UInt32.v (MkLog?.ctr (Ghost.reveal log)) + 1) (pow2 32);
  Math.Lemmas.modulo_lemma (UInt32.v (MkLog?.ctr (Ghost.reveal log)) + 2) (pow2 32);
  state_incr log' k2;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 k2 st;
  no_upd_lemma_1 h4 h5 k2 k0;
  no_upd_lemma_1 h4 h5 k2 k1;
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h5 k2 == Spec.setup k n (UInt32.v c + 2));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h5 k1 == Spec.setup k n (UInt32.v c + 1));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h5 k0 == Spec.setup k n (UInt32.v c));
  assert(match Ghost.reveal log with | MkLog k n c -> as_state h5 st == Spec.setup k n (UInt32.v c));
  lemma_chacha_incr3_modifies h0 h1 h3 h5 k0 k1 k2


[@ "c_inline"]
val chacha20_sum3:
  log:log_t ->
  k0:state ->
  k1:state{disjoint k0 k1 /\ frameOf k0 == frameOf k1} ->
  k2:state{disjoint k0 k2 /\ disjoint k1 k2 /\ frameOf k1 == frameOf k2} ->
  st:state{disjoint k0 st /\ disjoint k1 st /\ disjoint k2 st /\ frameOf st <> frameOf k2} ->
  Stack unit
    (requires (fun h -> live h k0 /\ live h k1 /\ live h k2 /\ live h st /\ invariant log h st /\
      (match Ghost.reveal log with
      | MkLog k n ctr -> UInt32.v ctr < pow2 32 - 2 /\
      as_state h k0 == Spec.rounds (Spec.setup k n (UInt32.v ctr)) /\ 
      as_state h k1 == Spec.rounds (Spec.setup k n (UInt32.v ctr+1)) /\ 
      as_state h k2 == Spec.rounds (Spec.setup k n (UInt32.v ctr+2)) )))
    (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 k2 /\ live h1 st /\
      invariant log h0 st /\
      modifies_buf_3 (frameOf k0) k0 k1 k2 h0 h1 /\
      modifies_buf_1 (frameOf st) st h0 h1 /\
      HyperHeap.modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) FStar.HyperStack.(h0.h) FStar.HyperStack.(h1.h) /\ (
      match Ghost.reveal log with | MkLog k n ctr ->
      UInt32.v ctr < pow2 32 - 2 /\
      as_state h1 st == Spec.setup k n (UInt32.v ctr+2) /\
      as_state h1 k0 == Spec.chacha20_core (Spec.setup k n (UInt32.v ctr)) /\
      as_state h1 k1 == Spec.chacha20_core (Spec.setup k n (UInt32.v ctr+1)) /\
      as_state h1 k2 == Spec.chacha20_core (Spec.setup k n (UInt32.v ctr+2)) )))

#reset-options "--max_fuel 0 --z3rlimit 200"


val lemma_modifies_sum3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  h2:HyperStack.mem ->
  h3:HyperStack.mem ->
  h4:HyperStack.mem ->
  h5:HyperStack.mem ->
  st:state ->
  k0:state{disjoint st k0 /\ frameOf st <> frameOf k0} ->
  k1:state{disjoint st k1 /\ disjoint k0 k1 /\ frameOf k1 == frameOf k0} ->
  k2:state{disjoint st k2 /\ disjoint k0 k2 /\ disjoint k1 k2 /\ frameOf k2 == frameOf k1} ->
  Lemma (requires (live h0 st /\ live h0 k0 /\ live h0 k1 /\ live h0 k2 /\
    HyperStack.equal_domains h0 h1 /\ HyperStack.equal_domains h1 h2 /\
    HyperStack.equal_domains h2 h3 /\ HyperStack.equal_domains h3 h4 /\ HyperStack.equal_domains h4 h5 /\
    modifies_1 k0 h0 h1 /\ modifies_1 st h1 h2 /\ modifies_1 k1 h2 h3 /\ modifies_1 st h3 h4 /\
    modifies_1 k2 h4 h5))
        (ensures (modifies_buf_3 (frameOf k0) k0 k1 k2 h0 h5 /\
          modifies_buf_1 (frameOf st) st h0 h5 /\
          HyperHeap.modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) FStar.HyperStack.(h0.h) FStar.HyperStack.(h5.h) ))
let lemma_modifies_sum3 h0 h1 h2 h3 h4 h5 st k0 k1 k2 =
  lemma_reveal_modifies_1 k0 h0 h1;
  lemma_reveal_modifies_1 st h1 h2;
  lemma_reveal_modifies_1 k1 h2 h3;
  lemma_reveal_modifies_1 st h3 h4;
  lemma_reveal_modifies_1 k2 h4 h5

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ "c_inline"]
let chacha20_sum3 log k0 k1 k2 st =
  let log' = log_incr log in
  Math.Lemmas.modulo_lemma (UInt32.v (MkLog?.ctr (Ghost.reveal log)) + 1) (pow2 32);
  Math.Lemmas.modulo_lemma (UInt32.v (MkLog?.ctr (Ghost.reveal log)) + 2) (pow2 32);
  let h0 = ST.get() in
  sum_states k0 st;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 k0 k1;
  no_upd_lemma_1 h0 h1 k0 k2;
  no_upd_lemma_1 h0 h1 k0 st;
  state_incr log st;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 st k0;
  no_upd_lemma_1 h1 h2 st k2;
  no_upd_lemma_1 h1 h2 st k1;
  sum_states k1 st;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 k1 k0;
  no_upd_lemma_1 h2 h3 k1 k2;
  no_upd_lemma_1 h2 h3 k1 st;
  state_incr log' st;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 st k0;
  no_upd_lemma_1 h3 h4 st k2;
  no_upd_lemma_1 h3 h4 st k1;
  sum_states k2 st;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 k2 k0;
  no_upd_lemma_1 h4 h5 k2 k1;
  no_upd_lemma_1 h4 h5 k2 st;
  lemma_modifies_sum3 h0 h1 h2 h3 h4 h5 st k0 k1 k2;
  ()



[@ "c_inline"]
val chacha20_core3:
  log:log_t ->
  k0:state ->
  k1:state{disjoint k0 k1 /\ frameOf k1 == frameOf k0} ->
  k2:state{disjoint k0 k2 /\ disjoint k1 k2 /\ frameOf k2 == frameOf k1} ->
  st:state{disjoint k0 st /\ disjoint k1 st /\ disjoint k2 st /\ frameOf st <> frameOf k0} ->
  Stack unit
    (requires (fun h -> live h k0 /\ live h k1 /\ live h k2 /\ live h st /\ invariant log h st /\
      (match Ghost.reveal log with
      | MkLog k n ctr -> UInt32.v ctr < pow2 32 - 2)))
    (ensures  (fun h0 updated_log h1 -> live h1 k0 /\ live h1 k1 /\ live h1 k2 /\ live h1 st /\
      invariant log h0 st /\
      modifies_buf_3 (frameOf k0) k0 k1 k2 h0 h1 /\
      modifies_buf_1 (frameOf st) st h0 h1 /\
      HyperHeap.modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) FStar.HyperStack.(h0.h) FStar.HyperStack.(h1.h) /\ (
      match Ghost.reveal log with | MkLog k n ctr ->
      UInt32.v ctr < pow2 32 - 2 /\
      as_state h1 k0 == Spec.(chacha20_core (setup k n (UInt32.v ctr))) /\
      as_state h1 k1 == Spec.(chacha20_core (setup k n (UInt32.v ctr + 1))) /\
      as_state h1 k2 == Spec.(chacha20_core (setup k n (UInt32.v ctr + 2))) ) ))


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "c_inline"]
let chacha20_core3 log k0 k1 k2 st =
  let h0 = ST.get() in
  chacha20_incr3 log k0 k1 k2 st;
  let h1 = ST.get() in
  rounds3 k0 k1 k2;
  let h2 = ST.get() in
  lemma_reveal_modifies_3 k0 k1 k2 h0 h2;
  chacha20_sum3 log k0 k1 k2 st;
  let h3 = ST.get() in
  ()

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

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ "c_inline"]
let chacha20_block log stream_block st =
  push_frame();
  let h0 = ST.get() in
  let k = Buffer.create zero 4ul in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 stream_block;
  no_upd_lemma_0 h0 h1 st;
  chacha20_core log k st;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 k stream_block;
  no_upd_lemma_1 h1 h2 k st;
  state_to_key_block stream_block k;
  let h3 = ST.get() in
  assert(modifies_2_1 stream_block h0 h3);
  pop_frame()

#reset-options "--max_fuel 0 --z3rlimit 100"

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


(* val load_bytes_to_state: *)
(*   st:state -> *)
(*   plain:uint8_p{length plain = 64 /\ disjoint st plain} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h st /\ live h plain)) *)
(*     (ensures (fun h0 _ h1 -> live h0 st /\ live h0 plain /\ *)
(*       live h1 st /\ modifies_1 st h0 h1 /\ ( *)
(*       let st = as_seq h1 st in *)
(*       let plain = as_seq h0 plain in *)
(*       vec_as_seq (Seq.index st 0) == Spec.Lib.uint32s_from_le 4 (Seq.slice plain 0 16) /\ *)
(*       vec_as_seq (Seq.index st 1) == Spec.Lib.uint32s_from_le 4 (Seq.slice plain 16 32) /\ *)
(*       vec_as_seq (Seq.index st 2) == Spec.Lib.uint32s_from_le 4 (Seq.slice plain 32 48) /\ *)
(*       vec_as_seq (Seq.index st 3) == Spec.Lib.uint32s_from_le 4 (Seq.slice plain 48 64) ))) *)
(* let load_bytes_to_state st plain = *)  

#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_uint32s_fragments:
  h:HyperStack.mem ->
  output:uint8_p{length output = 64 /\ live h output} ->
  a:Seq.seq UInt32.t{Seq.length a = 4} ->
  b:Seq.seq UInt32.t{Seq.length b = 4} ->
  c:Seq.seq UInt32.t{Seq.length c = 4} ->
  d:Seq.seq UInt32.t{Seq.length d = 4} ->
  Lemma (requires (as_seq h (Buffer.sub output 0ul  16ul) == Spec.Lib.uint32s_to_le 4 a /\
                   as_seq h (Buffer.sub output 16ul 16ul) == Spec.Lib.uint32s_to_le 4 b /\
                   as_seq h (Buffer.sub output 32ul 16ul) == Spec.Lib.uint32s_to_le 4 c /\
                   as_seq h (Buffer.sub output 48ul 16ul) == Spec.Lib.uint32s_to_le 4 d))
        (ensures (as_seq h output == Spec.Lib.uint32s_to_le 16 FStar.Seq.(a @| b @| c @| d)))

#reset-options "--max_fuel 0 --z3rlimit 100"

let lemma_append_assoc a b c : Lemma (let open FStar.Seq in a @| b @| c == (a @| b) @| c) =
  let open FStar.Seq in
  Seq.lemma_eq_intro ((a @| b) @| c) (a @| b @| c)

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_uint32s_fragments h output a b c d =
  let open FStar.Seq in
  let s = a @| b @| c @| d in
  let s02 = a @| b @| c in
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul  16ul)) (Seq.slice (as_seq h output) 0 16);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 16ul 16ul)) (Seq.slice (as_seq h output) 16 32);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 32ul 16ul)) (Seq.slice (as_seq h output) 32 48);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 48ul 16ul)) (Seq.slice (as_seq h output) 48 64);
  Seq.lemma_eq_intro (a @| b @| c) (slice s 0 12);
  Seq.lemma_eq_intro d (slice s 12 16);
  Spec.Lib.lemma_uint32s_to_le_slice 16 s 12;
  assert(Spec.Lib.uint32s_to_le 16 s == Spec.Lib.uint32s_to_le 12 s02 @| Spec.Lib.uint32s_to_le 4 d);
  let s01 = a @| b in
  Seq.lemma_eq_intro s01 (slice s02 0 8);
  Seq.lemma_eq_intro c (slice s02 8 12);
  Spec.Lib.lemma_uint32s_to_le_slice 12 s02 8;
  Seq.lemma_eq_intro (Spec.Lib.uint32s_to_le 16 s)
                     (Spec.Lib.uint32s_to_le 8 s01 @| Spec.Lib.uint32s_to_le 4 c @| Spec.Lib.uint32s_to_le 4 d);
  lemma_append_assoc (Spec.Lib.uint32s_to_le 8 s01) (Spec.Lib.uint32s_to_le 4 c) (Spec.Lib.uint32s_to_le 4 d);
  Seq.lemma_eq_intro a (slice s01 0 4);
  Seq.lemma_eq_intro b (slice s01 4 8);
  Spec.Lib.lemma_uint32s_to_le_slice 8 s01 4;
  Seq.lemma_eq_intro (Spec.Lib.uint32s_to_le 16 s)
                     (Spec.Lib.uint32s_to_le 4 a @| Spec.Lib.uint32s_to_le 4 b @| Spec.Lib.uint32s_to_le 4 c @| Spec.Lib.uint32s_to_le 4 d);
  Seq.lemma_eq_intro (slice (as_seq h output) 0 16 @| slice (as_seq h output) 16 32 @| slice (as_seq h output) 32 48 @| slice (as_seq h output) 48 64) (as_seq h output);
  Seq.lemma_eq_intro (Spec.Lib.uint32s_to_le 16 s) (as_seq h output)


#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_uint32s_fragments2:
  h:HyperStack.mem ->
  output:uint8_p{length output = 64 /\ live h output} ->
  a:Seq.seq UInt32.t{Seq.length a = 4} ->
  b:Seq.seq UInt32.t{Seq.length b = 4} ->
  c:Seq.seq UInt32.t{Seq.length c = 4} ->
  d:Seq.seq UInt32.t{Seq.length d = 4} ->
  Lemma (requires (Spec.Lib.uint32s_from_le 4 (as_seq h (Buffer.sub output 0ul  16ul)) == a /\
                   Spec.Lib.uint32s_from_le 4 (as_seq h (Buffer.sub output 16ul 16ul)) == b /\
                   Spec.Lib.uint32s_from_le 4 (as_seq h (Buffer.sub output 32ul 16ul)) == c /\
                   Spec.Lib.uint32s_from_le 4 (as_seq h (Buffer.sub output 48ul 16ul)) == d))
        (ensures (Spec.Lib.uint32s_from_le 16 (as_seq h output) == FStar.Seq.(a @| b @| c @| d)))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_uint32s_fragments2 h output a b c d =
  let open FStar.Seq in
  let s' = as_seq h output in
  let s  = s' in
  let s0 = slice s' 0  16 in
  let s1 = slice s' 16 32 in
  let s2 = slice s' 32 48 in
  let s3 = slice s' 48 64 in
  let s02 = slice s' 0 48 in
  let s01 = slice s' 0 32 in
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul  16ul)) (Seq.slice (as_seq h output) 0 16);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 16ul 16ul)) (Seq.slice (as_seq h output) 16 32);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 32ul 16ul)) (Seq.slice (as_seq h output) 32 48);
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 48ul 16ul)) (Seq.slice (as_seq h output) 48 64);
  Spec.Lib.lemma_uint32s_from_le_slice 16 s 12;
  assert(Spec.Lib.uint32s_from_le 16 s == Spec.Lib.uint32s_from_le 12 s02 @| Spec.Lib.uint32s_from_le 4 s3);
  Seq.lemma_eq_intro s01 (slice s02 0 32);
  Seq.lemma_eq_intro s2 (slice s02 32 48);
  Spec.Lib.lemma_uint32s_from_le_slice 12 s02 8;
  Seq.lemma_eq_intro (Spec.Lib.uint32s_from_le 16 s)
                     (Spec.Lib.uint32s_from_le 8 s01 @| Spec.Lib.uint32s_from_le 4 s2 @| Spec.Lib.uint32s_from_le 4 s3);
  lemma_append_assoc (Spec.Lib.uint32s_from_le 8 s01) (Spec.Lib.uint32s_from_le 4 s2) (Spec.Lib.uint32s_from_le 4 s3);
  Seq.lemma_eq_intro s0 (slice s01 0 16);
  Seq.lemma_eq_intro s1 (slice s01 16 32);
  Spec.Lib.lemma_uint32s_from_le_slice 8 s01 4;
  Seq.lemma_eq_intro (Spec.Lib.uint32s_from_le 16 s)
                     (Spec.Lib.uint32s_from_le 4 s0 @| Spec.Lib.uint32s_from_le 4 s1 @| Spec.Lib.uint32s_from_le 4 s2 @| Spec.Lib.uint32s_from_le 4 s3)


val store_4_vec:
  output:uint8_p{length output = 64} ->
  v0:vec -> v1:vec -> v2:vec -> v3:vec ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1 /\
      as_seq h1 output == FStar.Seq.(Spec.Lib.uint32s_to_le 16 (vec_as_seq v0 @| vec_as_seq v1 @|
                                                                vec_as_seq v2 @| vec_as_seq v3)) ))
let store_4_vec output v0 v1 v2 v3 =
  let o0 = (Buffer.sub output 0ul  16ul) in
  let o1 = (Buffer.sub output 16ul 16ul) in
  let o2 = (Buffer.sub output 32ul 16ul) in
  let o3 = (Buffer.sub output 48ul 16ul) in
  let h0 = ST.get() in
  vec_store_le o0 v0;
  let h1 = ST.get() in
  vec_store_le o1 v1;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 o1 o0;
  vec_store_le o2 v2;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 o2 o0;
  no_upd_lemma_1 h2 h3 o2 o1;
  vec_store_le o3 v3;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 o3 o0;
  no_upd_lemma_1 h3 h4 o3 o1;
  no_upd_lemma_1 h3 h4 o3 o2;
  assert(Spec.Lib.uint32s_from_le 4 (as_seq h4 o0) == vec_as_seq v0);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (as_seq h4 o0);
  Spec.Lib.lemma_uint32s_from_le_inj 4 (as_seq h4 o0) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v0));
  assert(Spec.Lib.uint32s_from_le 4 (as_seq h4 o1) == vec_as_seq v1);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (as_seq h4 o1);
  Spec.Lib.lemma_uint32s_from_le_inj 4 (as_seq h4 o1) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v1));
  assert(Spec.Lib.uint32s_from_le 4 (as_seq h4 o2) == vec_as_seq v2);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (as_seq h4 o2);
  Spec.Lib.lemma_uint32s_from_le_inj 4 (as_seq h4 o2) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v2));
  assert(Spec.Lib.uint32s_from_le 4 (as_seq h4 o3) == vec_as_seq v3);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (as_seq h4 o3);
  Spec.Lib.lemma_uint32s_from_le_inj 4 (as_seq h4 o3) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v3));
  lemma_uint32s_fragments h4 output (vec_as_seq v0) (vec_as_seq v1) (vec_as_seq v2) (vec_as_seq v3)


#reset-options "--max_fuel 0 --z3rlimit 100"

val xor_block:
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h st))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 st /\ live h0 plain /\
      live h1 output /\ modifies_1 output h0 h1 /\ (
      let st = as_seq h0 st in
      let output = as_seq h1 output in
      let plain = as_seq h0 plain in
      let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
      (* let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @| *)
      (*                          Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @| *)
      (*                          Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @| *)
      (*                          Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in *)
      output == Spec.Loops.seq_map2 UInt8.logxor plain stbytes) ))
let xor_block output plain st =
  let h0 = ST.get() in
  let p0 = vec_load_le (Buffer.sub plain 0ul 16ul) in
  let p1 = vec_load_le (Buffer.sub plain 16ul 16ul) in
  let p2 = vec_load_le (Buffer.sub plain 32ul 16ul) in
  let p3 = vec_load_le (Buffer.sub plain 48ul 16ul) in
  let k0 = st.(0ul) in
  let k1 = st.(1ul) in
  let k2 = st.(2ul) in
  let k3 = st.(3ul) in
  let o0 = vec_xor p0 k0 in
  let o1 = vec_xor p1 k1 in
  let o2 = vec_xor p2 k2 in
  let o3 = vec_xor p3 k3 in
  assert(let s = FStar.Seq.(vec_as_seq o0 @| vec_as_seq o1 @| vec_as_seq o2 @| vec_as_seq o3) in
         let k = FStar.Seq.(vec_as_seq k0 @| vec_as_seq k1 @| vec_as_seq k2 @| vec_as_seq k3) in
         let p = FStar.Seq.(vec_as_seq p0 @| vec_as_seq p1 @| vec_as_seq p2 @| vec_as_seq p3) in
         (forall (i:nat). i < 16 ==> Seq.index s i == FStar.UInt32.(Seq.index p i ^^ Seq.index k i)));
  Seq.lemma_eq_intro (let k = FStar.Seq.(vec_as_seq k0 @| vec_as_seq k1 @| vec_as_seq k2 @| vec_as_seq k3) in let p = FStar.Seq.(vec_as_seq p0 @| vec_as_seq p1 @| vec_as_seq p2 @| vec_as_seq p3) in
    Spec.Loops.seq_map2 FStar.UInt32.logxor p k)
                     FStar.Seq.(vec_as_seq o0 @| vec_as_seq o1 @| vec_as_seq o2 @| vec_as_seq o3);
  lemma_uint32s_fragments2 h0 plain (vec_as_seq p0) (vec_as_seq p1) (vec_as_seq p2) (vec_as_seq p3);
  assert (FStar.Seq.(vec_as_seq p0 @| vec_as_seq p1 @| vec_as_seq p2 @| vec_as_seq p3) ==
    Spec.Lib.uint32s_from_le 16 (as_seq h0 plain));
  Hacl.Impl.Xor.Lemmas.lemma_xor_uint32s_to_bytes (as_seq h0 plain) FStar.Seq.(vec_as_seq k0 @| vec_as_seq k1 @| vec_as_seq k2 @| vec_as_seq k3);
  store_4_vec output o0 o1 o2 o3;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (let st = as_seq h0 st in
                                         let output = as_seq h1 output in
                                         let plain = as_seq h0 plain in
                                         let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                                         vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                                        vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
                                         Spec.Loops.seq_map2 UInt8.logxor plain stbytes)


#reset-options "--max_fuel 0 --z3rlimit 200"

val update:
  log:log_t ->
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_1 output h0 h1 /\
      live h1 st /\ invariant log h0 st /\
      (let o = reveal_sbytes (as_seq h1 output) in
       let plain = reveal_sbytes (as_seq h0 plain) in
       match Ghost.reveal log with | MkLog k n ctr ->
       o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (Spec.chacha20_cipher k n (U32.v ctr)) )
       ))
let update log output plain st =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let k = Buffer.create zero 4ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 plain;
  no_upd_lemma_0 h1 h2 st;
  chacha20_core log k st;
  let h3 = ST.get() in
  assume (let st = as_seq h3 k in
          let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
          let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in
          stbytes == stbytes');
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                      Spec.chacha20_cipher k n (UInt32.v ctr))
                     (let st = as_seq h3 k in
                      FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))));
  no_upd_lemma_1 h2 h3 k plain;
  no_upd_lemma_1 h2 h3 k st;
  xor_block output plain k;
  let h4 = ST.get() in
  Seq.lemma_eq_intro (as_seq h4 output)
                     (let plain = as_seq h0 plain in
                      match Ghost.reveal log with | MkLog k n ctr ->
                      seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (Spec.chacha20_cipher k n (U32.v ctr)));
  pop_frame();
  let h5 = ST.get() in
  ()

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


val lemma_live_update3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem ->
  st:state ->
  k0:state{disjoint k0 st /\ frameOf st <> frameOf k0} ->
  k1:state{disjoint k1 st /\ disjoint k1 k0 /\ frameOf k0 == frameOf k1} ->
  k2:state{disjoint k0 k2 /\ disjoint k1 k2 /\ disjoint k2 st /\ frameOf k2 == frameOf k1} ->
  buf:uint8_p{disjoint st buf /\ frameOf buf <> frameOf k0} ->
  Lemma (requires (live h0 st /\ live h0 k0 /\ live h0 k1 /\ live h0 k2 /\ live h0 buf /\
      modifies_buf_3 (frameOf k0) k0 k1 k2 h0 h1 /\
      modifies_buf_1 (frameOf st) st h0 h1 /\
      HyperHeap.modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) FStar.HyperStack.(h0.h) FStar.HyperStack.(h1.h) ))
        (ensures (live h1 buf /\ live h0 buf /\ as_seq h0 buf == as_seq h1 buf))
let lemma_live_update3 h0 h1 st k0 k1 k2 buf =
  ()
  


val update3:
  log:log_t{UInt32.v (MkLog?.ctr (Ghost.reveal log)) < pow2 32 - 2} ->
  output:uint8_p{length output = 192} ->
  plain:uint8_p{disjoint output plain /\ length plain = 192} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1 /\
      invariant log h0 st /\ live h1 st /\ live h0 st /\
      (match Ghost.reveal log with | MkLog k n ctr ->
       let o = reveal_sbytes (as_seq h1 output) in
       let plain = reveal_sbytes (as_seq h0 plain) in
       let p0 = Seq.slice plain 0 64 in
       let p1 = Seq.slice plain 64 128 in
       let p2 = Seq.slice plain 128 192 in
      let o0 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p0 (Spec.chacha20_cipher k n (U32.v ctr)) in
    let o1 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p1 (Spec.chacha20_cipher k n (U32.v ctr+1)) in
    let o2 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p2 (Spec.chacha20_cipher k n (U32.v ctr+2)) in
       o == FStar.Seq.(o0 @| o1 @| o2) )
       ))

#reset-options "--max_fuel 0 --z3rlimit 200"

let update3 log output plain st =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let k0 = Buffer.create zero 4ul in
  let k1 = Buffer.create zero 4ul in
  let k2 = Buffer.create zero 4ul in
  let h2 = ST.get() in
  assert(live h2 plain);
  chacha20_core3 log k0 k1 k2 st;
  let h3 = ST.get() in
  lemma_live_update3 h2 h3 st k0 k1 k2 plain;
  lemma_live_update3 h2 h3 st k0 k1 k2 output;
  assert(live h3 plain);  
  assert(as_seq h3 plain == as_seq h0 plain);
  assume (let st = as_seq h3 k0 in
          let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
          let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in
          stbytes == stbytes');
  assume (let st = as_seq h3 k1 in
          let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
          let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in
          stbytes == stbytes');
  assume (let st = as_seq h3 k2 in
          let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
          let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in
          stbytes == stbytes');
  let p0 = Buffer.sub plain 0ul   64ul in
  let p1 = Buffer.sub plain 64ul  64ul in
  let p2 = Buffer.sub plain 128ul 64ul in
  let o0 = Buffer.sub output 0ul   64ul in
  let o1 = Buffer.sub output 64ul  64ul in
  let o2 = Buffer.sub output 128ul 64ul in
  xor_block o0 p0 k0;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 o0 p1;
  no_upd_lemma_1 h3 h4 o0 p1;
  no_upd_lemma_1 h3 h4 o0 p2;
  no_upd_lemma_1 h3 h4 o0 k1;
  no_upd_lemma_1 h3 h4 o0 k2;
  xor_block o1 p1 k1;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 o1 o0;
  no_upd_lemma_1 h4 h5 o1 p2;
  no_upd_lemma_1 h4 h5 o1 k2;
  xor_block o2 p2 k2;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 o2 o0;
  no_upd_lemma_1 h5 h6 o2 p1;
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                    let p0 = as_seq h0 p0 in
                    seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p0 (Spec.chacha20_cipher k n (U32.v ctr)))
                    (as_seq h6 o0);
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                    let p1 = as_seq h0 p1 in
                    seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p1 (Spec.chacha20_cipher k n (U32.v ctr+1)))
                    (as_seq h6 o1);
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                    let p2 = as_seq h0 p2 in
                    seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p2 (Spec.chacha20_cipher k n (U32.v ctr+2)))
                    (as_seq h6 o2);
  pop_frame();
  admit()


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
    state_incr log st in
  C.Loops.for 0ul len inv f';
  log


val chacha20_counter_mode_blocks3:
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
let chacha20_counter_mode_blocks3 log output plain len st =
  let len3 = U32.(len /^ 3ul) in
  let rest3 = U32.(len %^ 3ul) in
  let h0 = ST.get() in
  let inv (h1:HyperStack.mem) (i:nat) : Type0 = True in
  let f' (i:UInt32.t{0 <= U32.v i /\ U32.v i < U32.v len3}) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
  =
    let out_sub = Buffer.sub output 0ul U32.(192ul *^ i +^ 192ul) in
    let plain_sub = Buffer.sub plain 0ul U32.(192ul *^ i +^ 192ul) in
    let out_block = Buffer.sub output U32.(192ul *^ i) 192ul in
    let plain_block = Buffer.sub plain U32.(192ul *^ i) 192ul in
    let out_prefix = Buffer.sub output 0ul U32.(192ul *^ i) in
    let plain_prefix = Buffer.sub plain 0ul U32.(192ul *^ i) in
    update3 log out_block plain_block st;
    state_incr log st in
  C.Loops.for 0ul len3 inv f';

  let h0 = ST.get() in
  let inv (h1:HyperStack.mem) (i:nat) : Type0 = True in
  let f' (i:UInt32.t{0 <= U32.v i /\ U32.v i < U32.v rest3}) : Stack unit
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
    state_incr log st in
  C.Loops.for 0ul rest3 inv f';

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
  let log' = chacha20_counter_mode_blocks3 log output' plain' blocks_len st (* ctr *) in
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
