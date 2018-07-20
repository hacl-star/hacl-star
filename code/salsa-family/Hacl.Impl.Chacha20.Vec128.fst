module Hacl.Impl.Chacha20.Vec128

module ST = FStar.HyperStack.ST
module HyperHeap = FStar.Monotonic.HyperHeap

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
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

inline_for_extraction let vecsizebytes2 = 32ul
inline_for_extraction let vecsizebytes3 = 48ul
inline_for_extraction let vecsizebytes4 = 64ul
inline_for_extraction let vecsizebytes8 = 128ul
inline_for_extraction let vecsizebytes12 = 192ul

let idx = a:U32.t{U32.v a < 4}

val as_state: h:HyperStack.mem -> st:state{live h st} -> GTot Spec.state
let as_state h st =
  let st = as_seq h st in let op_String_Access = Seq.index in
  Seq.Create.create_4 (vec_as_seq (st.[0])) (vec_as_seq (st.[1])) (vec_as_seq (st.[2])) (vec_as_seq (st.[3]))

[@ CInline]
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{U32.v s > 0 /\ U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st /\
      as_state h1 st == Spec.line (U32.v a) (U32.v b) (U32.v d) s (as_state h0 st)
      ))
[@ CInline]
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


[@ CInline]
val round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.round (as_state h0 st)))
[@ CInline]
let round st =
  let h0 = ST.get() in
  line st 0ul 1ul 3ul 16ul;
  line st 2ul 3ul 1ul 12ul;
  line st 0ul 1ul 3ul 8ul ;
  line st 2ul 3ul 1ul 7ul;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st) (Spec.round (as_state h0 st))


[@ Substitute]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.column_round (as_state h0 st)))
[@ Substitute]
let column_round st = round st


[@ Substitute]
val shuffle_rows_0123:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.shuffle_rows_0123 (as_state h0 st)))
[@ Substitute]
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


[@ Substitute]
val shuffle_rows_0321:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.shuffle_rows_0321 (as_state h0 st)))
[@ Substitute]
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


[@ Substitute]
val diagonal_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.diagonal_round (as_state h0 st)))
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
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.double_round (as_state h0 st)))
[@ CInline]
let double_round st =
    column_round st;
    diagonal_round st


#reset-options "--max_fuel 0 --z3rlimit 10"

[@ CInline]
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
  Lemma (requires (live h0 st /\ live h0 st' /\ live h0 st'' /\ ST.equal_domains h0 h1 /\
    ST.equal_domains h1 h2 /\ ST.equal_domains h2 h3 /\
    modifies_1 st h0 h1 /\ modifies_1 st' h1 h2 /\ modifies_1 st'' h2 h3))
        (ensures (modifies_3 st st' st'' h0 h3))

#reset-options "--max_fuel 0 --z3rlimit 100"

let lemma_modifies_double_round3 h0 h1 h2 h3 st st' st'' =
  lemma_reveal_modifies_1 st   h0 h1;
  lemma_reveal_modifies_1 st'  h1 h2;
  lemma_reveal_modifies_1 st'' h2 h3;
  lemma_intro_modifies_3 st st' st'' h0 h3


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ CInline]
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


[@ Substitute]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1 /\
      as_state h1 st == Spec.rounds (as_state h0 st)))
[@ Substitute]
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


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ Substitute]
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

[@ Substitute]
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

[@ CInline]
val sum_states:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h1 st' /\ live h1 st /\ modifies_1 st' h0 h1 /\ live h0 st /\
      live h0 st' /\
      (let st1' = as_state h1 st' in let st0' = as_state h0 st' in let st0 = as_state h0 st in
       st1' == Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat st0' st0)))
[@ CInline]
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


[@ CInline]
val copy_state:
  st':state ->
  st:state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st' /\ live h0 st /\ modifies_1 st' h0 h1 /\
      as_state h1 st' == as_state h0 st))
[@ CInline]
let copy_state st' st =
  let h0 = ST.get() in
  let st0 = st.(0ul) in
  let st1 = st.(1ul) in
  let st2 = st.(2ul) in
  let st3 = st.(3ul) in
  st'.(0ul) <- st0;
  st'.(1ul) <- st1;
  st'.(2ul) <- st2;
  st'.(3ul) <- st3;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_state h1 st') (as_state h0 st)


#reset-options "--max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> ctr:UInt32.t -> log_t_
type log_t = Ghost.erased log_t_

let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s = as_state h st in
  match log with | MkLog key nonce ctr -> s == Spec.setup key nonce (UInt32.v ctr))


[@ CInline]
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
[@ CInline]
let chacha20_core log k st =
  let h0 = ST.get() in
  copy_state k st;
  let h1 = ST.get() in
  rounds k;
  let h2 = ST.get() in
  sum_states k st;
  let h3 = ST.get() in
  Seq.lemma_eq_intro (as_state h3 k) (Spec.Loops.seq_map2 Spec.op_Plus_Percent_Hat (as_state h2 k) (as_state h2 st))


#reset-options "--max_fuel 0 --z3rlimit 10"

[@ Substitute]
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


#reset-options "--max_fuel 0 --z3rlimit 50"


[@ Substitute]
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
  Lemma (requires (live h0 st0 /\ live h0 st1 /\ live h0 st2 /\ modifies_1 st0 h0 h1 /\ modifies_1 st1 h1 h2 /\ modifies_1 st2 h2 h3 /\ ST.equal_domains h0 h1 /\ ST.equal_domains h1 h2 /\ ST.equal_domains h2 h3))
        (ensures (modifies_3 st0 st1 st2 h0 h3))
let lemma_chacha_incr3_modifies h0 h1 h2 h3 st0 st1 st2 =
  lemma_reveal_modifies_1 st0 h0 h1;
  lemma_reveal_modifies_1 st1 h1 h2;
  lemma_reveal_modifies_1 st2 h2 h3;
  lemma_intro_modifies_3 st0 st1 st2 h0 h3

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ CInline]
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


[@ CInline]
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
      modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) (FStar.HyperStack.get_hmap h0) (FStar.HyperStack.get_hmap h1) /\ (
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
    ST.equal_domains h0 h1 /\ ST.equal_domains h1 h2 /\
    ST.equal_domains h2 h3 /\ ST.equal_domains h3 h4 /\ ST.equal_domains h4 h5 /\
    modifies_1 k0 h0 h1 /\ modifies_1 st h1 h2 /\ modifies_1 k1 h2 h3 /\ modifies_1 st h3 h4 /\
    modifies_1 k2 h4 h5))
        (ensures (modifies_buf_3 (frameOf k0) k0 k1 k2 h0 h5 /\
          modifies_buf_1 (frameOf st) st h0 h5 /\
          modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) (FStar.HyperStack.get_hmap h0) (FStar.HyperStack.get_hmap h5) ))
let lemma_modifies_sum3 h0 h1 h2 h3 h4 h5 st k0 k1 k2 =
  lemma_reveal_modifies_1 k0 h0 h1;
  lemma_reveal_modifies_1 st h1 h2;
  lemma_reveal_modifies_1 k1 h2 h3;
  lemma_reveal_modifies_1 st h3 h4;
  lemma_reveal_modifies_1 k2 h4 h5

#reset-options "--max_fuel 0 --z3rlimit 200"

[@ CInline]
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



[@ CInline]
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
      modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) (FStar.HyperStack.get_hmap h0) (FStar.HyperStack.get_hmap h1) /\ (
      match Ghost.reveal log with | MkLog k n ctr ->
      UInt32.v ctr < pow2 32 - 2 /\
      as_state h1 st == Spec.setup k n (UInt32.v ctr+2) /\
      as_state h1 k0 == Spec.(chacha20_core (setup k n (UInt32.v ctr))) /\
      as_state h1 k1 == Spec.(chacha20_core (setup k n (UInt32.v ctr + 1))) /\
      as_state h1 k2 == Spec.(chacha20_core (setup k n (UInt32.v ctr + 2))) ) ))


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ CInline]
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


[@ CInline]
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

[@ CInline]
let chacha20_block log stream_block st =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let k = Buffer.create zero 4ul in
  (**) let h1 = ST.get() in
  (**) no_upd_lemma_0 h0 h1 stream_block;
  (**) no_upd_lemma_0 h0 h1 st;
  chacha20_core log k st;
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' k h0 h1 h2;
  (**) no_upd_lemma_1 h1 h2 k stream_block;
  (**) no_upd_lemma_1 h1 h2 k st;
  state_to_key_block stream_block k;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1 stream_block h0 h2 h3;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 stream_block hinit h0 h3 hfin

#reset-options "--max_fuel 0 --z3rlimit 100"

[@ CInline]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 12 /\ disjoint st n} ->
  ctr:UInt32.t ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1 /\
      invariant log h1 st /\
      Ghost.reveal log == MkLog (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) ctr))
[@ CInline]
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
        let o = reveal_sbytes (as_seq h1 output) in
        let plain = reveal_sbytes (as_seq h0 plain) in
         o == (let mask = Spec.chacha20_cipher k n (U32.v ctr) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask)) ))
let update_last log output plain len st =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let block = create (uint8_to_sint8 0uy) vecsizebytes4 in
  (**) let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 plain;
  no_upd_lemma_0 h1 h2 st;
  (**) chacha20_block log block st;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' block h1 h2 h3;
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (Hacl.UInt8.logxor);
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1 output h1 h3 h4;
  pop_frame();
  (**) let h5 = ST.get() in
  (**) modifies_popped_1 output h0 h1 h4 h5


#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_uint32s_fragments:
  h:HyperStack.mem ->
  output:uint8_p{length output = 64 /\ live h output} ->
  a:Seq.seq UInt32.t{Seq.length a = 4} ->
  b:Seq.seq UInt32.t{Seq.length b = 4} ->
  c:Seq.seq UInt32.t{Seq.length c = 4} ->
  d:Seq.seq UInt32.t{Seq.length d = 4} ->
  Lemma (requires (reveal_sbytes (as_seq h (Buffer.sub output 0ul  16ul)) == Spec.Lib.uint32s_to_le 4 a /\
                   reveal_sbytes (as_seq h (Buffer.sub output 16ul 16ul)) == Spec.Lib.uint32s_to_le 4 b /\
                   reveal_sbytes (as_seq h (Buffer.sub output 32ul 16ul)) == Spec.Lib.uint32s_to_le 4 c /\
                   reveal_sbytes (as_seq h (Buffer.sub output 48ul 16ul)) == Spec.Lib.uint32s_to_le 4 d))
        (ensures (reveal_sbytes (as_seq h output) == Spec.Lib.uint32s_to_le 16 FStar.Seq.(a @| b @| c @| d)))

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
  Seq.lemma_eq_intro (Spec.Lib.uint32s_to_le 16 s) (reveal_sbytes (as_seq h output))


#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_uint32s_fragments2:
  h:HyperStack.mem ->
  output:uint8_p{length output = 64 /\ live h output} ->
  a:Seq.seq UInt32.t{Seq.length a = 4} ->
  b:Seq.seq UInt32.t{Seq.length b = 4} ->
  c:Seq.seq UInt32.t{Seq.length c = 4} ->
  d:Seq.seq UInt32.t{Seq.length d = 4} ->
  Lemma (requires (Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h (Buffer.sub output 0ul  16ul))) == a /\
                   Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h (Buffer.sub output 16ul 16ul))) == b /\
                   Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h (Buffer.sub output 32ul 16ul))) == c /\
                   Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h (Buffer.sub output 48ul 16ul))) == d))
        (ensures (Spec.Lib.uint32s_from_le 16 (reveal_sbytes (as_seq h output)) == FStar.Seq.(a @| b @| c @| d)))

#reset-options "--max_fuel 0 --z3rlimit 200"

let lemma_uint32s_fragments2 h output a b c d =
  let open FStar.Seq in
  let s' = reveal_sbytes (as_seq h output) in
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


val lemma_uint32s_fragments3:
  st:Seq.seq vec{Seq.length st = 4} ->
  Lemma ( let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
          let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                               Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))) in
          stbytes == stbytes')
let lemma_uint32s_fragments3 st =
  let a = vec_as_seq (Seq.index st 0) in
  let b = vec_as_seq (Seq.index st 1) in
  let c = vec_as_seq (Seq.index st 2) in
  let d = vec_as_seq (Seq.index st 3) in
  let stbytes' = FStar.Seq.(Spec.Lib.uint32s_to_le 4 a @| Spec.Lib.uint32s_to_le 4 b @|
                               Spec.Lib.uint32s_to_le 4 c @|
                               Spec.Lib.uint32s_to_le 4 d) in
  let open FStar.Seq in
  lemma_eq_intro (slice stbytes' 0 16) (Spec.Lib.uint32s_to_le 4 a);
  lemma_eq_intro (slice stbytes' 16 32) (Spec.Lib.uint32s_to_le 4 b);
  lemma_eq_intro (slice stbytes' 32 48) (Spec.Lib.uint32s_to_le 4 c);
  lemma_eq_intro (slice stbytes' 48 64) (Spec.Lib.uint32s_to_le 4 d);
  let s = a @| b @| c @| d in
  let s02 = a @| b @| c in
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
  Seq.lemma_eq_intro (slice (stbytes') 0 16 @| slice (stbytes') 16 32 @| slice (stbytes') 32 48 @| slice (stbytes') 48 64) stbytes';
  Seq.lemma_eq_intro (Spec.Lib.uint32s_to_le 16 s) (stbytes')


#reset-options "--max_fuel 0 --z3rlimit 200"

[@ "substitute"]
val store_4_vec:
  output:uint8_p{length output = 64} ->
  v0:vec -> v1:vec -> v2:vec -> v3:vec ->
  Stack unit
    (requires (fun h -> live h output))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output /\ modifies_1 output h0 h1 /\
      reveal_sbytes (as_seq h1 output) == FStar.Seq.(Spec.Lib.uint32s_to_le 16 (vec_as_seq v0 @| vec_as_seq v1 @|
                                                                vec_as_seq v2 @| vec_as_seq v3)) ))
[@ "substitute"]
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
  assert(Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h4 o0)) == vec_as_seq v0);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (reveal_sbytes (as_seq h4 o0));
  Spec.Lib.lemma_uint32s_from_le_inj 4 (reveal_sbytes (as_seq h4 o0)) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v0));
  assert(Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h4 o1)) == vec_as_seq v1);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (reveal_sbytes (as_seq h4 o1));
  Spec.Lib.lemma_uint32s_from_le_inj 4 (reveal_sbytes (as_seq h4 o1)) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v1));
  assert(Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h4 o2)) == vec_as_seq v2);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (reveal_sbytes (as_seq h4 o2));
  Spec.Lib.lemma_uint32s_from_le_inj 4 (reveal_sbytes (as_seq h4 o2)) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v2));
  assert(Spec.Lib.uint32s_from_le 4 (reveal_sbytes (as_seq h4 o3)) == vec_as_seq v3);
  Spec.Lib.lemma_uint32s_from_le_bij 4 (reveal_sbytes (as_seq h4 o3));
  Spec.Lib.lemma_uint32s_from_le_inj 4 (reveal_sbytes (as_seq h4 o3)) (Spec.Lib.uint32s_to_le 4 (vec_as_seq v3));
  lemma_uint32s_fragments h4 output (vec_as_seq v0) (vec_as_seq v1) (vec_as_seq v2) (vec_as_seq v3)


#reset-options "--max_fuel 0 --z3rlimit 100"

let flat_state_bytes h (st:state{live h st}) : GTot Spec.Lib.bytes =
  let st = as_seq h st in
  FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
             vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
             vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3)))

val xor_block:
  output:uint8_p{length output = U32.v vecsizebytes4} ->
  plain:uint8_p{disjoint output plain /\ length plain = U32.v vecsizebytes4} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h st))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 st /\ live h0 plain /\
      live h1 output /\ modifies_1 output h0 h1 /\ (
      let st = as_seq h0 st in
      let output = reveal_sbytes (as_seq h1 output) in
      let plain = reveal_sbytes (as_seq h0 plain) in
      // let stbytes = flat_state_bytes h0 st in
      let stbytes = FStar.Seq.(Spec.Lib.uint32s_to_le 16 (
                               vec_as_seq (Seq.index st 0) @| vec_as_seq (Seq.index st 1) @|
                               vec_as_seq (Seq.index st 2) @| vec_as_seq (Seq.index st 3))) in
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
    Spec.Lib.uint32s_from_le 16 (reveal_sbytes (as_seq h0 plain)));
  Hacl.Impl.Xor.Lemmas.lemma_xor_uint32s_to_bytes (reveal_sbytes (as_seq h0 plain)) FStar.Seq.(vec_as_seq k0 @| vec_as_seq k1 @| vec_as_seq k2 @| vec_as_seq k3);
  store_4_vec output o0 o1 o2 o3;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 output)) (let st = as_seq h0 st in
                                         let output = reveal_sbytes (as_seq h1 output) in
                                         let plain = reveal_sbytes (as_seq h0 plain) in
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
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let k = Buffer.create zero 4ul in
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_0 h1 h2 plain;
  (**) no_upd_lemma_0 h1 h2 st;
  chacha20_core log k st;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' k h1 h2 h3;
  (**) lemma_uint32s_fragments3 (as_seq h3 k);
  (**) Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                      Spec.chacha20_cipher k n (UInt32.v ctr))
                     (let st = as_seq h3 k in
                      FStar.Seq.(Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 0)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 1)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 2)) @|
                                 Spec.Lib.uint32s_to_le 4 (vec_as_seq (Seq.index st 3))));
  (**) no_upd_lemma_1 h2 h3 k plain;
  (**) no_upd_lemma_1 h2 h3 k st;
  xor_block output plain k;
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1 output h1 h3 h4;
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h4 output))
                     (let plain = reveal_sbytes (as_seq h0 plain) in
                      match Ghost.reveal log with | MkLog k n ctr ->
                      seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (Spec.chacha20_cipher k n (U32.v ctr)));
  pop_frame();
  (**) let h5 = ST.get() in
  (**) modifies_popped_1 output h0 h1 h4 h5


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
      modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) (FStar.HyperStack.get_hmap h0) (FStar.HyperStack.get_hmap h1) ))
        (ensures (live h1 buf /\ live h0 buf /\ as_seq h0 buf == as_seq h1 buf))
let lemma_live_update3 h0 h1 st k0 k1 k2 buf =
  ()


val log_incrn:
  log:log_t -> m:UInt32.t -> Tot (log':log_t{match Ghost.reveal log, Ghost.reveal log' with
    | MkLog k n c, MkLog k' n' c' -> k == k' /\ n == n' /\ UInt32.v c' == (UInt32.v c + UInt32.v m) % (pow2 32)})
let log_incrn log m =
  Ghost.elift1 (fun l -> match l with | MkLog k n c -> MkLog k n FStar.UInt32.(c +%^ m)) log


val update3:
  log:log_t{UInt32.v (MkLog?.ctr (Ghost.reveal log)) < pow2 32 - 2} ->
  output:uint8_p{length output = 192} ->
  plain:uint8_p{disjoint output plain /\ length plain = 192} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st /\
      (match Ghost.reveal log with
      | MkLog k n ctr -> UInt32.v ctr < pow2 32 - 2)))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ modifies_2 output st h0 h1 /\
      invariant log h0 st /\ live h1 st /\ live h0 st /\
      (match Ghost.reveal log with | MkLog k n ctr ->
       UInt32.v ctr < pow2 32 - 2 /\
       (let updated_log = Ghost.hide (MkLog k n U32.(ctr +^ 2ul)) in
       let o = reveal_sbytes (as_seq h1 output) in
       let plain = reveal_sbytes (as_seq h0 plain) in
       let p0 = Seq.slice plain 0 64 in
       let p1 = Seq.slice plain 64 128 in
       let p2 = Seq.slice plain 128 192 in
      let o0 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p0 (Spec.chacha20_cipher k n (U32.v ctr)) in
    let o1 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p1 (Spec.chacha20_cipher k n (U32.v ctr+1)) in
    let o2 = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p2 (Spec.chacha20_cipher k n (U32.v ctr+2)) in
        invariant updated_log h1 st /\
        o == FStar.Seq.(o0 @| o1 @| o2) ))
       ))


#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_modifies_update3:
  h0:HyperStack.mem ->
  h1:HyperStack.mem{HyperStack.fresh_frame h0 h1} ->
  h2:HyperStack.mem{modifies_0 h1 h2} ->
  h3:HyperStack.mem{ST.equal_domains h2 h3} ->
  h4:HyperStack.mem{ST.equal_domains h3 h4} ->
  h5:HyperStack.mem{ST.equal_domains h4 h5} ->
  h6:HyperStack.mem{ST.equal_domains h5 h6} ->
  h7:HyperStack.mem{HyperStack.popped h6 h7} ->
  output:uint8_p{length output = 192 /\ live h0 output /\ live h1 output /\ live h2 output /\ live h3 output /\ live h4 output /\ live h5 output /\ live h6 output /\ live h7 output} ->
  st:state{live h0 st /\ live h1 st /\ live h2 st /\ live h3 st /\ live h4 st /\ live h5 st /\ live h6 st /\ live h7 st} ->
  k0:state{k0 `unused_in` h1 /\ frameOf k0 = (FStar.HyperStack.get_tip h2) /\ live h2 k0 /\ live h3 k0 /\ live h4 k0 /\ live h5 k0 /\ live h6 k0 /\ disjoint k0 st} ->
  k1:state{k1 `unused_in` h1 /\ frameOf k1 = (FStar.HyperStack.get_tip h2) /\ live h2 k1 /\ live h3 k1 /\ live h4 k1 /\ live h5 k1 /\ live h6 k1 /\ disjoint k1 st /\ disjoint k0 k1} ->
  k2:state{k2 `unused_in` h1 /\ frameOf k2 = (FStar.HyperStack.get_tip h2) /\ live h2 k2 /\ live h3 k2 /\ live h4 k2 /\ live h5 k2 /\ live h6 k2 /\ disjoint st k2 /\ disjoint k0 k2 /\ disjoint k1 k2} ->
  Lemma (requires (
      modifies_buf_3 (frameOf k0) k0 k1 k2 h2 h3 /\
      modifies_buf_1 (frameOf st) st h2 h3 /\
      modifies_just (Set.union (Set.singleton (frameOf st)) (Set.singleton (frameOf k0))) (FStar.HyperStack.get_hmap h3) (FStar.HyperStack.get_hmap h2) /\
      modifies_1 (Buffer.sub output 0ul   64ul) h3 h4 /\
      modifies_1 (Buffer.sub output 64ul  64ul) h4 h5 /\
      modifies_1 (Buffer.sub output 128ul 64ul) h5 h6))
        (ensures (modifies_2 output st h0 h7))
let lemma_modifies_update3 h0 h1 h2 h3 h4 h5 h6 h7 output st k0 k1 k2 =
  lemma_reveal_modifies_0 h1 h2;
  lemma_reveal_modifies_1 (Buffer.sub output 0ul 64ul) h3 h4;
  lemma_reveal_modifies_1 (Buffer.sub output 64ul 64ul) h4 h5;
  lemma_reveal_modifies_1 (Buffer.sub output 128ul 64ul) h5 h6;
  lemma_intro_modifies_2 st output h0 h7


#reset-options "--max_fuel 0 --z3rlimit 200"
// #reset-options "--max_fuel 0 --z3rlimit 10"

let update3 log output plain st =
  assert_norm(pow2 32 = 0x100000000);
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let k0 = Buffer.create zero 4ul in
  let h1' = ST.get() in
  let k1 = Buffer.create zero 4ul in
  let h1'' = ST.get() in
  let k2 = Buffer.create zero 4ul in
  let h2 = ST.get() in
  lemma_modifies_0_0 h1 h1' h1'';
  lemma_modifies_0_0 h1 h1'' h2;
  assert(live h2 plain);
  chacha20_core3 log k0 k1 k2 st;
  let h3 = ST.get() in
  lemma_live_update3 h2 h3 st k0 k1 k2 plain;
  lemma_live_update3 h2 h3 st k0 k1 k2 output;
  assert(live h3 plain);
  assert(as_seq h3 plain == as_seq h0 plain);
  lemma_uint32s_fragments3 (as_seq h3 k0);
  lemma_uint32s_fragments3 (as_seq h3 k1);
  lemma_uint32s_fragments3 (as_seq h3 k2);
  let p0 = Buffer.sub plain 0ul   64ul in
  let p1 = Buffer.sub plain 64ul  64ul in
  let p2 = Buffer.sub plain 128ul 64ul in
  let o0 = Buffer.sub output 0ul   64ul in
  let o1 = Buffer.sub output 64ul  64ul in
  let o2 = Buffer.sub output 128ul 64ul in
  lemma_disjoint_sub plain p0 output;
  lemma_disjoint_sub plain p1 output;
  lemma_disjoint_sub plain p2 output;
  lemma_disjoint_sub output o0 p0;
  lemma_disjoint_sub output o1 p1;
  lemma_disjoint_sub output o2 p2;
  lemma_disjoint_sub plain p0 k0;
  lemma_disjoint_sub plain p1 k1;
  lemma_disjoint_sub plain p2 k2;
  lemma_disjoint_sub output o0 k0;
  lemma_disjoint_sub output o1 k1;
  lemma_disjoint_sub output o2 k2;
  xor_block o0 p0 k0;
  let h4 = ST.get() in
  // Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
  //                   let p0 = reveal_sbytes (as_seq h0 p0) in
  //                   seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p0 (Spec.chacha20_cipher k n (U32.v ctr)))
  //                   (reveal_sbytes (as_seq h4 o0));
  no_upd_lemma_1 h3 h4 o0 p1;
  no_upd_lemma_1 h3 h4 o0 p1;
  no_upd_lemma_1 h3 h4 o0 p2;
  no_upd_lemma_1 h3 h4 o0 k1;
  no_upd_lemma_1 h3 h4 o0 k2;
  no_upd_lemma_1 h3 h4 o0 st;
  assert(as_seq h4 p1 == as_seq h0 p1);
  assert(let ctr = (Ghost.reveal log).ctr in
         let n   = (Ghost.reveal log).n in
         let k   = (Ghost.reveal log).k in
         flat_state_bytes h4 k1 == (Spec.chacha20_cipher k n (U32.v ctr+1)));
  xor_block o1 p1 k1;
  let h5 = ST.get() in
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                    let p1 = reveal_sbytes (as_seq h0 p1) in
                    seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p1 (Spec.chacha20_cipher k n (U32.v ctr+1)))
                    (reveal_sbytes (as_seq h5 o1));
  no_upd_lemma_1 h4 h5 o1 o0;
  no_upd_lemma_1 h4 h5 o1 p2;
  no_upd_lemma_1 h4 h5 o1 k2;
  no_upd_lemma_1 h4 h5 o1 st;
  assert(let ctr = (Ghost.reveal log).ctr in
         let n   = (Ghost.reveal log).n in
         let k   = (Ghost.reveal log).k in
         flat_state_bytes h5 k2 == (Spec.chacha20_cipher k n (U32.v ctr+2)));
  xor_block o2 p2 k2;
  let h6 = ST.get() in
  Seq.lemma_eq_intro (match Ghost.reveal log with | MkLog k n ctr ->
                    let p2 = reveal_sbytes (as_seq h0 p2) in
                    seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p2 (Spec.chacha20_cipher k n (U32.v ctr+2)))
                    (reveal_sbytes (as_seq h6 o2));
  Seq.lemma_eq_intro (as_seq h6 output) FStar.Seq.(as_seq h6 o0 @| as_seq h6 o1 @| as_seq h6 o2);
  no_upd_lemma_1 h5 h6 o2 o0;
  no_upd_lemma_1 h5 h6 o2 p1;
  no_upd_lemma_1 h5 h6 o2 st;
  pop_frame();
  let h7 = ST.get() in
  lemma_modifies_update3 h0 h1 h2 h3 h4 h5 h6 h7 output st k0 k1 k2


#reset-options "--max_fuel 0 --z3rlimit 50"


val update3':
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint plain output} ->
  len:UInt32.t{192 * UInt32.v len = length output /\ length output == length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  i:UInt32.t{UInt32.v i < UInt32.v len} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\
      (match Ghost.reveal log with | MkLog k n ctr -> U32.v ctr + 3 * U32.v len < pow2 32 /\
       (let c' = U32.(ctr +^ 3ul *^  i) in
        let log' = Ghost.hide (MkLog k n c') in
        let plain = Seq.slice (reveal_sbytes (as_seq h plain)) 0 (192 * U32.v i) in
        invariant log' h st /\
        Seq.slice (reveal_sbytes (as_seq h output)) 0 (192 * U32.v i) == Spec.CTR3.counter_mode_blocks3 k n (U32.v ctr) plain (U32.v i)))))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 plain /\ live h0 st /\
        live h1 output /\ live h1 plain /\ live h1 st /\ modifies_2 output st h0 h1 /\
        as_seq h1 plain == as_seq h0 plain /\
      (match Ghost.reveal log with | MkLog k n ctr -> U32.v ctr + 3 * U32.v len < pow2 32 /\
       (let c' = U32.(ctr +^ 3ul *^ i +^ 3ul) in
        let log' = Ghost.hide (MkLog k n c') in
        let plain = Seq.slice (reveal_sbytes (as_seq h0 plain)) 0 (192 * U32.v i + 192) in
        invariant log' h1 st /\
        Seq.slice (reveal_sbytes (as_seq h1 output)) 0 (192 * U32.v i + 192) == Spec.CTR3.counter_mode_blocks3 k n (U32.v ctr) plain (U32.v i + 1)))))

#reset-options "--max_fuel 0 --z3rlimit 700"

let update3' log output plain len st i =
  let h0  = ST.get() in
  let h   = ST.get() in
  let out_sub      = Buffer.sub output 0ul U32.(192ul *^ i +^ 192ul) in
  let plain_sub    = Buffer.sub plain 0ul U32.(192ul *^ i +^ 192ul)  in
  let out_block    = Buffer.sub output U32.(192ul *^ i) 192ul        in
  let plain_block  = Buffer.sub plain U32.(192ul *^ i) 192ul         in
  assert (disjoint out_block plain_block);
  let out_prefix   = Buffer.sub output 0ul U32.(192ul *^ i)          in
  let plain_prefix = Buffer.sub plain 0ul U32.(192ul *^ i)           in
  Seq.lemma_eq_intro (as_seq h out_sub) (Seq.slice (as_seq h output) 0 (192 * U32.v i + 192));
  Seq.lemma_eq_intro (as_seq h plain_sub) (Seq.slice (as_seq h plain) 0 (192 * U32.v i + 192));
  Seq.lemma_eq_intro (as_seq h plain_prefix) (Seq.slice (as_seq h0 plain) 0 (192 * U32.v i));
  Seq.lemma_eq_intro (as_seq h plain_sub) (Seq.append (as_seq h plain_prefix) (as_seq h plain_block));
  Seq.lemma_eq_intro (as_seq h plain_block) (Seq.slice (as_seq h0 plain) (192 * U32.v i) (192 * U32.v i + 192));
  Seq.lemma_eq_intro FStar.Seq.(slice (as_seq h0 plain) 0 (192 * U32.v i) @| slice (as_seq h0 plain) (192 * U32.v i) (192 * U32.v i + 192))
                     (Seq.slice (as_seq h0 plain) 0 (192 * U32.v i + 192));
  Seq.lemma_eq_intro (Seq.slice (as_seq h plain_sub) (192 * U32.v i) (192 * U32.v i + 192))
                     (as_seq h plain_block);
  Seq.lemma_eq_intro (Seq.slice (as_seq h plain_sub) (0) (192 * U32.v i))
                     (as_seq h plain_prefix);
  let log' = log_incrn log U32.(3ul *^ i) in
  Spec.CTR3.lemma_counter_mode_blocks3_def1 (Ghost.reveal log).k (Ghost.reveal log).n (U32.v (Ghost.reveal log).ctr ) (Seq.slice (reveal_sbytes (as_seq h0 plain)) 0 (192 * U32.v i + 192)) (U32.v i + 1);
  update3 log' out_block plain_block st;
  let h'  = ST.get() in
  (**) modifies_subbuffer_2 h h' out_block st output;
  Seq.lemma_eq_intro (Seq.slice (as_seq h' out_sub) (192 * U32.v i) (192 * U32.v i + 192))
                     (as_seq h' out_block);
  Seq.lemma_eq_intro (Seq.slice (as_seq h' out_sub) (0) (192 * U32.v i))
                     (as_seq h' out_prefix);
  Seq.lemma_eq_intro FStar.Seq.(slice (as_seq h' output) 0 (192 * U32.v i) @| slice (as_seq h' output) (192 * U32.v i) (192 * U32.v i + 192))
                       (Seq.slice (as_seq h' output) 0 (192 * U32.v i + 192));
  Seq.lemma_eq_intro (Seq.append (reveal_sbytes (as_seq h out_prefix)) (reveal_sbytes (as_seq h' out_block)))
                     (match Ghost.reveal log with | MkLog k n c ->
                       Spec.CTR3.counter_mode_blocks3 k n (U32.v c) (reveal_sbytes (as_seq h plain_sub)) (U32.v i+1));
  no_upd_lemma_2 h h' out_block st out_prefix;
  no_upd_lemma_2 h h' out_block st plain_prefix;
  no_upd_lemma_2 h h' out_block st plain_block;
  no_upd_lemma_2 h h' out_block st plain;
  let log'' = log_incrn log' 2ul in
  state_incr log'' st;
  (**) let h'' = ST.get() in
  (**) lemma_modifies_2_1' st output h h' h'';
  no_upd_lemma_1 h' h'' st output;
  no_upd_lemma_1 h' h'' st plain;
  no_upd_lemma_1 h' h'' st out_block;
  no_upd_lemma_1 h' h'' st out_prefix;
  no_upd_lemma_1 h' h'' st out_sub;
  no_upd_lemma_1 h' h'' st plain_block;
  no_upd_lemma_1 h' h'' st plain_prefix;
  no_upd_lemma_1 h' h'' st plain_sub;
  assert(match Ghost.reveal log with | MkLog k n c ->
    let c' = U32.(c +^ 3ul *^ (i+^1ul)) in
    let log' = Ghost.hide (MkLog k n c') in
    invariant log' h'' st);
  Seq.lemma_eq_intro (as_seq h'' out_sub) (Seq.append (as_seq h out_prefix) (as_seq h' out_block));
  Seq.lemma_eq_intro (Seq.slice (reveal_sbytes (as_seq h'' output)) 0 (192 * U32.v i + 192))
                     (match Ghost.reveal log with | MkLog k n c ->
                      Spec.CTR3.counter_mode_blocks3 k n (UInt32.v c) (Seq.slice (reveal_sbytes (as_seq h0 plain)) 0 (192 * U32.v i + 192)) (U32.v i+1))


val chacha20_counter_mode_blocks3:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint plain output} ->
  len:UInt32.t{192 * UInt32.v len = length output /\ length output == length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st /\
      (match Ghost.reveal log with | MkLog _ _ ctr -> (U32.v ctr + 3 * U32.v len < pow2 32))))
    (ensures (fun h0 _ h1 -> live h0 plain /\ live h0 st /\ invariant log h0 st /\
      live h1 st /\ live h1 output /\ modifies_2 output st h0 h1 /\
      (match Ghost.reveal log with
       | MkLog k n ctr ->
         U32.v ctr + 3 * UInt32.v len < pow2 32 /\ (
         let updated_log = Ghost.hide (MkLog k n U32.(ctr +^ 3ul *^ len)) in
         let output = reveal_sbytes (as_seq h1 output) in let plain = reveal_sbytes (as_seq h0 plain) in
         invariant updated_log h1 st /\
         output == Spec.CTR3.counter_mode_blocks3 k n (U32.v ctr) plain (U32.v len)))))

#reset-options "--max_fuel 0 --z3rlimit 200"

val lemma_modifies_nothing_modifies_2:
  h:HyperStack.mem ->
  out:uint8_p{live h out} ->
  st:state{live h st /\ disjoint st out} ->
  Lemma (modifies_2 out st h h)
let lemma_modifies_nothing_modifies_2 h out st =
  lemma_intro_modifies_2 out st h h

#reset-options "--max_fuel 0 --z3rlimit 300"

let chacha20_counter_mode_blocks3 log output plain len st =
  let h0 = ST.get() in
  let inv (h1:HyperStack.mem) (i:nat) : Type0 =
    live h1 output /\ live h1 plain /\ live h1 st /\ modifies_2 output st h0 h1 /\
    as_seq h1 plain == as_seq h0 plain /\ i <= U32.v len /\
    (match Ghost.reveal log with | MkLog k n c ->
     let c' = U32.(c +^ 3ul *^ UInt32.uint_to_t i) in
     let log' = Ghost.hide (MkLog k n c') in
     let plain = Seq.slice (reveal_sbytes (as_seq h0 plain)) 0 (192 * i) in
     invariant log' h1 st /\
     Seq.slice (reveal_sbytes (as_seq h1 output)) 0 (192 * i) == Spec.CTR3.counter_mode_blocks3 k n (UInt32.v c) plain i)
  in
  let f' (i:UInt32.t{0 <= U32.v i /\ U32.v i < U32.v len}) : Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
  =
    let h   = ST.get() in
    update3' log output plain len st i;
    let h'  = ST.get() in
    (**) lemma_modifies_2_trans output st h0 h h';
    ()
    in
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) (Seq.createEmpty);
  Spec.CTR3.lemma_counter_mode_blocks3_def0 (Ghost.reveal log).k (Ghost.reveal log).n (U32.v (Ghost.reveal log).ctr) (Seq.slice (reveal_sbytes (as_seq h0 plain)) 0 0);
  C.Loops.for 0ul len inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (Seq.slice (as_seq h1 output) 0 (length output));
  Seq.lemma_eq_intro (as_seq h0 plain) (Seq.slice (as_seq h0 plain) 0 (length plain));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h1 output))
                     (Spec.CTR3.counter_mode_blocks3 (Ghost.reveal log).k (Ghost.reveal log).n (U32.v (Ghost.reveal log).ctr) (reveal_sbytes (as_seq h0 plain)) (U32.v len))


#reset-options "--max_fuel 0 --z3rlimit 20"

val chacha20_counter_mode_blocks:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint plain output} ->
  len:UInt32.t{64 * UInt32.v len = length output /\ length output == length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st /\
      (match Ghost.reveal log with | MkLog _ _ ctr -> (U32.v ctr + U32.v len < pow2 32))))
    (ensures (fun h0 _ h1 -> live h0 plain /\ live h0 st /\ invariant log h0 st /\
      live h1 st /\ live h1 output /\ modifies_2 output st h0 h1 /\
      (match Ghost.reveal log with
       | MkLog k n ctr ->
         U32.v ctr + U32.v len < pow2 32 /\
         (let updated_log = Ghost.hide (MkLog k n U32.(ctr +^ len)) in
         let output = reveal_sbytes (as_seq h1 output) in let plain = reveal_sbytes (as_seq h0 plain) in
         invariant updated_log h1 st /\
         output == Spec.CTR3.counter_mode_blocks k n (U32.v ctr) plain (U32.v len)))))

#reset-options "--max_fuel 0 --z3rlimit 200"

let chacha20_counter_mode_blocks log output plain len st =
  Math.Lemmas.lemma_div_mod (U32.v len) 3;
  assert(U32.v len = 3 * (U32.v len / 3) + (U32.v len % 3));
  assert(length plain = 64 * (3 * (U32.v len / 3) + (U32.v len % 3)));
  Math.Lemmas.distributivity_add_right 64 (3 * (U32.v len / 3)) (U32.v len % 3);
  assert(length plain = 192 * (U32.v len / 3) + 64 * (U32.v len % 3));
  let len3 = U32.(len /^ 3ul) in
  let rest3 = U32.(len %^ 3ul) in
  let plain' = Buffer.sub plain 0ul U32.(192ul *^ len3) in
  let blocks = Buffer.sub plain U32.(192ul *^ len3) U32.(64ul *^ rest3) in
  let output' = Buffer.sub output 0ul U32.(192ul *^ len3) in
  let outs   = Buffer.sub output U32.(192ul *^ len3) U32.(64ul *^ rest3) in
  let h0 = ST.get() in
  chacha20_counter_mode_blocks3 log output' plain' len3 st;
  let h1 = ST.get() in
  let log' = log_incrn log U32.(3ul *^ len3) in
  Math.Lemmas.modulo_lemma (U32.v (Ghost.reveal log).ctr + 3 * U32.v len3) (pow2 32);
  if rest3 = 2ul then (
    Math.Lemmas.modulo_lemma (U32.v (Ghost.reveal log).ctr + 3 * U32.v len3 + 1) (pow2 32);
    no_upd_lemma_2 h0 h1 output' st blocks;
    let block0 = Buffer.sub blocks 0ul 64ul in
    let block1 = Buffer.sub blocks 64ul 64ul in
    let out0   = Buffer.sub outs 0ul 64ul in
    let out1   = Buffer.sub outs 64ul 64ul in
    update log' out0 block0 st;
    let h2 = ST.get() in
    Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 out0)) (Spec.CTR.xor #64 (reveal_sbytes (as_seq h0 block0)) (match Ghost.reveal log' with | MkLog k n c -> Spec.Chacha20_vec.chacha20_block k n (UInt32.v c)));
    no_upd_lemma_1 h1 h2 out0 output';
    no_upd_lemma_1 h1 h2 out0 block1;
    no_upd_lemma_1 h1 h2 out0 st;
    state_incr log' st;
    let h3 = ST.get() in
    no_upd_lemma_1 h2 h3 st out0;
    no_upd_lemma_1 h2 h3 st block1;
    let log'' = log_incr log' in
    update log'' out1 block1 st;
    let h4 = ST.get() in
    Seq.lemma_eq_intro (reveal_sbytes (as_seq h4 out1)) (Spec.CTR.xor #64 (reveal_sbytes (as_seq h0 block1)) (match Ghost.reveal log' with | MkLog k n c -> Spec.Chacha20_vec.chacha20_block k n (UInt32.v c+1)));
    no_upd_lemma_1 h3 h4 out1 out0;
    Seq.lemma_eq_intro (as_seq h4 output) FStar.Seq.(as_seq h2 output' @| (as_seq h4 out0 @| as_seq h4 out1));
    state_incr log'' st;
    let h5 = ST.get() in
    no_upd_lemma_1 h4 h5 st output
  ) else if rest3 = 1ul then (
    no_upd_lemma_2 h0 h1 output' st blocks;
    update log' outs blocks st;
    let h2 = ST.get() in
    Seq.lemma_eq_intro (reveal_sbytes (as_seq h2 outs)) (Spec.CTR.xor #64 (reveal_sbytes (as_seq h0 blocks)) (match Ghost.reveal log' with | MkLog k n c -> Spec.Chacha20_vec.chacha20_block k n (UInt32.v c)));
    no_upd_lemma_1 h1 h2 outs output';
    Seq.lemma_eq_intro (as_seq h2 output) (Seq.append (as_seq h2 output') (as_seq h2 outs));
    state_incr log' st;
    let h3 = ST.get() in
    no_upd_lemma_1 h2 h3 st output
  ) else (
    Seq.lemma_eq_intro (as_seq h1 output') (Seq.append (as_seq h1 output) (Seq.createEmpty))
  )


#reset-options "--max_fuel 0 --z3rlimit 20"

val chacha20_counter_mode:
  log:log_t ->
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  st:state{disjoint st output /\ disjoint st plain} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st /\
      (match Ghost.reveal log with | MkLog _ _ ctr -> (U32.v ctr + U32.v len / 64 < pow2 32))))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ctr ->
         U32.v ctr + U32.v len / 64 < pow2 32 /\ o == Spec.CTR3.counter_mode k n (UInt32.v ctr) plain)))

#reset-options "--max_fuel 0 --z3rlimit 200"

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
  chacha20_counter_mode_blocks log output' plain' blocks_len st;
  let log' = log_incrn log blocks_len in
  let h1 = ST.get() in
  Math.Lemmas.modulo_lemma (U32.v (Ghost.reveal log).ctr + U32.v blocks_len) (pow2 32);
  assert(invariant log' h1 st);
  if FStar.UInt32.(part_len >^ 0ul) then (
    let _ = update_last log' output'' plain'' part_len st in
    ())
  else ();
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.append (as_seq h output') Seq.createEmpty) (as_seq h output');
  Seq.lemma_eq_intro (as_seq h output) (Seq.append (as_seq h output') (as_seq h output''));
  Seq.lemma_eq_intro (as_seq h0 plain) (Seq.append (as_seq h0 plain') (as_seq h0 plain''));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.CTR3.counter_mode (Ghost.reveal log).k (Ghost.reveal log).n (U32.v (Ghost.reveal log).ctr) (reveal_sbytes (as_seq h0 plain)));
  ()

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
      /\ modifies_1 output h0 h1 /\ (
        let output = reveal_sbytes (as_seq h1 output) in
        let key    = reveal_sbytes (as_seq h0 key) in
        let nonce  = reveal_sbytes (as_seq h0 nonce) in
        let ctr    = UInt32.v ctr in
        let plain  = reveal_sbytes (as_seq h0 plain) in
        output == Spec.Chacha20_vec.chacha20_encrypt_bytes key nonce ctr plain)))

#reset-options "--max_fuel 0 --z3rlimit 100"

let chacha20 output plain len k n ctr =
  (**) let h = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let st = state_alloc () in
  (**) let h0' = ST.get() in
  let log = init st k n ctr in
  (**) let h1 = ST.get() in
  (**) lemma_modifies_0_1' st h0 h0' h1;
  no_upd_lemma_0 h0 h1 plain;
  no_upd_lemma_0 h0 h1 k;
  no_upd_lemma_0 h0 h1 n;
  no_upd_lemma_0 h0 h1 output;
  assert(as_seq h1 plain == as_seq h plain);
  assert(invariant log h1 st);
  assert(Ghost.reveal log == MkLog (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) ctr);
  chacha20_counter_mode log output plain len st;
  let h2 = ST.get() in
  (**) lemma_modifies_0_2 output st h0 h1 h2;
  assert(
    let k = reveal_sbytes (as_seq h0 k) in let n = reveal_sbytes (as_seq h0 n) in let plain = reveal_sbytes (as_seq h1 plain) in
    reveal_sbytes (as_seq h2 output) == Spec.CTR3.counter_mode k n (UInt32.v ctr) plain);
  Spec.CTR3.lemma_counter_mode3_eq (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) (UInt32.v ctr) (reveal_sbytes (as_seq h0 plain));
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 output h h0 h2 hfin
