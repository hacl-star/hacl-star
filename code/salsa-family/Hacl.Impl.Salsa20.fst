module Hacl.Impl.Salsa20

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Salsa20
open C.Loops
open Hacl.Lib.LoadStore32
open Hacl.Lib.Create

module Spec = Spec.Salsa20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

#reset-options "--max_fuel 0  --z3rlimit 100"

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

private inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{0 < U32.v s && U32.v s < 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


[@ CInline]
private
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 8 /\ disjoint st n} ->
  c:UInt64.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let k = reveal_sbytes (as_seq h0 k) in
         let n = reveal_sbytes (as_seq h0 n) in
         s == setup k n (UInt64.v c))))
[@ CInline]
let setup st k n c =
  let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let tmp = Buffer.create (uint32_to_sint32 0ul) 10ul in
  (**) let h2 = ST.get() in
  let k'  = Buffer.sub tmp 0ul 8ul in
  let n'  = Buffer.sub tmp 8ul 2ul in
  uint32s_from_le_bytes k' k 8ul;
  (**) let h3 = ST.get() in
  (**) modifies_subbuffer_1 h2 h3 k' tmp;
  uint32s_from_le_bytes n' n 2ul;
  (**) let h4 = ST.get() in
  (**) modifies_subbuffer_1 h3 h4 n' tmp;
  (**) lemma_modifies_1_trans tmp h2 h3 h4;
  (**) lemma_modifies_0_1' tmp h1 h2 h4;
  let c0 = uint32_to_sint32 (FStar.Int.Cast.uint64_to_uint32 c) in
  let c1 = uint32_to_sint32 (FStar.Int.Cast.uint64_to_uint32 FStar.UInt64.(c >>^ 32ul)) in
  let k0 = k'.(0ul) in
  let k1 = k'.(1ul) in
  let k2 = k'.(2ul) in
  let k3 = k'.(3ul) in
  let k4 = k'.(4ul) in
  let k5 = k'.(5ul) in
  let k6 = k'.(6ul) in
  let k7 = k'.(7ul) in
  let n0 = n'.(0ul) in
  let n1 = n'.(1ul) in
  make_h32_16 st (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0 c1
               (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3);
  (**) let h5 = ST.get() in
  (**) lemma_modifies_0_1 st h1 h4 h5;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 st h0 h1 h5 hfin


let idx = a:U32.t{U32.v a < 16}

[@ CInline]
private
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{0 < U32.v s && U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st
      /\ (let st1 = reveal_h32s (as_seq h1 st) in
         let st0 = reveal_h32s (as_seq h0 st) in
         st1 == line (U32.v a) (U32.v b) (U32.v d) s st0)))
[@ CInline]
let line st a b d s =
  let sa = st.(a) in let sb = st.(b) in let sd = st.(d) in
  let sbd = sb +%^ sd in
  let sbds = sbd <<< s in
  st.(a) <- (sa ^^ sbds)


[@ CInline]
private
val quarter_round:
  st:state ->
  a:idx -> b:idx -> c:idx -> d:idx ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == quarter_round (U32.v a) (U32.v b) (U32.v c) (U32.v d) s)))
[@ CInline]
let quarter_round st a b c d =
  line st b a d 7ul;
  line st c b a 9ul;
  line st d c b 13ul;
  line st a d c 18ul


[@ Substitute]
private
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == column_round s)))
[@ Substitute]
let column_round st =
  quarter_round st 0ul  4ul  8ul  12ul;
  quarter_round st 5ul  9ul  13ul 1ul;
  quarter_round st 10ul 14ul 2ul  6ul;
  quarter_round st 15ul 3ul  7ul  11ul


[@ Substitute]
private
val row_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == row_round s)))
[@ Substitute]
let row_round st =
  quarter_round st 0ul  1ul   2ul  3ul;
  quarter_round st 5ul  6ul   7ul  4ul;
  quarter_round st 10ul 11ul 8ul  9ul;
  quarter_round st 15ul 12ul 13ul 14ul


[@ CInline]
private
val double_round:
  st:buffer H32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == double_round s)))
[@ CInline]
let double_round st =
    column_round st;
    row_round st


#reset-options "--max_fuel 0  --z3rlimit 100"

[@ CInline]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == Spec.Salsa20.rounds s)))
[@ CInline]
let rounds st =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 st /\ modifies_1 st h0 h1 /\ i <= 10
    /\ (let s' = reveal_h32s (as_seq h1 st) in
       let s  = reveal_h32s (as_seq h0 st) in
       s' == repeat_spec i Spec.Salsa20.double_round s)
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < 10 ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = double_round st;
    Spec.Loops.lemma_repeat (UInt32.v i + 1) Spec.Salsa20.double_round (reveal_h32s (as_seq h0 st))
  in
  lemma_repeat_0 0 Spec.Salsa20.double_round (reveal_h32s (as_seq h0 st));
  for 0ul 10ul inv f'


#reset-options "--max_fuel 0 --z3rlimit 100"

[@ CInline]
private
val sum_states:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s1 = as_seq h1 st in let s = as_seq h0 st in let s' = as_seq h0 st' in
         s1 == seq_map2 (fun x y -> H32.(x +%^ y)) s s')))
[@ CInline]
let sum_states st st' =
  in_place_map2 st st' 16ul (fun x y -> H32.(x +%^ y))


[@ CInline]
private
val copy_state:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st' in let s' = as_seq h1 st in s' == s)))
[@ CInline]
let copy_state st st' =
  Buffer.blit st' 0ul st 0ul 16ul;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h st) (Seq.slice (as_seq h st) 0 16);
  Seq.lemma_eq_intro (as_seq h st') (Seq.slice (as_seq h st') 0 16);
  Seq.lemma_eq_intro (as_seq h st) (as_seq h st')


#reset-options "--max_fuel 0 --z3rlimit 100"

type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> log_t_
type log_t = Ghost.erased log_t_


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
let u64_of_u32s (low:U32.t) (high:U32.t) : Tot (x:UInt64.t{UInt64.v x = pow2 32 * UInt32.v high + UInt32.v low}) =
  let h = FStar.UInt64.(Int.Cast.uint32_to_uint64 high <<^ 32ul) in
  Math.Lemmas.modulo_lemma (UInt64.v h) (pow2 64);
  let l = (Int.Cast.uint32_to_uint64 low) in
  let c = UInt64.logor h l in
  UInt.logor_disjoint #64 (UInt64.v h) (UInt64.v l) 32;
  c


inline_for_extraction
let low32_of_u64 (x:UInt64.t) : Tot (y:UInt32.t{UInt32.v y = UInt64.v x % pow2 32}) =
  Int.Cast.uint64_to_uint32 x

inline_for_extraction
let high32_of_u64 (x:UInt64.t) : Tot (y:UInt32.t{UInt32.v y = UInt64.v x / pow2 32}) =
  let x' = FStar.UInt64.(x >>^ 32ul) in
  Math.Lemmas.lemma_div_lt (UInt64.v x) 64 32;
  Math.Lemmas.modulo_lemma (UInt64.v x / pow2 32) (pow2 32);
  Int.Cast.uint64_to_uint32 x'


(* Invariant on the state recording which block was computed last *)
let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s   = as_seq h st in
    match log with | MkLog key nonce -> reveal_h32s s == Spec.setup key nonce (UInt64.v (u64_of_u32s (h32_to_u32 (Seq.index s 8)) (h32_to_u32 (Seq.index s 9)))))


module H64 = Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 200"

private
val lemma_invariant:
  st:Spec.state ->
  k:Spec.key -> n:Spec.nonce -> c:H64.t -> c':H64.t -> Lemma
    (requires (st == Spec.setup k n (H64.v c)))
    (ensures (let l = low32_of_u64 (h64_to_u64 c') in let h = high32_of_u64 (h64_to_u64 c') in
      Seq.upd (Seq.upd st 8 l) 9 h == Spec.setup k n (H64.v c')))
let lemma_invariant s k n c c' =
  let kk = k in
  let nn = n in
  let c = h64_to_u64 c in
  let c' = h64_to_u64 c' in
  let c0 = low32_of_u64 c in
  let c1 = high32_of_u64 c in
  let c0' = low32_of_u64 c' in
  let c1' = high32_of_u64 c' in
  let s' = intro_h32s (Seq.upd (Seq.upd s 8 c0') 9 c1') in
  let c0 = uint32_to_sint32 c0 in
  let c1 = uint32_to_sint32 c1 in
  let c0' = uint32_to_sint32 c0' in
  let c1' = uint32_to_sint32 c1' in
  let k = intro_h32s (Spec.Lib.uint32s_from_le 8 k) in
  let n = intro_h32s (Spec.Lib.uint32s_from_le 2 n) in
  let s = intro_h32s (s) in
  let k0 = Seq.index k 0 in
  let k1 = Seq.index k 1 in
  let k2 = Seq.index k 2 in
  let k3 = Seq.index k 3 in
  let k4 = Seq.index k 4 in
  let k5 = Seq.index k 5 in
  let k6 = Seq.index k 6 in
  let k7 = Seq.index k 7 in
  let n0 = Seq.index n 0 in
  let n1 = Seq.index n 1 in
  cut (intro_h32s (Spec.Salsa20.setup kk nn (UInt64.v c)) ==
                  Seq.Create.create_16 (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0 c1 (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3));
  cut (intro_h32s (Spec.Salsa20.setup kk nn (UInt64.v c')) ==
                  Seq.Create.create_16 (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0' c1' (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3));
  Seq.lemma_eq_intro s' (Seq.Create.create_16 (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0' c1' (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3))


private
val lemma_state_counter:
  k:Spec.key -> n:Spec.nonce -> c:Spec.counter ->
  Lemma (U32.v (Seq.index (Spec.setup k n c) 8) == c % pow2 32 /\ U32.v (Seq.index (Spec.setup k n c) 9) == c / pow2 32)
let lemma_state_counter k n c = ()


#reset-options "--max_fuel 0  --z3rlimit 100"

private
let lemma_u64_of_u32s (low:U32.t) (high:U32.t) : Lemma (low32_of_u64 (u64_of_u32s low high) = low /\ high32_of_u64 (u64_of_u32s low high) = high) =
  let low' = low32_of_u64 (u64_of_u32s low high) in
  cut (U32.v low' = (U32.v low + pow2 32 * U32.v high) % pow2 32);
  Math.Lemmas.lemma_mod_plus (U32.v low) (U32.v high) (pow2 32);
  Math.Lemmas.modulo_lemma (U32.v low) (pow2 32);
  cut (U32.v low' = U32.v low);
  Math.Lemmas.lemma_div_mod (UInt64.v (u64_of_u32s low high)) (pow2 32)


#reset-options "--max_fuel 0  --z3rlimit 100"

[@ CInline]
private
val salsa20_core:
  log:log_t ->
  k:state ->
  st:state{disjoint st k} ->
  ctr:UInt64.t ->
  Stack log_t
    (requires (fun h -> live h k /\ live h st /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h0 st /\ live h0 k /\ invariant log h0 st
      /\ live h1 k /\ invariant updated_log h1 st /\ modifies_2 k st h0 h1
      /\ (let key = reveal_h32s (as_seq h1 k) in
          let stv = reveal_h32s (as_seq h1 st) in
          Seq.index stv 8 == low32_of_u64 ctr /\
          Seq.index stv 9 == high32_of_u64 ctr /\
         (match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             key == salsa20_core stv /\ k == k' /\ n == n'))))
[@ CInline]
let salsa20_core log k st ctr =
  let h0 = ST.get() in
  let c0 = uint32_to_sint32 (low32_of_u64 ctr) in
  let c1 = uint32_to_sint32 (high32_of_u64 ctr) in
  let h1 = ST.get() in
  st.(8ul) <- c0;
  let h' = ST.get() in
  cut (as_seq h' st == Seq.upd (as_seq h1 st) 8 (c0));
  st.(9ul) <- c1;
  let h2 = ST.get() in
  cut (as_seq h2 st == Seq.upd (as_seq h' st) 9 (c1));
  cut (get h2 st 8 == c0 /\ get h2 st 9 == c1);
  cut (let s = as_seq h0 st in let s' = as_seq h2 st in s' == Seq.upd (Seq.upd s 8 c0) 9 c1);
  // GM: Need these explicit bindings as a workaround to FStarLang/FStar#1368
  (let hh8 = h32_to_u32 (get h0 st 8) in
   let hh9 = h32_to_u32 (get h0 st 9) in
   lemma_invariant (reveal_h32s (as_seq h0 st)) (Ghost.reveal log).k (Ghost.reveal log).n (uint64_to_sint64 (u64_of_u32s hh8 hh9)) (uint64_to_sint64 ctr));
  lemma_u64_of_u32s (h32_to_u32 c0) (h32_to_u32 c1);
  cut (invariant log h2 st);
  copy_state k st;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 k st;
  rounds k;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 k st;
  sum_states k st;
  let h5 = ST.get() in
  no_upd_lemma_1 h4 h5 k st;
  let h = ST.get() in
  Seq.lemma_eq_intro (reveal_h32s (as_seq h k)) (salsa20_core (reveal_h32s (as_seq h st)));
  log


[@ CInline]
val salsa20_block:
  log:log_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  ctr:UInt64.t ->
  Stack log_t
    (requires (fun h -> live h stream_block /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ invariant log h0 st
      /\ invariant updated_log h1 st /\ modifies_2 stream_block st h0 h1
      /\ (let block = reveal_sbytes (as_seq h1 stream_block) in
         match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             block == salsa20_block k n (UInt64.v ctr) /\ k == k' /\ n == n')))
[@ CInline]
let salsa20_block log stream_block st ctr =
  let h0 = ST.get() in
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h_0 = ST.get() in
  let st' = Buffer.create (uint32_to_sint32 0ul) 16ul in
  (**) let h1 = ST.get() in
  (**) let h_1 = ST.get() in
  (**) no_upd_lemma_0 h_0 h_1 st;
  (**) assert (as_seq h0 st == as_seq h_1 st);
  let log = salsa20_core log st' st ctr in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_2' st st' h_0 h1 h2;
  (**) let h_3 = ST.get() in
  uint32s_to_le_bytes stream_block st' 16ul;
  (**) let h_4 = ST.get() in
  (**) let h = ST.get() in
  (**) lemma_modifies_2_1'' st stream_block h_0 h2 h;
  (**) assert (reveal_sbytes (as_seq h stream_block) == salsa20_block (Ghost.reveal log).k (Ghost.reveal log).n (UInt64.v ctr));
  (**) assert (modifies_3_2 stream_block st h_0 h);
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 stream_block st h0 h_0 h hfin;
  log


[@ CInline]
val alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> (st `unmapped_in` h0) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == (HS.get_tip h1)))
[@ CInline]
let alloc () =
  create (uint32_to_sint32 0ul) 16ul


(* val intro_log: *)
(*   h:HyperStack.mem -> *)
(*   k:uint8_p{length k = 32 /\ live h k} -> *)
(*   n:uint8_p{length n = 8 /\ live h n} -> *)
(*   Tot (l:log_t{as_seq h k == (Ghost.reveal l).k /\ as_seq h n == (Ghost.reveal l).n}) *)
(* let intro_log h k n = *)
(*   let log = *)
(*   Ghost.elift2 (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 8 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n))) (Ghost.hide k) (Ghost.hide n) in *)
(*   log *)
(*   (\* assert(Ghost.reveal log == (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 8 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n))) k n); *\) *)
(*   (\* assert((Ghost.reveal log).k == as_seq h k); admit() *\) *)
(*   (\* Seq.lemma_eq_intro (as_seq h k) (Ghost.reveal log).k; admit() *\) *)



[@ CInline]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 8 /\ disjoint st n} ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1
      /\ invariant log h1 st
      /\ (match Ghost.reveal log with MkLog k' n' -> k' == reveal_sbytes (as_seq h0 k)
          /\ n' == reveal_sbytes (as_seq h0 n))))
[@ CInline]
let init st k n =
  let h0 = ST.get() in
  setup st k n 0uL;
  let h = ST.get() in
  lemma_state_counter (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) 0;
  cut (reveal_h32s (as_seq h st) == Spec.setup (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) 0);
  Ghost.elift2 (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 8 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n))) (Ghost.hide k) (Ghost.hide n)


private
val lemma_salsa20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len < 64 /\ U32.v len > 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (as_seq hi input))
     == Spec.CTR.xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 (U32.v len)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_salsa20_counter_mode_1 ho output hi input len k n ctr =
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  Math.Lemmas.modulo_lemma (UInt32.v len) 64;
  assert(UInt32.v len / (Spec.CTR.(salsa20_ctx.blocklen * salsa20_ctx.incr)) = 0);
  let open Spec.CTR in
  assert((xor #(UInt32.v len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 (UInt32.v len))) == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 (UInt32.v len)));
  let ctx = salsa20_ctx in
  let len:nat = UInt32.v len in
  let counter = UInt64.v ctr in
  let blocks_len = (ctx.incr * ctx.blocklen) * (len / (ctx.blocklen * ctx.incr)) in
  let part_len   = len % (ctx.blocklen * ctx.incr) in
    (* TODO: move to a single lemma for clarify *)
    Math.Lemmas.lemma_div_mod len (ctx.blocklen * ctx.incr);
    Math.Lemmas.multiple_modulo_lemma (len / (ctx.blocklen * ctx.incr)) (ctx.blocklen * ctx.incr);
    Math.Lemmas.lemma_div_le (blocks_len) len ctx.blocklen;
    (* End TODO *)
  let blocks, last_block = Seq.split (as_seq hi input) blocks_len in
  let cipher_blocks = counter_mode_blocks ctx salsa20_cipher k n counter (reveal_sbytes blocks) in
  Seq.lemma_eq_intro cipher_blocks Seq.createEmpty;
  assert(ctx.incr * (Seq.length (as_seq hi input) / ctx.blocklen) = 0);
  Seq.lemma_eq_intro (Seq.append Seq.createEmpty (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 len))) (xor #len (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 len));
  Seq.lemma_eq_intro (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (as_seq hi input)))
                     (Spec.CTR.xor #(len) (reveal_sbytes (as_seq hi input)) (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 (len)))


#reset-options "--max_fuel 0 --z3rlimit 100"

private
val lemma_salsa20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len >= 64
    /\ UInt32.v len % 64 = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr)
                                  (reveal_sbytes (as_seq hi input))
    == (let prefix, block = Seq.split (as_seq hi input) (UInt32.v len - 64) in
      Math.Lemmas.lemma_mod_plus (Seq.length prefix) 1 (64);
      Math.Lemmas.lemma_div_le (Seq.length prefix) (UInt32.v len) 64;
      Spec.CTR.Lemmas.lemma_div (UInt32.v len) (64);
    let cipher        = Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes prefix) in
    let mask          = salsa20_cipher k n (UInt64.v ctr + (UInt32.v len / 64 - 1) ) in
    let eb            = Spec.CTR.xor (reveal_sbytes block) mask in
    Seq.append cipher eb))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_2 ho output hi input len k n ctr = ()


#reset-options "--max_fuel 0 --z3rlimit 100"

private
val lemma_salsa20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr)
                                  (reveal_sbytes (as_seq hi input))
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_0 ho output hi input len k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty


#reset-options "--max_fuel 0 --z3rlimit 100"

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len < 64 /\ UInt32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == (let mask = salsa20_cipher k n (UInt64.v ctr+(UInt32.v len / 64)) in
               let mask = Seq.slice mask 0 (UInt32.v len) in
               Spec.CTR.xor #(UInt32.v len) plain mask))))
let update_last output plain len log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h = ST.get() in
  let block = create (uint8_to_sint8 0uy) 64ul in
  (**) let h' = ST.get() in
  let l = salsa20_block log block st ctr in
  (**) let h'' = ST.get() in
  (**) lemma_modifies_0_2' st block h h' h'';
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (fun x y -> H8.(x ^^ y));
  (**) let h1 = ST.get() in
  (**) lemma_modifies_2_1'' st output h h'' h1;
  (**) lemma_salsa20_counter_mode_1 h1 output h0 plain len (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 st output h0 h h1 hfin;
  l


val update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + 1 < pow2 64} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ updated_log == log
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (salsa20_cipher k n (UInt64.v ctr)))))
let update output plain log st ctr =
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let b  = create (uint32_to_sint32 0ul) 48ul in
  (**) let h2 = ST.get() in
  let k  = Buffer.sub b 0ul  16ul in
  let ib = Buffer.sub b 16ul 16ul in
  let ob = Buffer.sub b 32ul 16ul in
  let l  = salsa20_core log k st ctr in
  (**) let h3 = ST.get() in
  (**) modifies_subbuffer_2 h2 h3 k st b;
  uint32s_from_le_bytes ib plain 16ul;
  (**) let h = ST.get() in
  (**) modifies_subbuffer_1 h3 h ib b;
  map2 ob ib k 16ul (fun x y -> H32.(x ^^ y));
  (**) let h4  = ST.get() in
  (**) modifies_subbuffer_1 h h4 ob b;
  (**) lemma_modifies_1_trans b h3 h h4;
  (**) lemma_modifies_2_1' b st h2 h3 h4;
  (**) lemma_modifies_0_2 st b h1 h2 h4;
  uint32s_to_le_bytes output ob 16ul;
  (**) let h5  = ST.get() in
  (**) lemma_modifies_2_1'' st output h1 h4 h5;
  (**) Hacl.Impl.Xor.Lemmas.lemma_xor_uint32s_to_bytes (reveal_sbytes (as_seq h0 plain))
                                                       (reveal_h32s (as_seq h k));
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_3_2 st output h0 h1 h5 hfin;
  l



#reset-options "--max_fuel 0 --z3rlimit 100"

private
val lemma_aux_modifies_2: #a:Type -> #a':Type -> h:mem -> b:buffer a{live h b} -> b':buffer a'{live h b'} -> Lemma
  (requires (True))
  (ensures (modifies_2 b b' h h))
let lemma_aux_modifies_2 #a #a' h b b' =
  lemma_intro_modifies_2 b b' h h

private
val lemma_salsa20_counter_mode_def_0:
  s:Seq.seq Hacl.UInt8.t{Seq.length s = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr < pow2 64} -> Lemma
    (Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr)
                                  (reveal_sbytes s)
     == Seq.createEmpty)
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_def_0 s k n ctr =
  Seq.lemma_eq_intro s Seq.createEmpty


#reset-options "--max_fuel 0 --z3rlimit 200"

private
val salsa20_counter_mode_blocks:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:UInt32.t{64 * UInt32.v len = length output /\ length output = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1 /\ invariant log h1 st
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 200"
let rec salsa20_counter_mode_blocks output plain len log st ctr =
  let h0 = ST.get() in
  let inv (h1: mem) (i: nat): Type0 =
    live h1 output /\ invariant log h1 st /\ modifies_2 output st h0 h1 /\ 0 <= i /\ i <= UInt32.v len
    /\ (match Ghost.reveal log with | MkLog k n ->
      reveal_sbytes (Seq.slice (as_seq h1 output) 0 (64 * i))
      == Spec.CTR.counter_mode_blocks salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (Seq.slice (as_seq h0 plain) 0 (64 * i))))
  in
  let f' (i:UInt32.t{ FStar.UInt32.( 0 <= v i /\ v i < v len ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> FStar.UInt32.(inv h_2 (v i + 1))))
  = let h = ST.get() in
    let open FStar.UInt32 in
    let o'' = Buffer.sub output 0ul (64ul *^ i +^ 64ul) in
    let b'' = Buffer.sub plain  0ul (64ul *^ i +^ 64ul) in
    let b  = Buffer.sub plain (64ul *^ i) 64ul in
    let b' = Buffer.sub plain 0ul (64ul *^ i)  in
    let o  = Buffer.sub output (64ul *^ i) 64ul in
    let o' = Buffer.sub output 0ul (64ul *^ i)  in
    let log' = update o b log st FStar.UInt64.(ctr+^ Int.Cast.uint32_to_uint64 i) in
    let h' = ST.get() in
    (**) modifies_subbuffer_2 h h' o st output;
    (**) lemma_modifies_2_trans output st h0 h h';
    no_upd_lemma_2 h h' o st b;
    no_upd_lemma_2 h h' o st b';
    no_upd_lemma_2 h h' o st o';
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (as_seq h' (Buffer.sub output 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (as_seq h0 (Buffer.sub plain 0ul (64ul *^ i +^ 64ul)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h' output) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) 0 (64 * v i));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64))
                       (Seq.slice (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64)) (64 * v i) (64 * v i + 64));
    Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h0 plain) 0 (64 * v i)) (Seq.slice (as_seq h0 plain) (64 * v i) (64 * v i + 64)));
    Seq.lemma_eq_intro (Seq.slice (as_seq h' output) 0 (64 * v i + 64))
                       (Seq.append (Seq.slice (as_seq h' output) 0 (64 * v i)) (Seq.slice (as_seq h' output) (64 * v i) (64 * v i + 64)));
    lemma_salsa20_counter_mode_2 h o'' h0 b'' (64ul *^ i +^ 64ul) (MkLog?.k (Ghost.reveal log)) (MkLog?.n (Ghost.reveal log)) ctr
  in
  let o0 = Buffer.sub output 0ul 0ul in
  let i0 = Buffer.sub plain  0ul 0ul in
  Seq.lemma_eq_intro (as_seq h0 o0) (Seq.slice (as_seq h0 output) 0 0);
  Seq.lemma_eq_intro (as_seq h0 i0) (Seq.slice (as_seq h0 plain) 0 0);
  lemma_aux_modifies_2 h0 output st;
  lemma_salsa20_counter_mode_def_0 (Seq.slice (as_seq h0 plain) 0 0) (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 0) Seq.createEmpty;
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 output) 0 0) Seq.createEmpty;
  C.Loops.for 0ul len inv f';
  let h = ST.get() in
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 (64 * UInt32.v len)) (as_seq h output);
  Seq.lemma_eq_intro (Seq.slice (as_seq h0 plain) 0 (64 * UInt32.v len)) (as_seq h plain)


private
val salsa20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) plain)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let salsa20_counter_mode output plain len log st ctr =
  assert_norm(pow2 6 = 64);
  let open FStar.UInt32 in
  let blocks_len = (len >>^ 6ul) in
  let part_len   = len &^ 0x3ful in
  UInt.logand_mask (UInt32.v len) 6;
  Math.Lemmas.lemma_div_mod (UInt32.v len) 64;
  (**) let h0 = ST.get() in
  let output' = Buffer.sub output 0ul (64ul *^ blocks_len) in
  let plain'  = Buffer.sub plain  0ul (64ul *^ blocks_len) in
  let output'' = Buffer.sub output (64ul *^ blocks_len) part_len in
  let plain''  = Buffer.sub plain  (64ul *^ blocks_len) part_len in
  salsa20_counter_mode_blocks output' plain' blocks_len log st ctr;
  (**) let h1 = ST.get() in
  (**) modifies_subbuffer_2 h0 h1 output' st output;
  if FStar.UInt32.(part_len >^ 0ul) then (
    let _ = update_last output'' plain'' part_len log st FStar.UInt64.(ctr +^ Int.Cast.uint32_to_uint64 blocks_len) in
    (**) let h' = ST.get() in
    (**) modifies_subbuffer_2 h1 h' output'' st output)
  else
    (**) lemma_modifies_sub_2 h1 h1 output st;
  let h = ST.get() in
  (**) lemma_modifies_2_trans output st h0 h1 h;
  Seq.lemma_eq_intro (Seq.append (as_seq h output') Seq.createEmpty) (as_seq h output');
  Seq.lemma_eq_intro (as_seq h output) (Seq.append (as_seq h output') (as_seq h output''));
  Seq.lemma_eq_intro (as_seq h0 plain) (Seq.append (as_seq h0 plain') (as_seq h0 plain''));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher (Ghost.reveal log).k (Ghost.reveal log).n (UInt64.v ctr) (reveal_sbytes (as_seq h0 plain)));
  ()


val salsa20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 8} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = UInt64.v ctr in
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n ctr plain)))
let salsa20 output plain len k n ctr =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let st = alloc () in
  (**) let h1 = ST.get() in
  let l  = init st k n in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_0_1' st h0 h1 h2;
  (**) no_upd_lemma_0 h0 h2 plain;
  (**) no_upd_lemma_0 h0 h2 output;
  let l' = salsa20_counter_mode output plain len l st ctr in
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_2 output st h0 h2 h3;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 output hinit h0 h3 hfin
