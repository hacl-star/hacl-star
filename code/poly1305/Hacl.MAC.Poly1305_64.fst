module Hacl.MAC.Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Buffer
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spec.MAC.Poly1305_64
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

inline_for_extraction let log_t = unit

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0 = b:felem

let wordB = b:uint8_p{Buffer.length b <= 16}
let wordB_16 = b:uint8_p{Buffer.length b = 16}

noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val load64_le:
  b:uint8_p{Buffer.length b = 8} ->
  Stack limb
    (requires (fun h -> live h b))
    (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 b
      /\ r == load64_le_spec (as_seq h1 b)
      ))
let load64_le b =
  assert_norm (pow2 32 = 0x100000000);
  let h = ST.get() in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  cut (b0 == get h b 0);
  cut (b1 == get h b 1);
  cut (b2 == get h b 2);
  cut (b3 == get h b 3);
  cut (b4 == get h b 4);
  cut (b5 == get h b 5);
  cut (b6 == get h b 6);
  cut (b7 == get h b 7);
  Limb.(
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val store64_le:
  b:uint8_p{Buffer.length b = 8} ->
  z:Limb.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      /\ as_seq h1 b == store64_le_spec z
      ))
let store64_le b z =
  assert_norm (pow2 32 = 0x100000000);
  let open Hacl.UInt64 in
  let b0 = sint64_to_sint8 z in
  let b1 = sint64_to_sint8 (z >>^ 8ul) in
  let b2 = sint64_to_sint8 (z >>^ 16ul) in
  let b3 = sint64_to_sint8 (z >>^ 24ul) in
  let b4 = sint64_to_sint8 (z >>^ 32ul) in
  let b5 = sint64_to_sint8 (z >>^ 40ul) in
  let b6 = sint64_to_sint8 (z >>^ 48ul) in
  let b7 = sint64_to_sint8 (z >>^ 56ul) in
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  b.(3ul) <- b3;
  b.(4ul) <- b4;
  b.(5ul) <- b5;
  b.(6ul) <- b6;
  b.(7ul) <- b7;
  let h1 = ST.get() in
  cut (b0 == get h1 b 0);
  cut (b1 == get h1 b 1);
  cut (b2 == get h1 b 2);
  cut (b3 == get h1 b 3);
  cut (b4 == get h1 b 4);
  cut (b5 == get h1 b 5);
  cut (b6 == get h1 b 6);
  cut (b7 == get h1 b 7);
  Seq.lemma_eq_intro (as_seq h1 b) (store64_le_spec z)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = eval h b


let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

inline_for_extraction val upd_3: b:felem -> b0:limb -> b1:limb -> b2:limb ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == create_3 b0 b1 b2))
inline_for_extraction let upd_3 b b0 b1 b2 =
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  let h = ST.get() in
  cut (get h b 0 == b0);
  cut (get h b 1 == b1);
  cut (get h b 2 == b2);
  Seq.lemma_eq_intro (as_seq h b) (create_3 b0 b1 b2)


val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{Buffer.length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      /\ as_seq h1 r == poly1305_encode_r_spec (as_seq h0 key)
    ))
let poly1305_encode_r r key =
  let h0 = ST.get() in
  let t0 = load64_le(sub key 0ul 8ul) in
  let t1 = load64_le(sub key 8ul 8ul) in
  let open Hacl.Bignum.Limb in
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 42 = 0x40000000000);
  assert_norm(pow2 32 = 0x100000000);
  let r0 = ( t0                           ) &^ uint64_to_limb 0xffc0fffffffuL in
  let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_limb 0xfffffc0ffffuL in
  let r2 = ((t1 >>^ 24ul)                 ) &^ uint64_to_limb 0x00ffffffc0fuL in
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f;
  upd_3 r r0 r1 r2



inline_for_extraction let mask_42 : p:Hacl.Bignum.Limb.t{v p = pow2 42 - 1} = assert_norm(pow2 42 - 1 = 0x3ffffffffff); assert_norm(pow2 64 = 0x10000000000000000); uint64_to_limb 0x3ffffffffffuL
  
inline_for_extraction let mask_44 : p:Hacl.Bignum.Limb.t{v p = pow2 44 - 1} = assert_norm(pow2 44 - 1 = 0xfffffffffff);
  assert_norm (pow2 64 = 0x10000000000000000); uint64_to_limb 0xfffffffffffuL


val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
      /\ red_44 (as_seq h1 b)
      /\ v (Seq.index (as_seq h1 b) 2) < pow2 40
      /\ as_seq h1 b == toField_spec (as_seq h0 m)
    ))
let toField b m =
  (* Load block values *)
  let h0 = ST.get() in
  let t0 = load64_le (Buffer.sub m 0ul 8ul) in
  let t1 = load64_le (Buffer.sub m 8ul 8ul) in
  let open Hacl.UInt64 in  
  UInt.logand_mask (v t0) 44;
  UInt.logand_mask (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44;
  Math.Lemmas.lemma_div_lt (v t1) 64 24;
  Math.Lemmas.pow2_lt_compat 44 40;
  let t_0 = t0 &^ mask_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_44 in
  let t_2 = (t1 >>^ 24ul) in
  upd_3 b t_0 t_1 t_2


val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
      /\ red_44 (as_seq h1 b)
      /\ as_seq h1 b == toField_plus_2_128_spec (as_seq h0 m)
    ))
let toField_plus_2_128 b m =
  let h0 = ST.get() in
  toField b m;
  let b2 = b.(2ul) in
  let open Hacl.Bignum.Limb in
  assert_norm (pow2 40 = 0x10000000000);
  UInt.logor_disjoint (0x10000000000) (v b2) 40;
  assert_norm (pow2 40 + pow2 40 < pow2 44);
  let b2' = uint64_to_limb 0x10000000000uL |^ b2 in
  b.(2ul) <- b2'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      /\ red_45 (as_seq h1 a)
      /\ sel_int h1 a = 0
      /\ as_seq h1 a == poly1305_start_spec ()
      ))
let poly1305_start a =
  (* Zeroing the accumulator *)
  upd_3 a limb_zero limb_zero limb_zero;
  let h = ST.get() in
  lemma_seval_def (as_seq h a) 3;
  lemma_seval_def (as_seq h a) 2;
  lemma_seval_def (as_seq h a) 1;
  lemma_seval_def (as_seq h a) 0;
  cut (get h a 0 == limb_zero);
  cut (get h a 1 == limb_zero);
  cut (get h a 2 == limb_zero);
  Seq.lemma_eq_intro (as_seq h a) (poly1305_start_spec ())



(* ******************* *)
(* Fast implementation *)
(* ******************* *)

module Spec = Hacl.Spec.MAC.Poly1305_64

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{Buffer.length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ red_45 (as_seq h st.h) /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1 /\ live h0 key
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == poly1305_init_spec (as_seq h0 key)
      (* /\ acc_inv h1 log st *)
      ))
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{Buffer.length m >= 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st
      /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == poly1305_update_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ()) (as_seq h0 m)
      (* /\ acc_inv h1 updated_log st *)
      (* /\ (reveal updated_log) == *)
      (*     Seq.snoc (reveal current_log) (encode (sel_word h1 (Buffer.sub m 0ul 16ul))) *)
      (* /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r) *)
      ))
let poly1305_update log st m =
  push_frame();
  let tmp = Buffer.create limb_zero clen in
  let acc = st.h in
  let r   = st.r in
  toField_plus_2_128 tmp (sub m 0ul 16ul);
  add_and_multiply acc tmp r;
  pop_frame()


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= Buffer.length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == poly1305_blocks_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ()) (as_seq h0 m) len
      ))
let rec poly1305_blocks log st m len =
  let m0 = ST.get() in
  if U64.(len <^ 16uL) then (
    ()
  )
  else (
    let new_log = poly1305_update log st m in
    let len = U64.(len -^ 16uL) in
    let m   = offset m 16ul in
    poly1305_blocks new_log st m len
  )


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


inline_for_extraction val poly1305_concat:
  b:uint8_p{Buffer.length b = 16} ->
  m:uint8_p{disjoint b m} ->
  len:U64.t{U64.v len < 16 /\ U64.v len = Buffer.length m} ->
  Stack unit
    (requires (fun h -> live h m /\ live h b
      /\ as_seq h b == Seq.create 16 (uint8_to_sint8 0uy)))
    (ensures (fun h0 _ h1 -> live h0 m /\ live h0 b /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == Seq.append (as_seq h0 m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy))
    ))
inline_for_extraction let poly1305_concat b m len =
  assert_norm(pow2 32 = 0x100000000);
  let h0 = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h0 m);
  let i = FStar.Int.Cast.uint64_to_uint32 len in
  Math.Lemmas.modulo_lemma (U64.v len) (pow2 32);
  cut (Seq.slice (as_seq h0 m) 0 (U32.v i) == as_seq h0 m);
  blit m 0ul b 0ul i;
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy)) (Seq.slice (as_seq h0 b) (U64.v len) 16);
  Seq.lemma_eq_intro (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy)) (Seq.slice (as_seq h1 b) (U64.v len) 16);
  Seq.lemma_eq_intro (as_seq h0 m) (Seq.slice (as_seq h1 b) 0 (U64.v len));
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h1 b);
  Seq.lemma_eq_intro (as_seq h1 b) (Seq.append (as_seq h0 m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy)))


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_process_last_block_:
  block:uint8_p{Buffer.length block = 16} ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = Buffer.length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)
      /\ live h block /\ as_seq h block == Seq.upd (Seq.append (as_seq h m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy))) (U64.v len) (uint8_to_sint8 1uy)
      /\ disjoint block st.h /\ disjoint block st.r /\ disjoint block m
      ))
    (ensures (fun h0 _ h1 -> live_st h0 st /\ live h0 m /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ live h0 block
      /\ modifies_1 st.h h0 h1
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ()) (as_seq h0 m) (len)
      ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_process_last_block_ block st m rem' =
  push_frame();
  let tmp = Buffer.create limb_zero clen in
  assert_norm(pow2 32 = 0x100000000);
  Math.Lemmas.modulo_lemma (U64.v rem') (pow2 32);
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  let h0 = ST.get() in
  toField tmp block;
  let h1 = ST.get() in
  add_and_multiply st.h tmp st.r;
  let h2 = ST.get() in
  pop_frame()


val poly1305_process_last_block:
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = Buffer.length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures (fun h0 _ h1 -> live_st h0 st /\ live h0 m /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ modifies_1 st.h h0 h1
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ()) (as_seq h0 m) (len)
      ))
let poly1305_process_last_block st m rem' =
  push_frame();
  let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let block = Buffer.create zero 16ul in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  poly1305_concat block m rem';
  block.(i) <- uint8_to_sint8 1uy;
  poly1305_process_last_block_ block st m rem';
  pop_frame()


val poly1305_last_pass: acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ red_45 (as_seq h acc)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ live h1 acc /\ red_45 (as_seq h0 acc)
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == poly1305_last_pass_spec (as_seq h0 acc)))
let poly1305_last_pass acc =
  let h = ST.get() in
  last_pass_is_fine (as_seq h acc);
  Hacl.Bignum.Fproduct.carry_limb_ acc 0ul;
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val store128_le:
  mac:uint8_p{Buffer.length mac = 16} ->
  mac':wide ->
  Stack unit
    (requires (fun h -> live h mac))
    (ensures (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1
      /\ as_seq h1 mac ==   Seq.append (store64_le_spec (wide_to_limb mac')) (store64_le_spec (wide_to_limb Hacl.Bignum.Wide.(mac' >>^ 64ul)))))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let store128_le mac mac' =
  let open Hacl.Bignum.Wide in
  let macl = wide_to_limb mac' in
  let mach = wide_to_limb (mac' >>^ 64ul) in
  store64_le (Buffer.sub mac 0ul 8ul) macl;
  store64_le (Buffer.sub mac 8ul 8ul) mach;
  let h = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h mac);
  Seq.lemma_eq_intro (as_seq h mac) (Seq.append (store64_le_spec macl) (store64_le_spec mach))

#set-options "--z3rlimit 20"

inline_for_extraction val poly1305_finish__:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{Buffer.length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Buffer.length m} ->
  key_s:uint8_p{Buffer.length key_s = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) () == (
           assert_norm (pow2 64 = 0x10000000000000000);
           assert_norm (pow2 32 = 0x100000000);
           let rem' = U64.(len &^ 0xfuL) in
           assert_norm(pow2 4 - 1 = 0xf);
           UInt.logand_mask (U64.v len) 4;
           if U64.(rem' =^ 0uL) then (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ())
           else poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ())
                                                 (Seq.slice (as_seq h0 m) (U64.v len - U64.v rem') (U64.v len)) rem')
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"
inline_for_extraction let poly1305_finish__ log st mac m len key_s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  let rem' = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 - 1 = 0xf);
  UInt.logand_mask (U64.v len) 4;
  let h0 = ST.get() in
  if U64.(rem' =^ 0uL) then ()
  else (
    Math.Lemmas.lemma_div_mod (U64.v len) (16);
    Math.Lemmas.pow2_lt_compat 64 32;
    Math.Lemmas.modulo_lemma (U64.v len - U64.v rem') (pow2 32);
    Math.Lemmas.modulo_lemma (U64.v rem') (pow2 32);
    let start = Int.Cast.uint64_to_uint32 U64.(len -^ rem') in
    let l = Int.Cast.uint64_to_uint32 rem' in
    let last_block = sub m start l in
    cut (as_seq h0 last_block == (Seq.slice (as_seq h0 m) (U64.v len - U64.v rem') (U64.v len)));
    poly1305_process_last_block st (sub m start l) rem'
    );
  ()


val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{Buffer.length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Buffer.length m} ->
  key_s:uint8_p{Buffer.length key_s = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac /\ disjoint st.h key_s /\ disjoint st.h m
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ as_seq h1 mac == poly1305_finish_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) ())
                                              (as_seq h0 m) len (as_seq h0 key_s)
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
let poly1305_finish_ log st mac m len key_s =
  let h0 = ST.get() in
  poly1305_finish__ log st mac m len key_s;  
  poly1305_last_pass st.h;
  cut (disjoint st.h mac);
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 st.h key_s;
  let kl = load64_le (sub key_s 0ul 8ul) in
  let kh = load64_le (sub key_s 8ul 8ul) in
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let open Hacl.Bignum.Limb in
  let accl = h0 |^ (h1 <<^ 44ul) in
  let acch = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in
  let open Hacl.Bignum.Wide in
  let acc' = limb_to_wide accl |^ (limb_to_wide acch <<^ 64ul) in
  let k'   = limb_to_wide kl   |^ (limb_to_wide kh   <<^ 64ul) in
  let mac' = acc' +%^ k' in  
  store128_le mac mac'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val crypto_onetimeauth:
  output:uint8_p{Buffer.length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Buffer.length input} ->
  k:uint8_p{disjoint output k /\ Buffer.length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ as_seq h1 output == crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k)))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let buf = Buffer.create zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = MkState r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st k in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()
