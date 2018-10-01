module Hacl.Impl.Poly1305_64

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST


open FStar.Mul
open FStar.HyperStack.ST
open FStar.Seq
open FStar.HyperStack
open FStar.Ghost
open FStar.Endianness
open FStar.Buffer

open Hacl.Spec.Endianness
open Hacl.Endianness

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spe.Poly1305_64
open Hacl.Bignum.AddAndMultiply

include Hacl.Impl.Poly1305_64.State

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


let log_t = erased (Hacl.Spec.Poly1305_64.text)

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0  = b:felem

let wordB : Type0  = b:uint8_p{length b <= 16}
let wordB_16 : Type0 = b:uint8_p{length b = 16}

let mask_44 = Hacl.Bignum.Parameters.mask_44

#reset-options "--max_fuel 0 --z3rlimit 5"

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo)  *)
private val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
private let sel_int h b = eval h b


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#reset-options "--z3rlimit 200 --max_fuel 0"

[@"substitute"]
val upd_3: b:felem -> b0:limb -> b1:limb -> b2:limb ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == Hacl.Spec.Poly1305_64.create_3 b0 b1 b2))
[@"substitute"]
let upd_3 b b0 b1 b2 =
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  let h = ST.get() in
  cut (get h b 0 == b0);
  cut (get h b 1 == b1);
  cut (get h b 2 == b2);
  Seq.lemma_eq_intro (as_seq h b) (Hacl.Spec.Poly1305_64.create_3 b0 b1 b2)


inline_for_extraction private
let clamp_mask : cm:wide{Wide.v cm = 0x0ffffffc0ffffffc0ffffffc0fffffff} =
  Hacl.Spec.Poly1305_64.hload128 (0x0ffffffc0ffffffcuL) (0x0ffffffc0fffffffuL)


[@"substitute"]
val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      /\ as_seq h1 r == Hacl.Spec.Poly1305_64.poly1305_encode_r_spec (as_seq h0 key)
    ))
[@"substitute"]
let poly1305_encode_r r key =
  let h0 = ST.get() in
  let k = hload128_le key in
  let k_clamped = Wide.(k &^ clamp_mask) in
  let r0 = Limb.(sint128_to_sint64 k_clamped &^ Hacl.Spec.Poly1305_64.mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 44ul)) &^ Hacl.Spec.Poly1305_64.mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 88ul))) in
  Hacl.Spec.Poly1305_64.lemma_encode_r k_clamped;
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 40 = 0x10000000000);
  upd_3 r r0 r1 r2


[@"substitute"]
val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
      /\ red_44 (as_seq h1 b)
      /\ v (Seq.index (as_seq h1 b) 2) < pow2 40
      /\ as_seq h1 b == Hacl.Spec.Poly1305_64.toField_spec (as_seq h0 m)
    ))
[@"substitute"]
let toField b block =
  let h0 = ST.get() in
  let m  = hload128_le block in
  let r0 = Limb.(sint128_to_sint64 m &^ Hacl.Spec.Poly1305_64.mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(m >>^ 44ul)) &^ Hacl.Spec.Poly1305_64.mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(m >>^ 88ul))) in
  upd_3 b r0 r1 r2;
  let h1 = ST.get() in
  (**) Seq.lemma_eq_intro (as_seq h1 b) (Hacl.Spec.Poly1305_64.toField_spec (as_seq h0 block));
  ()


[@"substitute"]
val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b /\ live h0 m
      /\ red_44 (as_seq h1 b)
      /\ as_seq h1 b == Hacl.Spec.Poly1305_64.toField_plus_2_128_spec (as_seq h0 m)
    ))
[@"substitute"]
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


[@"substitute"]
val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      /\ red_45 (as_seq h1 a)
      /\ as_seq h1 a == Hacl.Spec.Poly1305_64.poly1305_start_spec ()
      ))
[@"substitute"]
let poly1305_start a =
  (* Zeroing the accumulator *)
  upd_3 a limb_zero limb_zero limb_zero;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h a) (Hacl.Spec.Poly1305_64.poly1305_start_spec ())


module Spec = Hacl.Spec.Poly1305_64

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"substitute"]
val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1 /\ live h0 key
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal log) == poly1305_init_spec (as_seq h0 key)
      ))
[@"substitute"]
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h;
  let log = hide (Seq.createEmpty #Spec.Poly1305.word) in
  log


#reset-options "--z3rlimit 100 --max_fuel 0"

noextract
private val hide_log:
  h0:HyperStack.mem ->
  m:uint8_p{length m <= 16} ->
  log:log_t{live h0 m} ->
  Tot (log':log_t{Ghost.reveal log' == FStar.Seq.(create 1 (as_seq h0 m) @| Ghost.reveal log)})

#reset-options "--z3rlimit 100 --max_fuel 0"

let hide_log h0 m log =
  let (m':erased Spec.Poly1305.word) = elift1 #(b:wordB{live h0 b}) #Spec.word'
                    (fun m -> reveal_sbytes (as_seq h0 m)) (hide m) in
  elift2 (fun (l:Spec.Poly1305.text) (m:Spec.Poly1305.word) -> FStar.Seq.((Seq.create 1 (m)) @| l)) log m'

#reset-options "--z3rlimit 100 --max_fuel 0"

[@"c_inline"]
val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st
      /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log)
        == poly1305_update_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m)
      ))
#reset-options "--z3rlimit 200 --max_fuel 0"
[@"c_inline"]
let poly1305_update log st m =
  let acc = st.h in
  let r   = st.r in
  (**) let h0 = ST.get() in
  push_frame();
  (**) let h1 = ST.get() in
  let tmp = create limb_zero clen in
  (**) let h2 = ST.get() in
  (**) no_upd_lemma_0 h1 h2 r;
  (**) no_upd_lemma_0 h1 h2 acc;
  toField_plus_2_128 tmp m;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_0_1' tmp h1 h2 h3;
  (**) no_upd_lemma_1 h2 h3 tmp r;
  (**) no_upd_lemma_1 h2 h3 tmp acc;
  add_and_multiply acc tmp r;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 acc r;
  (**) lemma_modifies_0_1 acc h1 h3 h4;
  pop_frame();
  let h5 = ST.get() in
  (**) modifies_popped_1 st.h h0 h1 h4 h5;
  hide_log h0 m log

  (* let (m':erased Spec.Poly1305.word) = elift2_p #wordB_16 #HyperStack.mem #(fun m h -> live h m) #Spec.word' *)
  (*                   (fun m h -> reveal_sbytes (as_seq h m)) (hide m) (hide h0) in *)
  (* elift2 (fun (l:Spec.Poly1305.text) (m:Spec.Poly1305.word) -> FStar.Seq.((Seq.create 1 (m)) @| l)) log m' *)


#reset-options "--max_fuel 0 --z3rlimit 100"

[@"substitute"]
val poly1305_concat:
  b:uint8_p{length b = 16} ->
  m:uint8_p{disjoint b m} ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live h m /\ live h b
      /\ as_seq h b == Seq.create 16 (uint8_to_sint8 0uy)))
    (ensures (fun h0 _ h1 -> live h0 m /\ live h0 b /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == Seq.append (as_seq h0 m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy))
    ))
[@"substitute"]
let poly1305_concat b m len =
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

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"c_inline"]
val poly1305_process_last_block_:
  current_log:log_t ->
  block:uint8_p{length block = 16} ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)
      /\ live h block /\ as_seq h block == Seq.upd (Seq.append (as_seq h m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy))) (U64.v len) (uint8_to_sint8 1uy)
      /\ disjoint block st.h /\ disjoint block st.r
    ))
    (ensures (fun h0 updated_log h1 -> live_st h0 st /\ live h0 m /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ live h0 block
      /\ modifies_1 st.h h0 h1
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log) == Hacl.Spec.Poly1305_64.poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m) (len)
    ))

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"c_inline"]
let poly1305_process_last_block_ log block st m rem' =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h = ST.get() in
  let tmp = create limb_zero clen in
  (**) let h' = ST.get() in
  assert_norm(pow2 32 = 0x100000000);
  Math.Lemmas.modulo_lemma (U64.v rem') (pow2 32);
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  let h0 = ST.get() in
  toField tmp block;
  let h1 = ST.get() in
  (**) lemma_modifies_0_1' tmp h h' h1;
  add_and_multiply st.h tmp st.r;
  let h2 = ST.get() in
  (**) lemma_modifies_0_1 st.h h h1 h2;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 st.h hinit h h2 hfin;
  hide_log h0 m log
  

#reset-options "--max_fuel 0 --z3rlimit 100"

[@"c_inline"]
val poly1305_process_last_block:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures (fun h0 updated_log h1 -> live_st h0 st /\ live h0 m
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ modifies_1 st.h h0 h1
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log) == Hacl.Spec.Poly1305_64.poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m) (len)
    ))
[@"c_inline"]
let poly1305_process_last_block log st m rem' =
  (**) let hinit = ST.get() in
  push_frame();
  (**) let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let block = create zero 16ul in
  (**) let h1 = ST.get() in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  poly1305_concat block m rem';
  (**) let h2 = ST.get() in
  block.(i) <- uint8_to_sint8 1uy;
  (**) let h3 = ST.get() in
  (**) lemma_modifies_1_trans block h1 h2 h3;
  (**) lemma_modifies_0_1' block h0 h1 h3;
  let log' = poly1305_process_last_block_ log block st m rem' in
  (**) let h4 = ST.get() in
  (**) lemma_modifies_0_1 st.h h0 h3 h4;
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 st.h hinit h0 h4 hfin;
  log'


[@"substitute"]
val poly1305_last_pass_:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) p44 p44 p42))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) p44 p44 p42
      /\ live h1 acc /\ bounds (as_seq h1 acc) p44 p44 p42
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == Hacl.Spec.Poly1305_64.poly1305_last_pass_spec_ (as_seq h0 acc)))
[@"substitute"]
let poly1305_last_pass_ acc =
  let a0 = acc.(0ul) in
  let a1 = acc.(1ul) in
  let a2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let mask0 = gte_mask a0 Hacl.Spec.Poly1305_64.p44m5 in
  let mask1 = eq_mask a1 Hacl.Spec.Poly1305_64.p44m1 in
  let mask2 = eq_mask a2 Hacl.Spec.Poly1305_64.p42m1 in
  let mask  = mask0 &^ mask1 &^ mask2 in
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_1 (v mask2);
  UInt.logand_lemma_2 (v mask0); UInt.logand_lemma_2 (v mask1); UInt.logand_lemma_2 (v mask2);
  UInt.logand_associative (v mask0) (v mask1) (v mask2);
  cut (v mask = UInt.ones 64 ==> (v a0 >= pow2 44 - 5 /\ v a1 = pow2 44 - 1 /\ v a2 = pow2 42 - 1));
  UInt.logand_lemma_1 (v Hacl.Spec.Poly1305_64.p44m5); UInt.logand_lemma_1 (v Hacl.Spec.Poly1305_64.p44m1); UInt.logand_lemma_1 (v Hacl.Spec.Poly1305_64.p42m1);
  UInt.logand_lemma_2 (v Hacl.Spec.Poly1305_64.p44m5); UInt.logand_lemma_2 (v Hacl.Spec.Poly1305_64.p44m1); UInt.logand_lemma_2 (v Hacl.Spec.Poly1305_64.p42m1);
  let a0' = a0 -^ (Hacl.Spec.Poly1305_64.p44m5 &^ mask) in
  let a1' = a1 -^ (Hacl.Spec.Poly1305_64.p44m1 &^ mask) in
  let a2' = a2 -^ (Hacl.Spec.Poly1305_64.p42m1 &^ mask) in
  upd_3 acc a0' a1' a2'


[@"substitute"]
val carry_limb_unrolled:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) (p44+5*((p45+p20)/p42)) p44 p42))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) (p44+5*((p45+p20)/p42)) p44 p42
      /\ live h1 acc /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == Hacl.Spec.Poly1305_64.carry_limb_unrolled (as_seq h0 acc)))
[@"substitute"]
let carry_limb_unrolled acc =
  let a0 = acc.(0ul) in
  let a1 = acc.(1ul) in
  let a2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let a0' = a0 &^ Hacl.Spec.Poly1305_64.mask_44 in
  UInt.logand_mask (v a0) 44;
  cut (v a0 < p45);
  let r0  = a0 >>^ 44ul in
  Math.Lemmas.lemma_div_lt (v a0) 45 44;
  assert_norm(pow2 1 = 2); assert_norm(pow2 0 = 1);
  cut (v r0 <= 1);
  let a1' = (a1 +^ r0) &^ Hacl.Spec.Poly1305_64.mask_44 in
  UInt.logand_mask #64 (v a1 + v r0) 44;
  Math.Lemmas.lemma_div_lt (v a1 + v r0) 45 44;
  let r1  = (a1 +^ r0) >>^ 44ul in
  let a2' = a2 +^ r1 in
  upd_3 acc a0' a1' a2'


#reset-options "--z3rlimit 100 --max_fuel 0"

[@"substitute"]
val carry_last_unrolled:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) p44 p44 (p42+1)
      /\ (v (Seq.index (as_seq h acc) 2) = p42 ==> v (Seq.index (as_seq h acc) 1) = 0)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) p44 p44 (p42+1)
      /\ (v (Seq.index (as_seq h0 acc) 2) = p42 ==> v (Seq.index (as_seq h0 acc) 1) = 0)
      /\ live h1 acc /\ bounds (as_seq h1 acc) p44 p44 p42
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == Hacl.Spec.Poly1305_64.carry_last_unrolled (as_seq h0 acc)))
[@"substitute"]
let carry_last_unrolled acc =
  let h = ST.get() in
  lemma_carried_is_fine_to_carry_top (as_seq h acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec (as_seq h acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ (as_seq h acc);
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc


#reset-options "--z3rlimit 100 --max_fuel 0"

[@"substitute"]
val poly1305_last_pass:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ red_45 (as_seq h acc)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ live h1 acc /\ red_45 (as_seq h0 acc)
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == Hacl.Spec.Poly1305_64.poly1305_last_pass_spec (as_seq h0 acc)))
let poly1305_last_pass acc =
  let h = ST.get() in
  last_pass_is_fine (as_seq h acc);
  lemma_carried_is_fine_to_carry (as_seq h acc);
  Hacl.Bignum.Fproduct.carry_limb_ acc;
  let h1 = ST.get() in
  lemma_carried_is_fine_to_carry_top (as_seq h1 acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec (as_seq h1 acc);
  Hacl.Bignum.Modulo.carry_top acc;
  carry_limb_unrolled acc;
  carry_last_unrolled acc;
  poly1305_last_pass_ acc


[@"substitute"]
val bignum_to_128:
  a:felem ->
  Stack wide
    (requires (fun h -> live h a /\ bounds (as_seq h a) p44 p44 p42))
    (ensures (fun h0 z h1 -> live h0 a /\ bounds (as_seq h0 a) p44 p44 p42
      /\ h0 == h1 /\ z == Hacl.Spec.Poly1305_64.bignum_to_128 (as_seq h0 a)))
[@"substitute"]
let bignum_to_128 acc =
  let h0 = acc.(0ul) in
  let h1 = acc.(1ul) in
  let h2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let accl = (h1 <<^ 44ul) |^ h0 in
  let acch = (h2 <<^ 24ul) |^ (h1 >>^ 20ul)in
  let open Hacl.Bignum.Wide in
  let acc' = (limb_to_wide acch <<^ 64ul) |^ limb_to_wide accl in
  acc'


[@"substitute"]
val poly1305_finish__:
  log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h0 st /\ live h1 st.h
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h) /\ red_45 (as_seq h1 st.h) /\ live h0 m
      /\ (let r1   = as_seq h1 st.r in
         let r0   = as_seq h0 st.r in
         let acc1 = as_seq h1 st.h in
         let acc0 = as_seq h0 st.h in
         let log  = reveal log in
         let log' = reveal updated_log in
         let m    = as_seq h0 m in
         Spec.MkState r1 acc1 log' == (
           if U64.(len =^ 0uL) then Spec.MkState r0 acc0 log
           else Hacl.Spec.Poly1305_64.poly1305_process_last_block_spec (Spec.MkState r0 acc0 log) m len))
      ))
[@"substitute"]
let poly1305_finish__ log st m len =
  let h0 = ST.get() in
  if U64.(len =^ 0uL) then (log)
  else (
    let last_block = m in
    poly1305_process_last_block log st m len
    )


#reset-options "--max_fuel 0 --z3rlimit 1000"

[@"substitute"]
val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac /\ disjoint st.h key_s /\ disjoint st.h m
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ (let r0   = as_seq h0 st.r in
         let acc0 = as_seq h0 st.h in
         let log  = reveal log in
         let m    = as_seq h0 m in
         let mac  = as_seq h1 mac in
         let k    = as_seq h0 key_s in
         mac == poly1305_finish_spec (Spec.MkState r0 acc0 log) m len k)
    ))

// Wintersteiger: admitting this query to unblock CI. It's likely solvable, but Z3 takes ages. 
#reset-options "--max_fuel 0 --z3rlimit 1000"

[@"substitute"]
let poly1305_finish_ log st mac m len key_s =
  let acc = st.h in
  let h0 = ST.get() in
  let log' = poly1305_finish__ log st m len in
  poly1305_last_pass acc;
  cut (disjoint acc mac);
  let h2 = ST.get() in
  no_upd_lemma_1 h0 h2 acc key_s;
  assert (equal h0 key_s h2 key_s);
  let k'  = hload128_le key_s in
  assert (FStar.UInt128.v k' == FStar.Endianness.little_endian (as_seq h0 key_s));
  FStar.UInt128.v_inj k' (FStar.UInt128.uint_to_t (FStar.Endianness.little_endian (as_seq h0 key_s))); //NS: 07/14 ... need to invoke injectivity explicitly; which is rather heavy
  assert (k' == Hacl.Spec.Poly1305_64.load128_le_spec (as_seq h0 key_s));
  let open Hacl.Bignum.Wide in
  let acc' = bignum_to_128 acc in
  let mac' = acc' +%^ k' in
  hstore128_le mac mac';
  let h1 = ST.get() in
  lemma_little_endian_inj (Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 mac)) (Hacl.Spec.Endianness.reveal_sbytes (poly1305_finish_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal log)) (as_seq h0 m) len (as_seq h0 key_s)))


#reset-options "--max_fuel 0 --z3rlimit 1000"

[@"substitute"]
val poly1305_update_last:
  log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 _ h1 -> modifies_1 st.h h0 h1 /\ live_st h0 st /\ live h0 m /\ live h1 st.h
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ (let r0   = as_seq h0 st.r in
         let acc0 = as_seq h0 st.h in
         let log  = reveal log in
         let r1   = as_seq h1 st.r in
         let acc1 = as_seq h1 st.h in
         let m    = as_seq h0 m in
         bounds acc1 p44 p44 p42 /\ 
         acc1 == Hacl.Spec.Poly1305_64.poly1305_update_last_spec (Spec.MkState r0 acc0 log) m len)
    ))
[@"substitute"]
let poly1305_update_last log st m len =
  let log' = poly1305_finish__ log st m len in
  let acc  = st.h in
  poly1305_last_pass acc


[@"substitute"]
val poly1305_finish:
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h mac /\ live h k
      /\ bounds (as_seq h (st.h)) p44 p44 p42))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1 /\ live_st h0 st /\ live h0 mac /\ live h0 k /\ live h1 mac
      /\ bounds (as_seq h0 (st.h)) p44 p44 p42
      /\ as_seq h1 mac == Hacl.Spec.Poly1305_64.poly1305_finish_spec' (as_seq h0 (st.h)) (as_seq h0 k)
    ))
[@"substitute"]
let poly1305_finish st mac key_s =
  let h0 = ST.get() in
  let acc = st.h in
  let k'  = hload128_le key_s in
  let open Hacl.Bignum.Wide in
  let acc' = bignum_to_128 acc in
  let mac' = acc' +%^ k' in
  hstore128_le mac mac';
  let h1 = ST.get() in
  lemma_little_endian_inj (Hacl.Spec.Endianness.reveal_sbytes (as_seq h1 mac)) (Hacl.Spec.Endianness.reveal_sbytes (Hacl.Spec.Poly1305_64.poly1305_finish_spec' (as_seq h0 acc) (as_seq h0 key_s)))


let mk_state r h = MkState r h

val alloc:
  unit -> StackInline poly1305_state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> modifies_0 h0 h1 /\ live_st h1 st /\ frameOf st.h == get_tip h0
      /\ frameOf st.r = get_tip h0 /\ (st.r `unused_in` h0) /\ (st.h `unused_in` h0)))
let alloc () =
  let buf = create limb_zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  mk_state r h
