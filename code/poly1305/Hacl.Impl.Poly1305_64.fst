module Hacl.Impl.Poly1305_64


open FStar.Mul
open FStar.ST
open FStar.Ghost
open FStar.SeqProperties
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer

open C

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spec.Poly1305_64
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


inline_for_extraction let log_t = erased (text)

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0  = b:felem

let wordB : Type0  = b:uint8_p{length b <= 16}
let wordB_16 : Type0 = b:uint8_p{length b = 16}


noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state


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


inline_for_extraction private
let clamp_mask : cm:wide{Wide.v cm = 0x0ffffffc0ffffffc0ffffffc0fffffff} =
  load128 (0x0ffffffc0ffffffcuL) (0x0ffffffc0fffffffuL)


val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      /\ as_seq h1 r == poly1305_encode_r_spec (as_seq h0 key)
    ))
let poly1305_encode_r r key =
  let h0 = ST.get() in
  let k = load128_le key in
  let k_clamped = Wide.(k &^ clamp_mask) in
  let r0 = Limb.(sint128_to_sint64 k_clamped &^ mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 44ul)) &^ mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 88ul))) in
  lemma_encode_r k_clamped;
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 40 = 0x10000000000);
  upd_3 r r0 r1 r2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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
let toField b block =
  let h0 = ST.get() in
  let m  = load128_le block in
  let r0 = Limb.(sint128_to_sint64 m &^ mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(m >>^ 44ul)) &^ mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(m >>^ 88ul))) in
  upd_3 b r0 r1 r2;
  let h1 = ST.get() in
  cut (as_seq h1 b == toField_spec (as_seq h0 block));
  ()


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
      /\ as_seq h1 a == poly1305_start_spec ()
      ))
let poly1305_start a =
  (* Zeroing the accumulator *)
  upd_3 a limb_zero limb_zero limb_zero;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h a) (poly1305_start_spec ())



module Spec = Hacl.Spec.Poly1305_64

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ red_45 (as_seq h st.h) /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1 /\ live h0 key
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal log) == poly1305_init_spec (as_seq h0 key)
      ))
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h;
  let log = hide (Seq.createEmpty #word) in
  log


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
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
let poly1305_update log st m =
  let acc = st.h in
  let r   = st.r in
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let tmp = create limb_zero clen in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 r;
  no_upd_lemma_0 h1 h2 acc;
  toField_plus_2_128 tmp m;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 tmp r;
  no_upd_lemma_1 h2 h3 tmp acc;
  add_and_multiply acc tmp r;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 acc r;
  pop_frame();
  let h5 = ST.get() in
  let m' = elift2_p #wordB_16 #HyperStack.mem #(fun m h -> live h m) #Spec.word
                    (fun m h -> as_seq h m) (hide m) (hide h0) in
  elift2 (fun l m -> FStar.Seq.(l @| (Seq.create 1 m))) log m'


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

inline_for_extraction val poly1305_concat:
  b:uint8_p{length b = 16} ->
  m:uint8_p{disjoint b m} ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
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
  current_log:log_t ->
  block:uint8_p{length block = 16} ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)
      /\ live h block /\ as_seq h block == Seq.upd (Seq.append (as_seq h m) (Seq.create (16 - U64.v len) (uint8_to_sint8 0uy))) (U64.v len) (uint8_to_sint8 1uy)
      /\ disjoint block st.h /\ disjoint block st.r /\ disjoint block m
    ))
    (ensures (fun h0 updated_log h1 -> live_st h0 st /\ live h0 m /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ live h0 block
      /\ modifies_1 st.h h0 h1
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log) == poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m) (len)
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_process_last_block_ log block st m rem' =
  let h0 = ST.get() in
  push_frame();
  let tmp = create limb_zero clen in
  assert_norm(pow2 32 = 0x100000000);
  Math.Lemmas.modulo_lemma (U64.v rem') (pow2 32);
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  let h0 = ST.get() in
  toField tmp block;
  let h1 = ST.get() in
  add_and_multiply st.h tmp st.r;
  let h2 = ST.get() in
  pop_frame();
  let m' = elift2_p #wordB #HyperStack.mem #(fun m h -> live h m) #Spec.word
                    (fun m h -> as_seq h m) (hide m) (hide h0) in
  elift2 (fun l m -> FStar.Seq.(l @| (Seq.create 1 m))) log m'
  

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log) == poly1305_process_last_block_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m) (len)
    ))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_process_last_block log st m rem' =
  push_frame();
  let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let block = create zero 16ul in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  poly1305_concat block m rem';
  block.(i) <- uint8_to_sint8 1uy;
  let log' = poly1305_process_last_block_ log block st m rem' in
  pop_frame();
  log'


val poly1305_last_pass_:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) p44 p44 p42))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) p44 p44 p42
      /\ live h1 acc /\ bounds (as_seq h1 acc) p44 p44 p42
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == poly1305_last_pass_spec_ (as_seq h0 acc)))
let poly1305_last_pass_ acc =
  let a0 = acc.(0ul) in
  let a1 = acc.(1ul) in
  let a2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let mask0 = gte_mask a0 p44m5 in
  let mask1 = eq_mask a1 p44m1 in
  let mask2 = eq_mask a2 p42m1 in
  let mask  = mask0 &^ mask1 &^ mask2 in
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_1 (v mask2);
  UInt.logand_lemma_2 (v mask0); UInt.logand_lemma_2 (v mask1); UInt.logand_lemma_2 (v mask2);
  UInt.logand_associative (v mask0) (v mask1) (v mask2);
  cut (v mask = UInt.ones 64 ==> (v a0 >= pow2 44 - 5 /\ v a1 = pow2 44 - 1 /\ v a2 = pow2 42 - 1));
  UInt.logand_lemma_1 (v p44m5); UInt.logand_lemma_1 (v p44m1); UInt.logand_lemma_1 (v p42m1);
  UInt.logand_lemma_2 (v p44m5); UInt.logand_lemma_2 (v p44m1); UInt.logand_lemma_2 (v p42m1);
  let a0' = a0 -^ (p44m5 &^ mask) in
  let a1' = a1 -^ (p44m1 &^ mask) in
  let a2' = a2 -^ (p42m1 &^ mask) in
  upd_3 acc a0' a1' a2'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val carry_limb_unrolled:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) (p44+5*((p45+p20)/p42)) p44 p42))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) (p44+5*((p45+p20)/p42)) p44 p42
      /\ live h1 acc /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == carry_limb_unrolled (as_seq h0 acc)))
let carry_limb_unrolled acc =
  let a0 = acc.(0ul) in
  let a1 = acc.(1ul) in
  let a2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let a0' = a0 &^ mask_44 in
  UInt.logand_mask (v a0) 44;
  cut (v a0 < p45);
  let r0  = a0 >>^ 44ul in
  Math.Lemmas.lemma_div_lt (v a0) 45 44;
  assert_norm(pow2 1 = 2); assert_norm(pow2 0 = 1);
  cut (v r0 <= 1);
  let a1' = (a1 +^ r0) &^ mask_44 in
  UInt.logand_mask #64 (v a1 + v r0) 44;
  Math.Lemmas.lemma_div_lt (v a1 + v r0) 45 44;
  let r1  = (a1 +^ r0) >>^ 44ul in
  let a2' = a2 +^ r1 in
  upd_3 acc a0' a1' a2'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val carry_last_unrolled:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ bounds (as_seq h acc) p44 p44 (p42+1)
      /\ (v (Seq.index (as_seq h acc) 2) = p42 ==> v (Seq.index (as_seq h acc) 1) = 0)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ bounds (as_seq h0 acc) p44 p44 (p42+1)
      /\ (v (Seq.index (as_seq h0 acc) 2) = p42 ==> v (Seq.index (as_seq h0 acc) 1) = 0)
      /\ live h1 acc /\ bounds (as_seq h1 acc) p44 p44 p42
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == carry_last_unrolled (as_seq h0 acc)))
let carry_last_unrolled acc =
  let h = ST.get() in
  lemma_carried_is_fine_to_carry_top (as_seq h acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec (as_seq h acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ (as_seq h acc);
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc


val poly1305_last_pass:
  acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ red_45 (as_seq h acc)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ live h1 acc /\ red_45 (as_seq h0 acc)
      /\ modifies_1 acc h0 h1
      /\ as_seq h1 acc == poly1305_last_pass_spec (as_seq h0 acc)))
let poly1305_last_pass acc =
  let h = ST.get() in
  last_pass_is_fine (as_seq h acc);
  lemma_carried_is_fine_to_carry (as_seq h acc);
  Hacl.Bignum.Fproduct.carry_limb_ acc 0ul;
  let h1 = ST.get() in
  lemma_carried_is_fine_to_carry_top (as_seq h1 acc);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec (as_seq h1 acc);
  Hacl.Bignum.Modulo.carry_top acc;
  carry_limb_unrolled acc;
  carry_last_unrolled acc;
  poly1305_last_pass_ acc


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val bignum_to_128:
  a:felem ->
  Stack wide
    (requires (fun h -> live h a /\ bounds (as_seq h a) p44 p44 p42))
    (ensures (fun h0 z h1 -> live h0 a /\ bounds (as_seq h0 a) p44 p44 p42
      /\ h0 == h1 /\ z == bignum_to_128 (as_seq h0 a)))
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


inline_for_extraction val poly1305_finish__:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h0 st /\ live h0 m
      /\ live h1 st.h /\ live h1 mac /\ live h0 key_s
      /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ red_45 (as_seq h1 st.h)
      /\ (let r1   = as_seq h1 st.r in
         let r0   = as_seq h0 st.r in
         let acc1 = as_seq h1 st.h in
         let acc0 = as_seq h0 st.h in
         let log  = reveal log in
         let log' = reveal updated_log in
         let m    = as_seq h0 m in
         Spec.MkState r1 acc1 log' == (
           if U64.(len =^ 0uL) then Spec.MkState r0 acc0 log
           else poly1305_process_last_block_spec (Spec.MkState r0 acc0 log) m len))
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
inline_for_extraction let poly1305_finish__ log st mac m len key_s =
  let h0 = ST.get() in
  if U64.(len =^ 0uL) then (log)
  else (
    let last_block = m in
    poly1305_process_last_block log st m len
    )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

(* val poly1305_finish_spec: *)
(*   st:Spec.poly1305_state_{red_44 Spec.(MkState?.r st) /\ red_45 Spec.(MkState?.h st)} -> *)
(*   m:word -> *)
(*   rem':limb{v rem' = Seq.length m /\ Seq.length m < 16} -> *)
(*   key_s:Seq.seq H8.t{Seq.length key_s = 16} -> *)
(*   Tot word_16 *)
(* let poly1305_finish_spec st m rem' key_s = *)
(*   let st' = if U64.(rem' =^ 0uL) then st *)
(*            else poly1305_process_last_block_spec st m rem' in *)
(*   let acc = poly1305_last_pass_spec Spec.(MkState?.h st') in *)
(*   let k' = load128_le_spec key_s in *)
(*   let open Hacl.Bignum.Wide in *)
(*   let acc' = Spec.bignum_to_128 acc in *)
(*   let mac = acc' +%^ k' in *)
(*   let mac = store128_le_spec mac in *)
(*   mac *)


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
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_finish_ log st mac m len key_s =
  let acc = st.h in
  let h0 = ST.get() in
  let log' = poly1305_finish__ log st mac m len key_s in
  poly1305_last_pass acc;
  cut (disjoint acc mac);
  let h2 = ST.get() in
  no_upd_lemma_1 h0 h2 acc key_s;
  let k'  = load128_le key_s in
  cut (k' = load128_le_spec (as_seq h0 key_s));
  let open Hacl.Bignum.Wide in
  let acc' = bignum_to_128 acc in
  let mac' = acc' +%^ k' in
  store128_le mac mac'


(* ************************************************ *)
(*                Standalone code                   *)
(* ************************************************ *)


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st /\ live_st h0 st /\ live h0 m
      /\ red_45 (as_seq h0 st.h)
      /\ red_44 (as_seq h0 st.r)
      /\ red_45 (as_seq h1 st.h)
      /\ Spec.MkState (as_seq h1 st.r) (as_seq h1 st.h) (reveal updated_log) == poly1305_blocks_spec (Spec.MkState (as_seq h0 st.r) (as_seq h0 st.h) (reveal current_log)) (as_seq h0 m) len
      ))
let rec poly1305_blocks log st m len =
  let m0 = ST.get() in
  if U64.(len =^ 0uL) then (
    log
  )
  else (
    let new_log = poly1305_update log st m in
    let len = U64.(len -^ 1uL) in
    let m   = offset m 16ul in
    poly1305_blocks new_log st m len
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 /\ live h0 input /\ live h0 k
      /\ as_seq h1 output == crypto_onetimeauth_spec (as_seq h0 input) len (as_seq h0 k)))
let crypto_onetimeauth output input len k =
  push_frame();
  let len16 = U64.(len >>^ 4ul) in
  let rem16 = U64.(len &^ 0xfuL) in
  let partial_input = Buffer.sub input 0ul U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) in
  let last_block    = Buffer.sub input U32.(16ul *^ Int.Cast.uint64_to_uint32 len16) (Int.Cast.uint64_to_uint32 len) in
  let buf = create limb_zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = MkState r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st key_r in
  let partial_log = poly1305_blocks init_log st partial_input len16 in
  let final_log = poly1305_finish_ partial_log st output last_block rem16 key_s in
  pop_frame()
