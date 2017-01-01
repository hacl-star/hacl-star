module Hacl.MAC.Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Buffer
open FStar.Ghost
open FStar.SeqProperties
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
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

let wordB = b:uint8_p{length b <= 16}
let wordB_16 = b:uint8_p{length b = 16}

noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val load64_le:
  b:uint8_p{length b = 8} ->
  Stack limb
    (requires (fun h -> live h b))
    (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 b
      (* /\ Limb.v r = little_endian (as_seq h0 b) *)
      ))
let load64_le b =
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
  (* lemma_little_endian_8 h b; *)
  (* lemma_load64_le b0 b1 b2 b3 b4 b5 b6 b7; *)
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


val store64_le:
  b:uint8_p{length b = 8} ->
  z:Limb.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      (* /\ Limb.v z = little_endian (as_seq h1 b) *)
      ))
let store64_le b z =
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
  (* lemma_little_endian_8 h1 b; *)
  (* lemma_store64_le_ z; *)
  ()


val sel_word:
  h:mem ->
  b:wordB{live h b} ->
  GTot (s:Seq.seq H8.t{Seq.length s = length b
    /\ (forall (i:nat). {:pattern (Seq.index s i)}
      i < Seq.length s ==> H8.v (Seq.index s i) == H8.v (get h b i))})
let sel_word h b = as_seq h b

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = eval h b


let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val mk_mask: nbits:U32.t{U32.v nbits < 64} -> Tot (z:limb{Limb.v z = pow2 (U32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (U32.v nbits);
  cut( (1*pow2 (U32.v nbits)) % pow2 64 = pow2 (U32.v nbits));
  let one = uint64_to_sint64 1uL in
  Limb.((one <<^ nbits) -^ one)


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

assume val lemma_logand_lt: #n:pos -> a:UInt.uint_t n -> m:pos{m < n} -> b:UInt.uint_t n{b < pow2 m} ->
  Lemma (pow2 m < pow2 n /\ UInt.logand #n a b < pow2 m)


val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      (* /\ sel_elem h1 r = Hacl.Symmetric.Poly1305_64.FC.Spec.clamp (sel_word h0 (sub key 0ul 16ul)) *)
    ))
let poly1305_encode_r r key =
  let t0 = load64_le(sub key 0ul 8ul) in
  let t1 = load64_le(sub key 8ul 8ul) in
  let open Hacl.Bignum.Limb in
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 42 = 0x40000000000);
  let r0 = ( t0                           ) &^ uint64_to_limb 0xffc0fffffffuL in
  let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_limb 0xfffffc0ffffuL in
  let r2 = ((t1 >>^ 24ul)                 ) &^ uint64_to_limb 0x00ffffffc0fuL in
  r.(0ul) <- r0;
  r.(1ul) <- r1;
  r.(2ul) <- r2;
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f


inline_for_extraction let mask_42 : p:Hacl.Bignum.Limb.t{v p = pow2 42 - 1} = assert_norm(pow2 42 - 1 = 0x3ffffffffff); assert_norm(pow2 64 = 0x10000000000000000); uint64_to_limb 0x3ffffffffffuL
  
inline_for_extraction let mask_44 : p:Hacl.Bignum.Limb.t{v p = pow2 44 - 1} = assert_norm(pow2 44 - 1 = 0xfffffffffff);
  assert_norm (pow2 64 = 0x10000000000000000); uint64_to_limb 0xfffffffffffuL


val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      /\ red_44 (as_seq h1 b)
      /\ v (Seq.index (as_seq h1 b) 2) < pow2 40))
let toField b m =
  (* Load block values *)
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
  b.(0ul) <- t_0;
  b.(1ul) <- t_1;
  b.(2ul) <- t_2


val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      /\ red_44 (as_seq h1 b)))
let toField_plus_2_128 b m =
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
      ))
let poly1305_start a =
  (* Zeroing the accumulator *)
  a.(0ul) <- limb_zero;
  a.(1ul) <- limb_zero;
  a.(2ul) <- limb_zero;
  let h = ST.get() in
  lemma_seval_def (as_seq h a) 3;
  lemma_seval_def (as_seq h a) 2;
  lemma_seval_def (as_seq h a) 1;
  lemma_seval_def (as_seq h a) 0


(* ******************* *)
(* Fast implementation *)
(* ******************* *)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ red_45 (as_seq h st.h) /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 log st *)
      ))
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h


val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m >= 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 updated_log st *)
      (* /\ (reveal updated_log) == *)
      (*     SeqProperties.snoc (reveal current_log) (encode (sel_word h1 (Buffer.sub m 0ul 16ul))) *)
      (* /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r) *)
      ))
let poly1305_update log st m =
  push_frame();
  let tmp = create limb_zero clen in
  let acc = st.h in
  let r   = st.r in
  toField_plus_2_128 tmp (sub m 0ul 16ul);
  add_and_multiply acc tmp r;
  let new_log = (* elift1 (fun l -> SeqProperties.snoc l (eval_3_limbs h0 h1 h2)) log in *) () in
  pop_frame();
  new_log


val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 updated_log st *)
      (* /\ (reveal updated_log) == *)
      (*     encode_pad (reveal current_log) (as_seq h0 (Buffer.sub m 0ul (Int.Cast.uint64_to_uint32 len))) *)
      (* /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r) *)
      ))
let rec poly1305_blocks log st m len =
  let m0 = ST.get() in
  if U64.(len <^ 16uL) then (
    (* log *)
    ()
  )
  else (
    let new_log = poly1305_update log st m in
    let len = U64.(len -^ 16uL) in
    let m   = offset m 16ul in
    poly1305_blocks new_log st m len
  )


val poly1305_process_last_block:
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len < 16 /\ U64.v len = length m} ->
  Stack unit
    (requires (fun h -> live_st h st /\ live h m /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures (fun h0 _ h1 -> live_st h0 st /\ live h0 m /\ red_44 (as_seq h0 st.r) /\ red_45 (as_seq h0 st.h)
      /\ live_st h1 st /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      /\ modifies_1 st.h h0 h1))
let poly1305_process_last_block st m rem' =
  push_frame();
  let tmp = create limb_zero clen in
  push_frame();
  let zero = uint8_to_sint8 0uy in
  let block = create zero 16ul in
  let i = FStar.Int.Cast.uint64_to_uint32 rem' in
  (* Math.Lemmas.modulo_lemma (U64.v len - U64.v rem') (pow2 32); *)
  (* blit m (FStar.Int.Cast.uint64_to_uint32 (U64.(len -^ rem'))) block 0ul i; *)
  blit m 0ul block 0ul i;
  block.(i) <- uint8_to_sint8 1uy;
  toField tmp block;
  add_and_multiply st.h tmp st.r;
  pop_frame();
  pop_frame()


#set-options "--lax"

val poly1305_last_pass: acc:felem ->
  Stack unit
    (requires (fun h -> live h acc /\ red_45 (as_seq h acc)))
    (ensures (fun h0 _ h1 -> live h0 acc /\ live h1 acc /\ red_45 (as_seq h0 acc)
      /\ modifies_1 acc h0 h1))
let poly1305_last_pass acc =
  Hacl.Bignum.Fproduct.carry_limb_ acc 0ul;
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p{length mac = 16} ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun h -> (* acc_inv h log st *)live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1
      /\ live h1 st.h /\ live h1 mac
      (* /\ acc_inv h1 updated_log st *)
      ))
let poly1305_finish_ log st mac m len key_s =
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
    poly1305_process_last_block st (sub m start l) rem'
    );
  let h1 = ST.get() in
  cut (modifies_1 st.h h0 h1);
  poly1305_last_pass st.h;
  let h2 = ST.get() in
  cut (modifies_1 st.h h0 h2);
  cut (disjoint st.h mac);
  (* Hacl.Bignum.Fproduct.carry_limb_ st.h 0ul; *)
  (* Hacl.Bignum.Modulo.carry_top st.h; *)
  (* Hacl.Bignum.Fproduct.carry_0_to_1 st.h; *)
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
  store64_le (Buffer.sub mac 0ul 8ul) (wide_to_limb mac');
  store64_le (Buffer.sub mac 8ul 8ul) (wide_to_limb (mac' >>^ 64ul))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crypto_onetimeauth:
  output:uint8_p{length output = 16} ->
  input:uint8_p{disjoint input output} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length input} ->
  k:uint8_p{disjoint output k /\ length k = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let buf = create zero U32.(clen +^ clen) in
  let r = sub buf 0ul clen in
  let h = sub buf clen clen in
  let st = MkState r h in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st k in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()
