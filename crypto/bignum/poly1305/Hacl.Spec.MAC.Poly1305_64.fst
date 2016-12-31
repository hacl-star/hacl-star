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

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

inline_for_extraction let log_t = unit

let elem : Type0 = b:int{ b >= 0 /\ b < prime }

let word = b:Seq.seq H8.t{Seq.length b <= 16}
let word_16 = b:Seq.seq H8.t{Seq.length b = 16}

(* noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> poly1305_state_ *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val load64_le_spec: b:Seq.seq H8.t{Seq.length b = 8} -> Tot limb
let load64_le_spec b =
  let b0 = Seq.index b 0 in
  let b1 = Seq.index b 1 in
  let b2 = Seq.index b 2 in
  let b3 = Seq.index b 3 in
  let b4 = Seq.index b 4 in
  let b5 = Seq.index b 5 in
  let b6 = Seq.index b 6 in
  let b7 = Seq.index b 7 in
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


val store64_le_spec: z:Limb.t -> Tot (b:Seq.seq H8.t{Seq.length b = 8})
let store64_le_spec z =
  let open Hacl.UInt64 in
  let b0 = sint64_to_sint8 z in
  let b1 = sint64_to_sint8 (z >>^ 8ul) in
  let b2 = sint64_to_sint8 (z >>^ 16ul) in
  let b3 = sint64_to_sint8 (z >>^ 24ul) in
  let b4 = sint64_to_sint8 (z >>^ 32ul) in
  let b5 = sint64_to_sint8 (z >>^ 40ul) in
  let b6 = sint64_to_sint8 (z >>^ 48ul) in
  let b7 = sint64_to_sint8 (z >>^ 56ul) in
  let s = Seq.create 8 (uint8_to_sint8 0uy) in
  let s = Seq.upd s 0 b0 in
  let s = Seq.upd s 1 b1 in
  let s = Seq.upd s 2 b2 in
  let s = Seq.upd s 3 b3 in
  let s = Seq.upd s 4 b4 in
  let s = Seq.upd s 5 b5 in
  let s = Seq.upd s 6 b6 in
  let s = Seq.upd s 7 b7 in
  s


(** From the current memory state, returns the field element corresponding to a elemB *)
val selem: seqelem -> GTot elem
let selem s = seval s % prime


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)

assume val lemma_logand_lt: #n:pos -> a:UInt.uint_t n -> m:pos{m < n} -> b:UInt.uint_t n{b < pow2 m} ->
  Lemma (pow2 m < pow2 n /\ UInt.logand #n a b < pow2 m)

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val poly1305_encode_r_spec: key:Seq.seq H8.t{Seq.length key = 16} -> Tot (s':seqelem{red_44 s'})
let poly1305_encode_r_spec key =
  let t0 = load64_le_spec (Seq.slice key 0 8) in
  let t1 = load64_le_spec (Seq.slice key 8 16) in
  let open Hacl.Bignum.Limb in
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 42 = 0x40000000000);
  let r0 = ( t0                           ) &^ uint64_to_limb 0xffc0fffffffuL in
  let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_limb 0xfffffc0ffffuL in
  let r2 = ((t1 >>^ 24ul)                 ) &^ uint64_to_limb 0x00ffffffc0fuL in
  let s = Seq.create len limb_zero in
  let s = Seq.upd s 0 r0 in
  let s = Seq.upd s 1 r1 in
  let s = Seq.upd s 2 r2 in
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f;
  s


inline_for_extraction let mask_42 : p:Hacl.Bignum.Limb.t{v p = pow2 42 - 1} = assert_norm(pow2 42 - 1 = 0x3ffffffffff); assert_norm(pow2 64 = 0x10000000000000000); uint64_to_limb 0x3ffffffffffuL

inline_for_extraction let mask_44 : p:Hacl.Bignum.Limb.t{v p = pow2 44 - 1} = assert_norm(pow2 44 - 1 = 0xfffffffffff);
  assert_norm (pow2 64 = 0x10000000000000000); uint64_to_limb 0xfffffffffffuL


val toField_spec: m:word_16 -> Tot (s:seqelem{red_44 s /\ v (Seq.index s 2) < pow2 40})
let toField_spec m =
  (* Load block values *)
  let t0 = load64_le_spec (Seq.slice m 0 8) in
  let t1 = load64_le_spec (Seq.slice m 8 16) in
  let open Hacl.UInt64 in  
  UInt.logand_mask (v t0) 44;
  UInt.logand_mask (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44;
  Math.Lemmas.lemma_div_lt (v t1) 64 24;
  Math.Lemmas.pow2_lt_compat 44 40;
  let t_0 = t0 &^ mask_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_44 in
  let t_2 = (t1 >>^ 24ul) in
  let b = Seq.create len limb_zero in
  let b = Seq.upd b 0 t_0 in
  let b = Seq.upd b 1 t_1 in
  let b = Seq.upd b 2 t_2 in
  b


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val toField_plus_2_128_spec: m:word_16 -> Tot (s:seqelem{red_44 s})
let toField_plus_2_128_spec m =
  let b = toField_spec m in
  let b2 = Seq.index b 2 in
  cut (v b2 < pow2 40);
  let open Hacl.Bignum.Limb in
  assert_norm (0 = 0x10000000000 % pow2 40);
  assert_norm (pow2 40 = 0x10000000000);
  UInt.logor_disjoint (0x10000000000) (v b2) 40;
  assert_norm (pow2 40 + pow2 40 < pow2 44);
  let b2' = uint64_to_limb 0x10000000000uL |^ b2 in
  Seq.upd b 2 b2'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

assume val lemma_logor_max: #n:pos -> a:UInt.uint_t n -> b:UInt.uint_t n -> m:nat{m <= n} -> Lemma
  (requires (a < pow2 m /\ b < pow2 m))
  (ensures (UInt.logor a b < pow2 m))

val toField_plus_spec: len:U32.t{U32.v len < 16} -> m:word{Seq.length m = U32.v len} ->
  Tot (s:seqelem{red_44 s})
let toField_plus_spec len m' =
  cut (pow2 (24 + U32.v len) % pow2 (24 + U32.v len) = 0);
  let m = Seq.append m' (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy)) in
  let b = toField_spec m in
  let b2 = Seq.index b 2 in
  let open Hacl.Bignum.Limb in
  let b2' = uint64_to_sint64 1uL <<^ (U32.(24ul +^ len)) |^ b2 in
  Math.Lemmas.pow2_lt_compat 64 (24 + U32.v len);
  Math.Lemmas.modulo_lemma (pow2 (24 + U32.v len)) (pow2 64);
  Math.Lemmas.pow2_lt_compat 44 (24 + U32.v len);
  lemma_logor_max #64 (pow2 (24 + U32.v len)) (v b2) 44;
  Seq.upd b 2 b2'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_finish_spec: acc:seqelem{red_45 acc} -> key_s:Seq.seq H8.t{Seq.length key_s = 16} ->
  Tot (mac:Seq.seq H8.t{Seq.length mac = 16})
let poly1305_finish_spec acc key_s =
  Math.Lemmas.pow2_lt_compat 63 44;
  let acc1 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc 0 in
  (* assume (v (Seq.index (as_seq h1 acc) 2) < pow2 45 + pow2 20); *)
  assert_norm(pow2 45 + pow2 20 = 0x200000000000 + 0x100000);
  assert_norm(pow2 42 = 0x40000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  let acc2 = Hacl.Spec.Bignum.Modulo.carry_top_spec acc1 in
  let acc3 = Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec acc in
  (* Adding 2nd part of the key (one time pad) *)
  let key = toField_spec key_s in
  let acc4 = Hacl.Spec.Bignum.Fsum.fsum_spec acc key len in
  (* Last carry and truncation *)
  let acc5 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc 0 in
  let h0 = Seq.index acc5 0 in
  let h1 = Seq.index acc5 1 in
  let h2 = Seq.index acc5 2 in
  let open Hacl.Bignum.Limb in
  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in
  let mac0 = store64_le_spec h0 in
  let mac1 = store64_le_spec h1 in
  Seq.append mac0 mac1


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_start_spec: unit -> Tot (s:seqelem{Seq.index s 0 == limb_zero /\ Seq.index s 1 == limb_zero /\ Seq.index s 2 == limb_zero /\ selem s = 0})
let poly1305_start_spec () =
  let s = Seq.create len limb_zero in
  lemma_seval_def (s) 3;
  lemma_seval_def (s) 2;
  lemma_seval_def (s) 1;
  lemma_seval_def (s) 0;
  s

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


(* ******************* *)
(* Fast implementation *)
(* ******************* *)


val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ red_45 (as_seq h st.h) /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
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


val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p ->
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
  push_frame();
  let tmp   = create limb_zero clen in
  let rem' = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 - 1 = 0xf);
  UInt.logand_mask (U64.v len) 4;
  if U64.(rem' =^ 0uL) then ()
  else (
    let zero = uint8_to_sint8 0uy in
    let block = create zero 16ul in
    let i = FStar.Int.Cast.uint64_to_uint32 rem' in
    Math.Lemmas.modulo_lemma (U64.v len - U64.v rem') (pow2 32);
    blit m (FStar.Int.Cast.uint64_to_uint32 (U64.(len -^ rem'))) block 0ul i;
    block.(i) <- uint8_to_sint8 1uy;
    toField tmp block;
    add_and_multiply st.h tmp st.r
    );
  Hacl.Bignum.Fproduct.carry_limb_ st.h 0ul;
  Hacl.Bignum.Modulo.carry_top st.h;
  Hacl.Bignum.Fproduct.carry_0_to_1 st.h;
  toField tmp key_s;
  Hacl.Bignum.Fsum.fsum_ st.h tmp clen;
  Hacl.Bignum.Fproduct.carry_limb_ st.h 0ul;
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let open Hacl.Bignum.Limb in
  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ ((h2 &^ mask_42) <<^ 24ul) in
  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame();
  log // TODO


val crypto_onetimeauth:
  output:uint8_p ->
  input:uint8_p ->
  len:U64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let r = create zero clen in
  let h = create zero clen in
  let st = MkState r h in
  (* let st = {r = r; h = h} in *)
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st key_r in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()
