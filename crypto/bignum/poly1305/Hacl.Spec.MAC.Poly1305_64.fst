module Hacl.Spec.MAC.Poly1305_64

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

noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

val load64_le_spec: b:Seq.seq H8.t{Seq.length b = 8} -> Tot limb
let load64_le_spec b =
  assert_norm (pow2 32 = 0x100000000);
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

inline_for_extraction val create_3: s0:limb -> s1:limb -> s2:limb -> Tot (s:seqelem{
  Seq.index s 0 == s0 /\ Seq.index s 1 == s1 /\ Seq.index s 2 == s2})
inline_for_extraction let create_3 s0 s1 s2 =
  let s = Seq.create len limb_zero in
  let s = Seq.upd s 0 s0 in
  let s = Seq.upd s 1 s1 in
  let s = Seq.upd s 2 s2 in
  s
  

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
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f;
  create_3 r0 r1 r2


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
  create_3 t_0 t_1 t_2


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

val poly1305_start_spec: unit -> Tot (s:seqelem{Seq.index s 0 == limb_zero /\ Seq.index s 1 == limb_zero /\ Seq.index s 2 == limb_zero /\ selem s = 0 /\ red_45 s})
let poly1305_start_spec () =
  let s = Seq.create len limb_zero in
  lemma_seval_def (s) 3;
  lemma_seval_def (s) 2;
  lemma_seval_def (s) 1;
  lemma_seval_def (s) 0;
  s


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 32} ->
  Tot (st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)})
let poly1305_init_spec key =
  let r = poly1305_encode_r_spec (Seq.slice key 0 16) in
  let h = poly1305_start_spec () in
  MkState r h ()


val poly1305_update_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t{Seq.length m >= 16} ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')})
let poly1305_update_spec st m =
  let block = toField_plus_2_128_spec (Seq.slice m 0 16) in
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = MkState?.log st in
  let acc' = add_and_multiply_tot acc block r in
  MkState r acc' log


val poly1305_blocks_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  len:U64.t{U64.v len <= Seq.length m} -> 
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')})
  (decreases (U64.v len))
let rec poly1305_blocks_spec st m len =
  if U64.(len <^ 16uL) then st
  else (
    let st' = poly1305_update_spec st m in
    let len = U64.(len -^ 16uL) in
    let m'   = Seq.slice m 16 (Seq.length m) in
    poly1305_blocks_spec st' m' len
  )



val poly1305_process_last_block_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  rem':U64.t{U64.v rem' = Seq.length m /\ U64.v rem' < 16} ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')})
let poly1305_process_last_block_spec st m rem' =
  assert_norm (pow2 8 = 256);
  let m' = Seq.append m (Seq.create (16 - U64.v rem') (uint8_to_sint8 0uy)) in
  let m'' = Seq.upd m' (U64.v rem') (uint8_to_sint8 1uy) in
  let block = toField_spec m'' in
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = MkState?.log st in
  let acc' = add_and_multiply_tot acc block r in
  MkState r acc' log


#set-options "--initial_fuel 0 --max_fuel 0"

val poly1305_last_pass_spec: acc:seqelem{red_45 acc} -> Tot (acc':seqelem)
let poly1305_last_pass_spec acc =
  last_pass_is_fine acc;
  let acc1 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc 0 in
  let acc2 = Hacl.Spec.Bignum.Modulo.carry_top_spec acc1 in
  Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec acc2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_finish_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Seq.length m} ->
  key_s:Seq.seq H8.t{Seq.length key_s = 16} ->
  Tot (m:Seq.seq H8.t{Seq.length m = 16})
let poly1305_finish_spec st m len key_s =
  assert_norm (pow2 64 = 0x10000000000000000);
  assert_norm (pow2 32 = 0x100000000);
  let rem' = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 - 1 = 0xf);
  UInt.logand_mask (U64.v len) 4;
  let st' = if U64.(rem' =^ 0uL) then st
           else poly1305_process_last_block_spec st (Seq.slice m (U64.v len - U64.v rem') (U64.v len)) rem' in
  let acc = poly1305_last_pass_spec (MkState?.h st') in
  let kl = load64_le_spec (Seq.slice key_s 0 8) in
  let kh = load64_le_spec (Seq.slice key_s 8 16) in
  let h0 = Seq.index acc 0 in
  let h1 = Seq.index acc 1 in
  let h2 = Seq.index acc 2 in
  let open Hacl.Bignum.Limb in
  let accl = h0 |^ (h1 <<^ 44ul) in
  let acch = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in
  let open Hacl.Bignum.Wide in
  let acc' = limb_to_wide accl |^ (limb_to_wide acch <<^ 64ul) in
  let k'   = limb_to_wide kl   |^ (limb_to_wide kh   <<^ 64ul) in
  let mac = acc' +%^ k' in
  let macl = wide_to_limb mac in
  let mach = wide_to_limb (mac >>^ 64ul) in
  Seq.append (store64_le_spec macl) (store64_le_spec mach)


val crypto_onetimeauth_spec:
  input:Seq.seq H8.t ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Seq.length input} ->
  k:Seq.seq H8.t{Seq.length k = 32} ->
  Tot (mac:Seq.seq H8.t{Seq.length mac = 16})
let crypto_onetimeauth_spec input len k =
  let init_st = poly1305_init_spec k in  
  let partial_st = poly1305_blocks_spec init_st input len in
  poly1305_finish_spec partial_st input len (Seq.slice k 16 32)
