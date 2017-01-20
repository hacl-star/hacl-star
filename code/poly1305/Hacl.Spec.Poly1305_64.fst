module Hacl.Spec.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.SeqProperties
open FStar.Endianness
open FStar.Int.Cast

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


(* Types from Low-level crypto *)
type byte = FStar.UInt8.t
type bytes = seq byte
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16
type text = seq word

let log_t = text

let elem : Type0 = b:int{ b >= 0 /\ b < prime }

noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

assume val load64_le_spec : b:Seq.seq H8.t{Seq.length b = 8} -> Tot (r:limb{v r == little_endian b})
assume val store64_le_spec: r:limb -> Tot (b:Seq.seq H8.t{Seq.length b = 8 /\ v r == little_endian b})

assume val load128_le_spec : b:word_16 -> Tot (r:wide{Wide.v r == little_endian b})
assume val store128_le_spec: r:wide -> Tot (b:word_16{Wide.v r == little_endian b})

(* let lemma_cast_shift (a:H8.t) (off:U32.t{U32.v off <= 56}) : Lemma *)
(*   (let a' = Limb.(sint8_to_sint64 a <<^ off) in *)
(*    Limb.v a' = pow2 (U32.v off) * H8.v a *)
(*    /\ Limb.v a' < pow2 (8 + U32.v off) *)
(*    /\ Limb.v a' % pow2 (U32.v off) = 0 *)
(*    ) *)
(*   = assert_norm(pow2 8 = 256); *)
(*     assert_norm(pow2 64 = 0x10000000000000000); *)
(*     let a' = sint8_to_sint64 a in *)
(*     let a'' = Limb.(a' <<^ off) in *)
(*     Math.Lemmas.pow2_plus 8 (U32.v off); *)
(*     Math.Lemmas.pow2_le_compat (64) (8 + U32.v off); *)
(*     Math.Lemmas.modulo_lemma (H8.v a * pow2 (U32.v off)) (pow2 64); *)
(*     Math.Lemmas.lemma_mod_plus 0 (H8.v a) (pow2 (U32.v off)); *)
(*     cut (Limb.v a'' = 0 + H8.v a * pow2 (U32.v off)); *)
(*     Math.Lemmas.modulo_lemma 0 (pow2 (U32.v off)) *)

(* (\* let lemma_load64_le_spec (b0:H8.t) (b1:H8.t) (b2:H8.t) (b3:H8.t) (b4:H8.t) (b5:H8.t) (b6:H8.t) (b7:H8.t) : Lemma (H8.(v b0 + pow2 8 * v b1 + pow2 8 * v b1 + pow2 8 * v b1 + pow2 8 * v b1 + pow2 8 * v b1 + pow2 8 * v b + pow2 56 * v b7) *\) *)

(* val load64_le_spec: b:Seq.seq H8.t{Seq.length b = 8} -> Tot (r:limb{v r = little_endian b}) *)
(* let load64_le_spec b = *)
(*   admit(); *)
(*   assert_norm (pow2 32 = 0x100000000); *)
(*   let b0 = Seq.index b 0 in *)
(*   let b1 = Seq.index b 1 in *)
(*   let b2 = Seq.index b 2 in *)
(*   let b3 = Seq.index b 3 in *)
(*   let b4 = Seq.index b 4 in *)
(*   let b5 = Seq.index b 5 in *)
(*   let b6 = Seq.index b 6 in *)
(*   let b7 = Seq.index b 7 in *)
(*   Limb.( *)
(*     sint8_to_sint64 b0 *)
(*     |^ (sint8_to_sint64 b1 <<^ 8ul) *)
(*     |^ (sint8_to_sint64 b2 <<^ 16ul) *)
(*     |^ (sint8_to_sint64 b3 <<^ 24ul) *)
(*     |^ (sint8_to_sint64 b4 <<^ 32ul) *)
(*     |^ (sint8_to_sint64 b5 <<^ 40ul) *)
(*     |^ (sint8_to_sint64 b6 <<^ 48ul) *)
(*     |^ (sint8_to_sint64 b7 <<^ 56ul) *)
(*   ) *)

(* #set-options "--lax" *)
(* val store64_le_spec: z:Limb.t -> Tot (b:Seq.seq H8.t{Seq.length b = 8}) *)
(* let store64_le_spec z = *)
(*   assert_norm (pow2 32 = 0x100000000); *)
(*   let open Hacl.UInt64 in *)
(*   let b0 = sint64_to_sint8 z in *)
(*   let b1 = sint64_to_sint8 (z >>^ 8ul) in *)
(*   let b2 = sint64_to_sint8 (z >>^ 16ul) in *)
(*   let b3 = sint64_to_sint8 (z >>^ 24ul) in *)
(*   let b4 = sint64_to_sint8 (z >>^ 32ul) in *)
(*   let b5 = sint64_to_sint8 (z >>^ 40ul) in *)
(*   let b6 = sint64_to_sint8 (z >>^ 48ul) in *)
(*   let b7 = sint64_to_sint8 (z >>^ 56ul) in *)
(*   let s = Seq.create 8 (uint8_to_sint8 0uy) in *)
(*   let s = Seq.upd s 0 b0 in *)
(*   let s = Seq.upd s 1 b1 in *)
(*   let s = Seq.upd s 2 b2 in *)
(*   let s = Seq.upd s 3 b3 in *)
(*   let s = Seq.upd s 4 b4 in *)
(*   let s = Seq.upd s 5 b5 in *)
(*   let s = Seq.upd s 6 b6 in *)
(*   let s = Seq.upd s 7 b7 in *)
(*   s *)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

(** From the current memory state, returns the field element corresponding to a elemB *)
val selem: seqelem -> GTot elem
let selem s = seval s % prime


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


(* TODO: move to kremlib or another associated library *)
inline_for_extraction
val load128: high:UInt64.t -> low:UInt64.t -> Tot (z:UInt128.t{UInt128.v z = pow2 64 * UInt64.v high
  + UInt64.v low})
inline_for_extraction
let load128 h l =
  let open FStar.UInt128 in
  let hs = uint64_to_uint128 h <<^ 64ul in
  let ls = uint64_to_uint128 l in
  Math.Lemmas.modulo_lemma (UInt64.v h * pow2 64) (pow2 128);
  UInt.logor_disjoint #128 (v hs) (v ls) 64;
  hs |^ ls



inline_for_extraction private
let clamp_mask : cm:wide{Wide.v cm = 0x0ffffffc0ffffffc0ffffffc0fffffff} =
  load128 (0x0ffffffc0ffffffcuL) (0x0ffffffc0fffffffuL)


inline_for_extraction let mask_44 : m:limb{v m = pow2 44 - 1} =
  assert_norm(pow2 44 - 1 = 0xfffffffffff);
  uint64_to_limb 0xfffffffffffuL

inline_for_extraction let mask_42 : m:limb{v m = pow2 42 - 1} =
  assert_norm(pow2 42 - 1 = 0x3ffffffffff);
  uint64_to_limb 0x3ffffffffffuL

inline_for_extraction let mask_40 : m:limb{v m = pow2 40 - 1} =
  assert_norm(pow2 40 - 1 = 0xffffffffff);
  uint64_to_limb 0xffffffffffuL


private
let lemma_encode_r0 (k:wide) : Lemma (let r0 = Limb.(sint128_to_sint64 k &^ mask_44) in
   v r0 = Wide.v k % pow2 44)
  = UInt.logand_mask (v (sint128_to_sint64 k)) 44;
    Math.Lemmas.pow2_modulo_modulo_lemma_1 (Wide.v k) 44 64


private
let lemma_encode_r1 (k:wide) : Lemma (let r1 = Limb.(sint128_to_sint64 Wide.(k >>^ 44ul) &^ mask_44) in
   v r1 = (Wide.v k / pow2 44) % pow2 44)
  = UInt.logand_mask (v (sint128_to_sint64 Wide.(k >>^ 44ul))) 44;
    Math.Lemmas.pow2_modulo_modulo_lemma_1 (Wide.(v (k >>^ 44ul))) 44 64


private
let lemma_encode_r2 (k:wide) : Lemma (let r2 = Limb.(sint128_to_sint64 Wide.(k >>^ 88ul)) in
   v r2 = (Wide.v k / pow2 88))
  = Math.Lemmas.lemma_div_lt (Wide.v k) 128 88;
    Math.Lemmas.modulo_lemma (Wide.(v (k >>^ 88ul))) (pow2 64)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

private
let lemma_encode_r (k:wide) : Lemma (let r0 = Limb.(sint128_to_sint64 k &^ mask_44) in
  let r1 = Limb.(sint128_to_sint64 Wide.(k >>^ 44ul) &^ mask_44) in
  let r2 = Limb.(sint128_to_sint64 Wide.(k >>^ 88ul)) in
  v r0 + pow2 44 * v r1 + pow2 88 * v r2 = Wide.v k
  /\ v r0 < pow2 44 /\ v r1 < pow2 44 /\ v r2 < pow2 40)
  = let vk = Wide.v k in
    Math.Lemmas.lemma_div_mod vk (pow2 88);
    Math.Lemmas.lemma_div_mod (vk % pow2 88) (pow2 44);
    Math.Lemmas.pow2_modulo_modulo_lemma_1 vk 44 88;
    Math.Lemmas.pow2_modulo_division_lemma_1 vk 44 88;
    lemma_encode_r0 k; lemma_encode_r1 k; lemma_encode_r2 k;
    Math.Lemmas.lemma_div_lt (Wide.v k) 128 88


#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

val toField_spec: m:word_16 -> Tot (s':seqelem{red_44 s' /\ v (Seq.index s' 2) < pow2 40
  /\ seval s' = little_endian m})
let toField_spec block =
  let m = load128_le_spec block in
  let r0 = Limb.(sint128_to_sint64 m &^ mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(m >>^ 44ul)) &^ mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(m >>^ 88ul))) in
  lemma_encode_r m;
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 40 = 0x10000000000);
  let s = create_3 r0 r1 r2 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 s;
  s


val poly1305_encode_r_spec: key:Seq.seq H8.t{Seq.length key = 16} -> Tot (s':seqelem{red_44 s'
  /\ seval s' = UInt.logand #128 (little_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff})
let poly1305_encode_r_spec key =
  let k = load128_le_spec key in
  let k_clamped = Wide.(k &^ clamp_mask) in
  let r0 = Limb.(sint128_to_sint64 k_clamped &^ mask_44) in
  let r1 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 44ul)) &^ mask_44) in
  let r2 = Limb.(sint128_to_sint64 (Wide.(k_clamped >>^ 88ul))) in
  lemma_encode_r k_clamped;
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 40 = 0x10000000000);
  let s = create_3 r0 r1 r2 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 s;
  s


#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0"

val toField_plus_2_128_spec: m:word_16 -> Tot (s:seqelem{red_44 s
  /\ seval s = little_endian m + pow2 128})
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
  let m' = Seq.upd b 2 b2' in
  cut (Seq.index m' 0 == Seq.index b 0 /\ Seq.index m' 1 == Seq.index b 1
    /\ v (Seq.index m' 2) = v (Seq.index b 2) + pow2 40);
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 m';
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 b;
  Math.Lemmas.distributivity_add_right (pow2 88) (v (Seq.index b 2)) (pow2 40);
  Math.Lemmas.pow2_plus 88 40;
  m'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_start_spec: unit -> Tot (s:seqelem{Seq.index s 0 == limb_zero /\ Seq.index s 1 == limb_zero /\ Seq.index s 2 == limb_zero /\ selem s = 0 /\ red_45 s
  /\ seval s = 0})
let poly1305_start_spec () =
  let s = Seq.create len limb_zero in
  lemma_seval_def (s) 3;
  lemma_seval_def (s) 2;
  lemma_seval_def (s) 1;
  lemma_seval_def (s) 0;
  s


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 16} ->
  Tot (st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)
    /\ seval (MkState?.r st) = UInt.logand #128 (little_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff
    /\ seval (MkState?.h st) = 0})
let poly1305_init_spec key =
  let r = poly1305_encode_r_spec key in
  let h = poly1305_start_spec () in
  MkState r h (Seq.createEmpty)


val poly1305_update_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word_16 ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) in
       let acc1 = seval (MkState?.h st') in
       let r0 = seval (MkState?.r st) in
       let r1 = seval (MkState?.r st') in
       let log0:seq word = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = little_endian m + pow2 128 in
       r0 = r1 /\ acc1 % prime = ((acc0 + block) * r0) % prime
       /\ (log1 == log0 @| (Seq.create 1 m)))})
let poly1305_update_spec st m =
  let block = toField_plus_2_128_spec m in
  cut (seval block = little_endian m + pow2 128);
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = Seq.append (MkState?.log st) (Seq.create 1 m) in
  let acc' = add_and_multiply_tot acc block r in
  cut (seval acc' % prime = ((seval acc + seval block) * seval r) % prime);
  MkState r acc' log


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

private val lemma_append_one_to_zeros_: unit -> Lemma
  (little_endian (Seq.create 1 (uint8_to_sint8 1uy)) = 1)
private let lemma_append_one_to_zeros_ () = little_endian_singleton (uint8_to_sint8 1uy)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

private val lemma_append_one_to_zeros: (n:nat{n >= 1 /\ n <= 16}) -> Lemma
  (little_endian (Seq.create 1 (uint8_to_sint8 1uy) @| Seq.create (n-1) (uint8_to_sint8 0uy)) = 1)
private let lemma_append_one_to_zeros n =
  let nm1:nat = n - 1 in
  let one = Seq.create 1 (uint8_to_sint8 1uy) in
  let zeros = Seq.create (nm1) (uint8_to_sint8 0uy) in
  let s = one @| zeros in
  Seq.lemma_eq_intro (tail s) zeros;
  little_endian_append one zeros;
  lemma_append_one_to_zeros_ ();
  little_endian_null (nm1)


private
val lemma_seq_append_little_endian: (m:word{Seq.length m < 16}) -> Lemma
  (let m' = Seq.upd (Seq.append m (Seq.create (16 - length m) (uint8_to_sint8 0uy))) (Seq.length m) (uint8_to_sint8 1uy) in
   little_endian m' = little_endian m + pow2 (8 * length m))
private let lemma_seq_append_little_endian m =
  let m' = Seq.append m (Seq.create (16 - length m) (uint8_to_sint8 0uy)) in
  let m'' = Seq.upd m' (length m) (uint8_to_sint8 1uy) in
  let one = Seq.create 1 (uint8_to_sint8 1uy) in
  let zeros = Seq.create (16 - length m - 1) (uint8_to_sint8 0uy) in
  let z'' = m @| one @| zeros in
  cut (m @| one @| zeros == m @| (one @| zeros));
  Seq.lemma_eq_intro m'' z'';
  lemma_append_one_to_zeros (16 - length m);
  little_endian_append one zeros;
  assert_norm(pow2 0 = 1);
  little_endian_append m (one @| zeros)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_process_last_block_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  rem':U64.t{U64.v rem' = Seq.length m /\ U64.v rem' < 16} ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) in
       let acc1 = seval (MkState?.h st') in
       let r0 = seval (MkState?.r st) in
       let r1 = seval (MkState?.r st') in
       let log0:seq word = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = little_endian m + pow2 (8 * v rem') in
       r0 = r1 /\ acc1 % prime = ((acc0 + block) * r0) % prime
       /\ (log1 == log0 @| (Seq.create 1 m)))})
let poly1305_process_last_block_spec st m rem' =
  assert_norm (pow2 8 = 256);
  let m' = Seq.append m (Seq.create (16 - U64.v rem') (uint8_to_sint8 0uy)) in
  let m'' = Seq.upd m' (U64.v rem') (uint8_to_sint8 1uy) in
  lemma_seq_append_little_endian m;
  let block = toField_spec m'' in
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = Seq.append (MkState?.log st) (Seq.create 1 m) in
  let acc' = add_and_multiply_tot acc block r in
  MkState r acc' log


#reset-options "--initial_fuel 0 --max_fuel 0"

val poly1305_last_pass_spec: acc:seqelem{red_45 acc} -> Tot (acc':seqelem{
    seval acc' % prime = seval acc % prime})
let poly1305_last_pass_spec acc =
  last_pass_is_fine acc;
  let acc1 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc 0 in
  let acc2 = Hacl.Spec.Bignum.Modulo.carry_top_spec acc1 in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec acc1;
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
  let k' = load128_le_spec key_s in
  (* let kl = load64_le_spec (Seq.slice key_s 0 8) in *)
  (* let kh = load64_le_spec (Seq.slice key_s 8 16) in *)
  let h0 = Seq.index acc 0 in
  let h1 = Seq.index acc 1 in
  let h2 = Seq.index acc 2 in
  let open Hacl.Bignum.Limb in
  let accl = h0 |^ (h1 <<^ 44ul) in
  let acch = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in
  let open Hacl.Bignum.Wide in
  let acc' = limb_to_wide accl |^ (limb_to_wide acch <<^ 64ul) in
  (* let k'   = limb_to_wide kl   |^ (limb_to_wide kh   <<^ 64ul) in *)
  let mac = acc' +%^ k' in
  let macl = wide_to_limb mac in
  let mach = wide_to_limb (mac >>^ 64ul) in
  Seq.append (store64_le_spec macl) (store64_le_spec mach)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val poly1305_blocks_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  len:U64.t{U64.v len <= Seq.length m} ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')})
      (decreases (U64.v len))
let rec poly1305_blocks_spec st m len =
  if U64.(len <^ 16uL) then st
  else (
    let mblock = Seq.slice m 0 16 in
    let m'     = Seq.slice m 16 (Seq.length m) in
    let st' = poly1305_update_spec st mblock in
    let len = U64.(len -^ 16uL) in
    poly1305_blocks_spec st' m' len
  )


val crypto_onetimeauth_spec:
  input:Seq.seq H8.t ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Seq.length input} ->
  k:Seq.seq H8.t{Seq.length k = 32} ->
  Tot (mac:Seq.seq H8.t{Seq.length mac = 16})
let crypto_onetimeauth_spec input len k =
  let init_st = poly1305_init_spec k in  
  let partial_st = poly1305_blocks_spec init_st input len in
  poly1305_finish_spec partial_st input len (Seq.slice k 16 32)
