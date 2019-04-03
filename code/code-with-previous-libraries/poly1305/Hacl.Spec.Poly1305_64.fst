module Hacl.Spec.Poly1305_64

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
open FStar.Int.Cast.Full

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Endianness
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply

module Spec = Spec.Poly1305

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

include Hacl.Spec.Poly1305_64.State

(* (\* Types from Low-level crypto *\) *)
(* type byte = Hacl.UInt8.t *)
(* type bytes = seq byte *)
(* type word = w:bytes{length w <= 16} *)
(* type word_16 = w:bytes{length w = 16} *)
(* type tag = word_16 *)


(* (\* Types from specs *\) *)
(* type seqelem = seqelem *)

(* type word' = Spec.word *)
(* type text = Spec.text *)

(* let log_t = text *)

(* let elem : Type0 = b:int{ b >= 0 /\ b < prime } *)


(* inline_for_extraction let red_44 s = Hacl.Spec.Bignum.AddAndMultiply.red_44 s *)
(* inline_for_extraction let red_45 s = Hacl.Spec.Bignum.AddAndMultiply.red_45 s *)

(* inline_for_extraction let p42  = Hacl.Spec.Bignum.AddAndMultiply.p42 *)
(* inline_for_extraction let p44  = Hacl.Spec.Bignum.AddAndMultiply.p44 *)

(* noeq type poly1305_state_ = | MkState: r:seqelem -> h:seqelem -> log:log_t -> poly1305_state_ *)

#reset-options "--max_fuel 0 --z3rlimit 200"


val lemma_bignum_to_128_:
  h0:limb{v h0 < pow2 44} -> h1:limb{v h1 < pow2 44} -> h2:limb{v h2 < pow2 42} ->
  Lemma (((v h2 * (pow2 24)) % pow2 64 + v h1 / pow2 20) * pow2 64 + ((v h1 * pow2 44) % pow2 64) + v h0
    = (v h0 + pow2 44 * v h1 + pow2 88 * (v h2 % pow2 40)))
let lemma_bignum_to_128_ h0 h1 h2 =
  let v1 = ((v h2 * (pow2 24)) % pow2 64 + v h1 / pow2 20) * pow2 64 in
  Math.Lemmas.distributivity_add_left ((v h2 * pow2 24) % pow2 64) (v h1 / pow2 20) (pow2 64);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v h2) 64 24;
  Math.Lemmas.pow2_plus 64 24;
  Math.Lemmas.pow2_multiplication_division_lemma_2 (v h1) 64 44;
  cut (v1 = pow2 88 * (v h2 % pow2 40) + pow2 64 * ((v h1 * pow2 44)/ pow2 64));
  Math.Lemmas.lemma_div_mod (v h1 * pow2 44) (pow2 64)

private val lemma_aux: a:nat -> b:nat -> c:nat -> Lemma
  (requires (a < pow2 44 /\ b < pow2 44 /\ c < pow2 40))
  (ensures (a + pow2 44 * b + pow2 88 * c < pow2 128))
let lemma_aux a b c =
  assert_norm((pow2 44 - 1) + pow2 44 * (pow2 44 - 1) + (pow2 40 - 1) * pow2 88 < pow2 128)


val lemma_bignum_to_128:
  h0:limb{v h0 < pow2 44} -> h1:limb{v h1 < pow2 44} -> h2:limb{v h2 < pow2 42} ->
  Lemma (((v h2 * (pow2 24)) % pow2 64 + v h1 / pow2 20) * pow2 64 + ((v h1 * pow2 44) % pow2 64) + v h0
    = (v h0 + pow2 44 * v h1 + pow2 88 * v h2) % pow2 128)
let lemma_bignum_to_128 h0 h1 h2 =
  lemma_bignum_to_128_ h0 h1 h2;
  let z = (v h0 + pow2 44 * v h1 + pow2 88 * v h2) % pow2 128 in
  Math.Lemmas.lemma_mod_plus_distr_l (pow2 88 * v h2) (v h0 + pow2 44 * v h1) (pow2 128);
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v h2) 128 88;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v h2) 128 88;
  cut (z = (v h0 + pow2 44 * v h1 + (v h2 % pow2 40) * pow2 88) % pow2 128);
  assert_norm((pow2 44 - 1) + pow2 44 * (pow2 44 - 1) + (pow2 40 - 1) * pow2 88 < pow2 128);
  lemma_aux (v h0) (v h1) (v h2 % pow2 40);
  Math.Lemmas.modulo_lemma (v h0 + pow2 44 * v h1 + pow2 88 * (v h2 % pow2 40)) (pow2 128)

#reset-options "--max_fuel 0 --z3rlimit 200"

val bignum_to_128: s:seqelem{bounds s p44 p44 p42} -> Tot (acc:wide{Wide.v acc = seval s % pow2 128})
let bignum_to_128 s =
  let h0 = Seq.index s 0 in
  let h1 = Seq.index s 1 in
  let h2 = Seq.index s 2 in
  let open Hacl.Bignum.Limb in
  let accl = (h1 <<^ 44ul) |^ h0 in
  UInt.logor_disjoint (v (h1 <<^ 44ul)) (v h0) 44;
  cut (v accl = ((v h1 * pow2 44) % pow2 64) + v h0);
  let acch = (h2 <<^ 24ul) |^ (h1 >>^ 20ul) in
  Math.Lemmas.lemma_div_lt (v h1) 44 20;
  Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v h2) 64 24;
  Math.Lemmas.lemma_mod_plus 0 (v h2 % pow2 40) (pow2 24);
  UInt.logor_disjoint (v (h2 <<^ 24ul)) (v (h1 >>^ 20ul)) 24;
  cut (v acch = (v h2 * (pow2 24)) % pow2 64 + v h1 / pow2 20);
  Math.Lemmas.multiple_modulo_lemma (v acch) (pow2 64);
  let open Hacl.Bignum.Wide in  
  let acc' = (limb_to_wide acch <<^ 64ul) |^ limb_to_wide accl in
  UInt.logor_disjoint #128 (v (limb_to_wide acch <<^ 64ul)) (v (limb_to_wide accl)) 64;
  lemma_bignum_to_128 h0 h1 h2;
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 s;
  acc'


#reset-options "--z3rlimit 20 --max_fuel 0"

val load64_le_spec : b:bytes{Seq.length b = 8} -> GTot (r:limb{v r == hlittle_endian b})
let load64_le_spec b = lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint64_to_sint64 (UInt64.uint_to_t (hlittle_endian b))

val store64_le_spec: r:limb -> GTot (b:bytes{Seq.length b = 8 /\ v r == hlittle_endian b})
let store64_le_spec r = hlittle_bytes 8ul (v r)

val load128_le_spec : b:word_16 -> GTot (r:wide{Wide.v r == hlittle_endian b})
let load128_le_spec b = lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint128_to_sint128 (UInt128.uint_to_t (hlittle_endian b))

val store128_le_spec: r:wide -> GTot (b:word_16{Wide.v r == hlittle_endian b})
let store128_le_spec r = hlittle_bytes 16ul (w r)


#reset-options "--z3rlimit 20 --max_fuel 0"

(** From the current memory state, returns the field element corresponding to a elemB *)
val selem: seqelem -> GTot elem
let selem s = seval s % prime

inline_for_extraction
val seval: seqelem -> GTot nat
inline_for_extraction
let seval s = seval s


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#reset-options "--z3rlimit 20 --max_fuel 0"

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


(* TODO: move to kremlib or another associated library *)
inline_for_extraction
val hload128: high:UInt64.t -> low:UInt64.t -> Tot (z:wide{Hacl.UInt128.v z = pow2 64 * UInt64.v high
  + UInt64.v low})
inline_for_extraction
let hload128 h l =
  let open Hacl.UInt128 in
  let hs = uint64_to_sint128 h <<^ 64ul in
  let ls = uint64_to_sint128 l in
  Math.Lemmas.modulo_lemma (UInt64.v h * pow2 64) (pow2 128);
  UInt.logor_disjoint #128 (v hs) (v ls) 64;
  hs |^ ls



inline_for_extraction private
let clamp_mask : cm:wide{Wide.v cm = 0x0ffffffc0ffffffc0ffffffc0fffffff} =
  hload128 (0x0ffffffc0ffffffcuL) (0x0ffffffc0fffffffuL)


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


#reset-options "--z3rlimit 20 --max_fuel 0"

(* private *)
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


#reset-options "--z3rlimit 100 --max_fuel 0"

val toField_spec: m:word_16 -> GTot (s':seqelem{red_44 s' /\ v (Seq.index s' 2) < pow2 40
  /\ seval s' = hlittle_endian m})
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


val poly1305_encode_r_spec: key:Seq.seq H8.t{Seq.length key = 16} -> GTot (s':seqelem{red_44 s'
  /\ seval s' = UInt.logand #128 (hlittle_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff})
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


#reset-options "--z3rlimit 50 --max_fuel 0"

val toField_plus_2_128_spec: m:word_16 -> GTot (s:seqelem{red_44 s
  /\ seval s = hlittle_endian m + pow2 128})
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


#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_start_spec: unit -> Tot (s:seqelem{Seq.index s 0 == limb_zero /\ Seq.index s 1 == limb_zero /\ Seq.index s 2 == limb_zero /\ selem s = 0 /\ red_45 s
  /\ seval s = 0})
let poly1305_start_spec () =
  let s = Seq.create len limb_zero in
  lemma_seval_def (s) 3;
  lemma_seval_def (s) 2;
  lemma_seval_def (s) 1;
  lemma_seval_def (s) 0;
  s


#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 16} ->
  GTot (st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)
    /\ seval (MkState?.r st) = UInt.logand #128 (hlittle_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff
    /\ seval (MkState?.h st) = 0})
let poly1305_init_spec key =
  let r = poly1305_encode_r_spec key in
  let h = poly1305_start_spec () in
  MkState r h (Seq.createEmpty)


val poly1305_update_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word_16 ->
  GTot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) in
       let acc1 = seval (MkState?.h st') in
       let r0 = seval (MkState?.r st) in
       let r1 = seval (MkState?.r st') in
       let log0:seq word' = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = hlittle_endian m + pow2 128 in
       r0 = r1 /\ acc1 % prime = ((acc0 + block) * r0) % prime
       /\ (log1 == (Seq.create 1 (reveal_sbytes m)) @| log0))})
let poly1305_update_spec st m =
  let block = toField_plus_2_128_spec m in
  cut (seval block = hlittle_endian m + pow2 128);
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = Seq.append (Seq.create 1 (reveal_sbytes m)) (MkState?.log st) in
  let acc' = add_and_multiply_tot acc block r in
  cut (seval acc' % prime = ((seval acc + seval block) * seval r) % prime);
  MkState r acc' log


#reset-options "--max_fuel 0 --z3rlimit 50"

private val lemma_append_one_to_zeros_: unit -> Lemma
  (hlittle_endian (Seq.create 1 (uint8_to_sint8 1uy)) = 1)
private let lemma_append_one_to_zeros_ () = 
  little_endian_singleton (1uy)


#reset-options "--max_fuel 0 --z3rlimit 100"

private val lemma_append_one_to_zeros: (n:nat{n >= 1 /\ n <= 16}) -> Lemma
  (hlittle_endian (Seq.create 1 (uint8_to_sint8 1uy) @| Seq.create (n-1) (uint8_to_sint8 0uy)) = 1)
private let lemma_append_one_to_zeros n =
  let nm1:nat = n - 1 in
  let one = Seq.create 1 (1uy) in
  let zeros = Seq.create (nm1) (0uy) in
  let s = one @| zeros in
  Seq.lemma_eq_intro (tail s) zeros;
  little_endian_append one zeros;
  lemma_append_one_to_zeros_ ();
  little_endian_null (nm1)


private
val lemma_seq_append_little_endian: (m:word{Seq.length m < 16}) -> Lemma
  (let m' = Seq.upd (Seq.append m (Seq.create (16 - length m) (uint8_to_sint8 0uy))) (Seq.length m) (uint8_to_sint8 1uy) in
   hlittle_endian m' = hlittle_endian m + pow2 (8 * length m))
private let lemma_seq_append_little_endian m =
  let m = reveal_sbytes m in
  let m' = Seq.append m (Seq.create (16 - length m) (0uy)) in
  let m'' = Seq.upd m' (length m) (1uy) in
  let one = Seq.create 1 (1uy) in
  let zeros = Seq.create (16 - length m - 1) (0uy) in
  let z'' = m @| one @| zeros in
  cut (m @| one @| zeros == m @| (one @| zeros));
  Seq.lemma_eq_intro m'' z'';
  lemma_append_one_to_zeros (16 - length m);
  little_endian_append one zeros;
  assert_norm(pow2 0 = 1);
  little_endian_append m (one @| zeros)


#reset-options "--max_fuel 0 --z3rlimit 100"

val poly1305_process_last_block_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  rem':U64.t{U64.v rem' = Seq.length m /\ U64.v rem' < 16} ->
  GTot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) in
       let acc1 = seval (MkState?.h st') in
       let r0 = seval (MkState?.r st) in
       let r1 = seval (MkState?.r st') in
       let log0:seq word' = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = hlittle_endian m + pow2 (8 * U64.v rem') in
       r0 = r1 /\ acc1 % prime = ((acc0 + block) * r0) % prime
       /\ (log1 == (Seq.create 1 (reveal_sbytes m)) @| log0))})
let poly1305_process_last_block_spec st m rem' =
  assert_norm (pow2 8 = 256);
  let m' = Seq.append m (Seq.create (16 - U64.v rem') (uint8_to_sint8 0uy)) in
  let m'' = Seq.upd m' (U64.v rem') (uint8_to_sint8 1uy) in
  lemma_seq_append_little_endian m;
  let block = toField_spec m'' in
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = Seq.append (Seq.create 1 (reveal_sbytes m)) (MkState?.log st) in
  let acc' = add_and_multiply_tot acc block r in
  MkState r acc' log


#reset-options "--max_fuel 0"

inline_for_extraction let p44m5 : p:limb{v p = pow2 44 - 5} =
  assert_norm(pow2 44 - 5 = 0xffffffffffb); uint64_to_sint64 0xffffffffffbuL

inline_for_extraction let p44m1 : p:limb{v p = pow2 44 - 1} =
  assert_norm(pow2 44 - 1 = 0xfffffffffff); uint64_to_sint64 0xfffffffffffuL

inline_for_extraction let p42m1 : p:limb{v p = pow2 42 - 1} =
  assert_norm(pow2 42 - 1 = 0x3ffffffffff); uint64_to_sint64 0x3ffffffffffuL


#reset-options "--max_fuel 0 --z3rlimit 20"

val seq_upd_3: a0:limb -> a1:limb -> a2:limb -> Tot (s:seqelem{Seq.index s 0 == a0
  /\ Seq.index s 1 == a1 /\ Seq.index s 2 == a2})
let seq_upd_3 a0 a1 a2 =
  let s = Seq.create 3 limb_zero in
  let s = Seq.upd s 0 a0 in
  let s = Seq.upd s 1 a1 in
  let s = Seq.upd s 2 a2 in
  s


#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_poly_last_pass: s:seqelem{bounds s p44 p44 p42} -> Lemma
  (requires (bounds s p44 p44 p42 /\
    (let a0' = Seq.index s 0 in let a1' = Seq.index s 1 in let a2' = Seq.index s 2 in
     (v a0' <= 4 /\ v a1' = 0 /\ v a2' = 0) \/ (v a0' < pow2 44 - 5 \/ v a1' <> pow2 44 - 1 \/ v a2' <> pow2 42 - 1) )))
  (ensures (seval s = seval s % prime))
let lemma_poly_last_pass s =
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 s;
  assert_norm(pow2 44 = 0x100000000000); assert_norm(pow2 88 = 0x10000000000000000000000);
  assert_norm(pow2 44 - 5 + pow2 44 * (pow2 44 - 1) + pow2 88 * (pow2 42 - 1) = pow2 130 - 5);
  let a0' = Seq.index s 0 in let a1' = Seq.index s 1 in let a2' = Seq.index s 2 in
  if v a0'  <= 4 && v a1' = 0 && v a2' = 0 then Math.Lemmas.modulo_lemma (seval s) prime
  else (
    assert (v a0' + pow2 44 * v a1' + pow2 88 * v a2' < pow2 44 - 5 + pow2 44 * (pow2 44 - 1) + pow2 88 * (pow2 42 - 1));
    Math.Lemmas.modulo_lemma (seval s) prime)

val lemma_poly_last_pass': a0:limb -> a1:limb -> a2:limb -> Lemma
  (requires (let open Hacl.Bignum.Limb in
    v a0 >= pow2 44 - 5 /\ v a1 = pow2 44 - 1 /\ v a2 = pow2 42 - 1))
  (ensures (let open Hacl.Bignum.Limb in
    (v a0 - (pow2 44 - 5) + pow2 44 * (v a1 - (pow2 44 - 1)) + pow2 88 * (v a2 - (pow2 42 - 1))) % prime
    = (v a0 + pow2 44 * (v a1) + pow2 88 * (v a2)) % prime))
let lemma_poly_last_pass' a0 a1 a2 =
  assert_norm(pow2 130 - 5 = 0x3fffffffffffffffffffffffffffffffb);
  assert_norm(pow2 44 = 0x100000000000); assert_norm(pow2 88 = 0x10000000000000000000000);
  Math.Lemmas.distributivity_add_right (pow2 44) (v a1) (pow2 44 - 1);
  Math.Lemmas.distributivity_add_right (pow2 88) (v a2) (pow2 42 - 1);
  assert_norm(pow2 44 - 5 + pow2 44 * (pow2 44 - 1) + pow2 88 * (pow2 42 - 1) = pow2 130 - 5);
  Math.Lemmas.lemma_mod_plus (v a0 + pow2 44 * (v a1) + pow2 88 * (v a2)) 1 prime

val lemma_poly_last_pass'': a0:limb -> a1:limb -> a2:limb -> Lemma
  (requires (true))
  (ensures (let open Hacl.Bignum.Limb in
    (v a0 >= pow2 44 - 5 /\ v a1 = pow2 44 - 1 /\ v a2 = pow2 42 - 1) ==>
    ((v a0 - (pow2 44 - 5) + pow2 44 * (v a1 - (pow2 44 - 1)) + pow2 88 * (v a2 - (pow2 42 - 1))) % prime
    = (v a0 + pow2 44 * (v a1) + pow2 88 * (v a2)) % prime)))
let lemma_poly_last_pass'' a0 a1 a2 =
  if (v a0 >= pow2 44 - 5 && v a1 = pow2 44 - 1 && v a2 = pow2 42 - 1)
  then lemma_poly_last_pass' a0 a1 a2


#reset-options "--max_fuel 0 --z3rlimit 100"

val poly1305_last_pass_spec_: acc:seqelem{bounds acc p44 p44 p42} -> Tot (acc':seqelem{
  bounds acc' p44 p44 p42 /\  seval acc' = seval acc % prime})
let poly1305_last_pass_spec_ acc =
  let a0 = Seq.index acc 0 in
  let a1 = Seq.index acc 1 in
  let a2 = Seq.index acc 2 in
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
  cut ( (v a0 >= pow2 44 - 5 /\ v a1 = pow2 44 - 1 /\ v a2 = pow2 42 - 1) ==> (v a0' <= 4 /\ v a1' = 0 /\ v a2' = 0) );
  cut ( (v a0 < pow2 44 - 5 \/ v a1 <> pow2 44 - 1 \/ v a2 <> pow2 42 - 1) ==> (v a0' = v a0 /\ v a1' = v a1 /\ v a2' = v a2) );
  let acc' = seq_upd_3 a0' a1' a2' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 acc';
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 acc;
  lemma_poly_last_pass acc';
  lemma_poly_last_pass'' a0 a1 a2;
  cut (bounds acc' p44 p44 p42);
  Math.Lemmas.modulo_lemma (seval acc') prime;
  acc'


#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_carry_limb_unrolled: a0:limb -> a1:limb -> a2:limb ->
  Lemma (v a0 % p44 + p44 * ((v a1 + v a0 / p44) % p44) + pow2 88 * (v a2 + ((v a1 + v a0 / p44) / p44))
    = v a0 + p44 * v a1 + pow2 88 * v a2)
let lemma_carry_limb_unrolled a0 a1 a2 =
  let z = v a0 % p44 + p44 * ((v a1 + v a0 / p44) % p44) + pow2 88 * (v a2 + ((v a1 + v a0 / p44) / p44)) in
  let p88 = pow2 88 in
  let open FStar.Math.Lemmas in
  distributivity_add_right (pow2 88) (v a2) ((v a1 + v a0 / p44) / p44);
  cut (z = v a0 % p44 + p44 * ((v a1 + v a0 / p44) % p44) + p88 * v a2 + p88 * ((v a1 + v a0 / p44) / p44));
  pow2_plus 44 44; lemma_div_mod (v a1 + v a0 / p44) p44;
  lemma_div_mod (v a1 + v a0 / p44) p44;
  distributivity_add_right (p44) ((v a1 + v a0 / p44)%p44) (p44 * ((v a1 + v a0 / p44) / p44));
  cut (p44 * ((v a1 + v a0 / p44) % p44) + p88 * ((v a1 + v a0 / p44) / p44) =
    p44 * (v a1 + v a0 / p44) );
  distributivity_add_right (p44) (v a1) (v a0 / p44);
  lemma_div_mod (v a0) p44


#reset-options "--max_fuel 0 --z3rlimit 100"

val carry_limb_unrolled: acc:seqelem{bounds (acc) (p44+5*((p45+p20)/p42)) p44 p42} ->
  Tot (s:seqelem{bounds s p44 p44 (p42+1)
    /\ seval s = seval acc
    /\ Limb.(v (Seq.index s 2) >= p42 ==> v (Seq.index s 1) = 0)})
let carry_limb_unrolled acc =
  let a0 = Seq.index acc 0 in
  let a1 = Seq.index acc 1 in
  let a2 = Seq.index acc 2 in
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
  let s = seq_upd_3 a0' a1' a2' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 s;
  Hacl.Spec.Bignum.Modulo.lemma_seval_3 acc;
  lemma_carry_limb_unrolled a0 a1 a2;
  s


private val lemma_div: a:nat -> b:pos -> Lemma
  ((a = b ==> a / b = 1) /\ (a < b ==> a / b = 0))
private let lemma_div a b =
  if a < b then Math.Lemmas.small_division_lemma_1 a b
  else Math.Lemmas.lemma_div_mod a b


val carry_last_unrolled: s:seqelem{bounds s p44 p44 (p42+1) /\ (v (Seq.index s 2) = p42 ==> v (Seq.index s 1) = 0)} -> Tot (s':seqelem{bounds s' p44 p44 p42
  /\ seval s' % prime = seval s % prime})
let carry_last_unrolled s =
  lemma_carried_is_fine_to_carry_top s;
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s;
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s;
  lemma_div (v (Seq.index s 2)) (pow2 42);
  let s' = Hacl.Spec.Bignum.Modulo.carry_top_spec s in
  cut (v (Seq.index s' 0) >= pow2 44 ==> v (Seq.index s' 1) = 0);
  let s'' = Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec s' in
  s''


#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_last_pass_spec: acc:seqelem{red_45 acc} -> Tot (acc':seqelem{
    seval acc' = seval acc % prime
    /\ bounds acc' p44 p44 p42})
let poly1305_last_pass_spec acc =
  last_pass_is_fine acc;
  lemma_carried_is_fine_to_carry acc;
  let acc1 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc in
  cut (bounds acc1 p44 p44 (p45 + p20));
  lemma_carried_is_fine_to_carry_top acc1;
  let acc2 = Hacl.Spec.Bignum.Modulo.carry_top_spec acc1 in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec acc1;
  cut (bounds (acc2) (p44+5*((p45+p20)/p42)) p44 p42);
  let acc3 = carry_limb_unrolled acc2 in
  let acc4 = carry_last_unrolled acc3 in
  let acc5 = poly1305_last_pass_spec_ acc4 in
  acc5


#reset-options "--max_fuel 0 --z3rlimit 200"



#reset-options "--max_fuel 0 --z3rlimit 200"


#reset-options "--max_fuel 0 --z3rlimit 100"

val poly1305_finish_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word ->
  rem':U64.t{U64.v rem' = length m /\ length m < 16} ->
  key_s:Seq.seq H8.t{Seq.length key_s = 16} ->
  GTot (mac:word_16{
      (let acc = seval (MkState?.h st) in
       let r   = seval (MkState?.r st) in
       let k   = hlittle_endian key_s   in
       let m'   = hlittle_endian m + pow2 (8*length m) in
       let mac = hlittle_endian mac in
       if Seq.length m >= 1
       then mac = (((((acc + m') * r) % prime)) + k) % pow2 128
       else mac = ((((acc % prime) ) + k) % pow2 128)) })
let poly1305_finish_spec st m rem' key_s =
  let st' = if U64.(rem' =^ 0uL) then st
           else poly1305_process_last_block_spec st m rem' in
  let acc = poly1305_last_pass_spec (MkState?.h st') in
  cut (if length m >= 1
       then (seval acc = ((seval (MkState?.h st) + (hlittle_endian m + pow2 (8 * length m))) * seval (MkState?.r st)) % prime)
       else seval acc = seval (MkState?.h st) % prime);
  let k' = load128_le_spec key_s in
  let open Hacl.Bignum.Wide in
  let acc' = bignum_to_128 acc in
  let mac = acc' +%^ k' in
  cut (let acc = seval (MkState?.h st) in
       let r   = seval (MkState?.r st) in
       let k   = hlittle_endian key_s   in
       let m'   = hlittle_endian m + pow2 (8*length m) in
       let mac = v mac in
       if Seq.length m >= 1
       then mac = (((((acc + m') * r) % prime) % pow2 128) + k) % pow2 128
       else mac = ((((acc % prime) % pow2 128) + k) % pow2 128));
  Math.Lemmas.lemma_mod_plus_distr_l (((seval (MkState?.h st) + (hlittle_endian m + pow2 (8*length m))) * seval (MkState?.r st)) % prime) (hlittle_endian key_s) (pow2 128);
  Math.Lemmas.lemma_mod_plus_distr_l (seval (MkState?.h st) % prime) (hlittle_endian key_s) (pow2 128);
  let mac = store128_le_spec mac in
  cut (let acc = seval (MkState?.h st) in
       let r   = seval (MkState?.r st) in
       let k   = hlittle_endian key_s   in
       let m'   = hlittle_endian m + pow2 (8*length m) in
       let mac = hlittle_endian mac in
       if Seq.length m >= 1
       then mac = (((((acc + m') * r) % prime) % pow2 128) + k) % pow2 128
       else mac = ((((acc % prime) % pow2 128) + k) % pow2 128));
  mac



private val lemma_mod_distr: acc0:nat -> block:nat -> r0:nat -> Lemma
  (((acc0 + block) * r0) % prime = ((((acc0 % prime) + (block % prime)) % prime) * (r0 % prime)) % prime)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 5 --z3cliopt smt.arith.nl=false"
private let lemma_mod_distr acc0 block r0 =
  let open FStar.Math.Lemmas in
  lemma_mod_mul_distr_l (acc0 + block) r0 prime;
  assert (((acc0 + block) * r0) % prime = (((acc0 + block) % prime) * r0) % prime);
  lemma_mod_mul_distr_r ((acc0 + block) % prime) r0 prime;
  assert ((((acc0 + block) % prime) * r0) % prime =
    (((acc0 + block) % prime) * (r0 % prime)) % prime
  );
  lemma_mod_plus_distr_l acc0 block prime;
  assert (
    (((acc0 + block) % prime) * (r0 % prime)) % prime =
    ((((acc0 % prime) + block) % prime) * (r0 % prime)) % prime
  );
  lemma_mod_plus_distr_r (acc0 % prime) block prime


#reset-options "--max_fuel 0  --z3rlimit 100"

val poly1305_update_last_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word ->
  rem':U64.t{U64.v rem' = length m /\ length m < 16} ->
  GTot (a:seqelem{
      (let acc = selem (MkState?.h st) in
       let acc' = seval a in
       let r   = selem (MkState?.r st) in
       let m'   = (hlittle_endian m + pow2 (8*length m)) % prime in
       bounds a p44 p44 p42
       /\ (if Seq.length m >= 1
         then acc' = (((acc + m') % prime) * r) % prime
         else acc' = acc)) })
let poly1305_update_last_spec st m rem' =
  if Seq.length m >= 1 then (
    lemma_mod_distr (seval (MkState?.h st)) (hlittle_endian m + pow2 (8*length m)) (seval (MkState?.r st))
  );
  let st' = if U64.(rem' =^ 0uL) then st
           else poly1305_process_last_block_spec st m rem' in
  let acc = poly1305_last_pass_spec (MkState?.h st') in
  Math.Lemmas.modulo_lemma (seval acc) prime;
  acc


#reset-options "--max_fuel 0 --z3rlimit 100"

val poly1305_finish_spec':
  acc:seqelem{bounds acc p44 p44 p42} ->
  key_s:word_16{Seq.length key_s = 16} ->
  GTot (mac:word_16{
    let acc = seval acc in
    let k   = hlittle_endian key_s in    
    hlittle_endian mac == (acc + k) % pow2 128})
let poly1305_finish_spec' acc key_s =
  let k' = load128_le_spec key_s in
  let open Hacl.Bignum.Wide in
  let acc' = bignum_to_128 acc in
  let mac = acc' +%^ k' in
  let mac = store128_le_spec mac in
  mac
