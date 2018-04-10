module Hacl.Spec.Poly1305_32

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
//open FStar.Int.Cast.Full

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

include Hacl.Spec.Poly1305_32.State

#reset-options "--z3rlimit 20 --max_fuel 0"


val lemma_bignum_to_128:
  h0:limb{v h0 < pow2 26} -> h1:limb{v h1 < pow2 26} -> h2:limb{v h2 < pow2 26} ->
  h3:limb{v h3 < pow2 26} -> h4:limb{v h4 < pow2 26} ->
  Lemma (((v h4 * pow2 8) % pow2 32 + v h3 / pow2 18) * pow2 96
          + ((v h3 * pow2 14) % pow2 32 + v h2 / pow2 12) * pow2 64
          + ((v h2 * pow2 20) % pow2 32 + v h1 / pow2 6) * pow2 32
          + ((v h1 * pow2 26) % pow2 32) + v h0
    = (v h0 + pow2 26 * v h1 + pow2 52 * v h2 + pow2 78 * v h3 + pow2 104 * v h4) % pow2 128)
let lemma_bignum_to_128 h0 h1 h2 h3 h4 =
  Hacl.Spec.Poly1305_32.Lemmas.lemma_bignum_to_128 (v h0) (v h1) (v h2) (v h3) (v h4)

#reset-options "--z3rlimit 50 --max_fuel 0 --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native"

inline_for_extraction
let shift_left_128 (h:Hacl.UInt32.t{v h < pow2 26}) (s:UInt32.t{UInt32.v s <= 78}) :
  Tot (z:Hacl.UInt128.t{Hacl.UInt128.v z = pow2 (UInt32.v s) * v h})
  = Math.Lemmas.pow2_le_compat 78 (UInt32.v s);
    Math.Lemmas.pow2_plus 78 26;
    assert(pow2 (UInt32.v s) * v h < pow2 104);
    Math.Lemmas.pow2_lt_compat 128 104;
    Math.Lemmas.small_modulo_lemma_1 (pow2 (UInt32.v s) * v h) (pow2 128);
    let z = Hacl.UInt128.(sint32_to_sint128 h <<^ s) in
    z

inline_for_extraction
let shift_left_128' (h:Hacl.UInt32.t{v h < pow2 26}) :
  Tot (z:Hacl.UInt128.t{Hacl.UInt128.v z = pow2 104 * (v h % pow2 24)})
  = Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v h) 128 104;
    Hacl.UInt128.(sint32_to_sint128 h <<^ 104ul)

inline_for_extraction
let add_limbs (h0:Hacl.UInt128.t{Hacl.UInt128.v h0 < pow2 26})
              (h1:Hacl.UInt128.t{Hacl.UInt128.v h1 % pow2 26 = 0 /\ Hacl.UInt128.v h1 < pow2 52})
              (h2:Hacl.UInt128.t{Hacl.UInt128.v h2 % pow2 52 = 0 /\ Hacl.UInt128.v h2 < pow2 78})
              (h3:Hacl.UInt128.t{Hacl.UInt128.v h3 % pow2 78 = 0 /\ Hacl.UInt128.v h3 < pow2 104})
              (h4:Hacl.UInt128.t{Hacl.UInt128.v h4 % pow2 104 = 0})
              : Tot (h:Hacl.UInt128.t{Hacl.UInt128.v h = Hacl.UInt128.v h0 + Hacl.UInt128.v h1
                                                         + Hacl.UInt128.v h2 + Hacl.UInt128.v h3
                                                         + Hacl.UInt128.v h4})
  = assert_norm(pow2 24 = 0x1000000);
    assert_norm(pow2 26 = 0x4000000);
    assert_norm(pow2 52 = 0x10000000000000);
    assert_norm(pow2 78 = 0x40000000000000000000);
    assert_norm(pow2 104 = 0x100000000000000000000000000);
    UInt.logor_disjoint (Hacl.UInt128.v h1) (Hacl.UInt128.v h0) 26;
    UInt.logor_disjoint (Hacl.UInt128.v h2) (Hacl.UInt128.v h1 + Hacl.UInt128.v h0) 52;
    UInt.logor_disjoint (Hacl.UInt128.v h3) (Hacl.UInt128.v h2 + Hacl.UInt128.v h1 + Hacl.UInt128.v h0) 78;
    UInt.logor_disjoint (Hacl.UInt128.v h4) (Hacl.UInt128.v h3 + Hacl.UInt128.v h2 + Hacl.UInt128.v h1 + Hacl.UInt128.v h0) 104;
    Hacl.UInt128.(h4 |^ (h3 |^ (h2 |^ (h1 |^ h0))))


#reset-options "--z3rlimit 20 --max_fuel 0"

val bignum_to_128: s:seqelem{bounds s p26 p26 p26 p26 p26} -> Tot (acc:Hacl.UInt128.t{Hacl.UInt128.v acc = seval s % pow2 128})
let bignum_to_128 s =
  assert_norm(pow2 24 = 0x1000000);
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  let h0 = Seq.index s 0 in
  let h1 = Seq.index s 1 in
  let h2 = Seq.index s 2 in
  let h3 = Seq.index s 3 in
  let h4 = Seq.index s 4 in
  let x0 = sint32_to_sint128 h0 in
  let x1 = shift_left_128 h1 26ul in
  let x2 = shift_left_128 h2 52ul in
  let x3 = shift_left_128 h3 78ul in
  let x4 = shift_left_128' h4 in
  let h  = add_limbs x0 x1 x2 x3 x4 in
  Hacl.Spec.Poly1305_32.Lemmas.lemma_seval_mod_128 (v h0) (v h1) (v h2) (v h3) (v h4);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  h


#reset-options "--z3rlimit 20 --max_fuel 0"

val load32_le_spec : b:bytes{Seq.length b = 4} -> GTot (r:limb{v r == hlittle_endian b})
let load32_le_spec b = lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint32_to_sint32 (UInt32.uint_to_t (hlittle_endian b))

val store32_le_spec: r:limb -> GTot (b:bytes{Seq.length b = 4 /\ v r == hlittle_endian b})
let store32_le_spec r = hlittle_bytes 4ul (v r)

val load128_le_spec : b:word_16 -> GTot (r:Hacl.UInt128.t{Hacl.UInt128.v r == hlittle_endian b})
let load128_le_spec b = lemma_little_endian_is_bounded (reveal_sbytes b);
  Hacl.Cast.uint128_to_sint128 (UInt128.uint_to_t (hlittle_endian b))

val store128_le_spec: r:Hacl.UInt128.t -> GTot (b:word_16{Hacl.UInt128.v r == hlittle_endian b})
let store128_le_spec r = hlittle_bytes 16ul (Hacl.UInt128.v r)


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

inline_for_extraction val create_5: s0:limb -> s1:limb -> s2:limb -> s3:limb -> s4:limb -> Tot (s:seqelem{
  Seq.index s 0 == s0 /\ Seq.index s 1 == s1 /\ Seq.index s 2 == s2 /\ Seq.index s 3 == s3 /\ Seq.index s 4 == s4})
inline_for_extraction let create_5 s0 s1 s2 s3 s4 =
  let s = Seq.create len limb_zero in
  let s = Seq.upd s 0 s0 in
  let s = Seq.upd s 1 s1 in
  let s = Seq.upd s 2 s2 in
  let s = Seq.upd s 3 s3 in
  let s = Seq.upd s 4 s4 in
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
val hload128: high:UInt64.t -> low:UInt64.t -> Tot (z:UInt128.t{Hacl.UInt128.v z = pow2 64 * UInt64.v high
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
let clamp_mask : cm:UInt128.t{UInt128.v cm = 0x0ffffffc0ffffffc0ffffffc0fffffff} =
  hload128 (0x0ffffffc0ffffffcuL) (0x0ffffffc0fffffffuL)


inline_for_extraction let mask_26 : m:limb{v m = pow2 26 - 1} =
  assert_norm(pow2 26 - 1 = 0x3ffffff);
  uint32_to_limb 0x3fffffful

inline_for_extraction let mask_24 : m:limb{v m = pow2 24 - 1} =
  assert_norm(pow2 24 - 1 = 0xffffff);
  uint32_to_limb 0xfffffful


val fexpand_spec: input:word_16 -> GTot (s:seqelem{bounds s p26 p26 p26 p26 p26 /\ seval s = hlittle_endian input /\ v (Seq.index s 4) < pow2 24})
let fexpand_spec input =
  let open Hacl.UInt32 in
  let i0 = load32_le_spec (Seq.slice input 0 4) in
  let i1 = load32_le_spec (Seq.slice input 3 7) in
  let i2 = load32_le_spec (Seq.slice input 6 10) in
  let i3 = load32_le_spec (Seq.slice input 9 13) in
  let i4 = load32_le_spec (Seq.slice input 12 16) in
  let output0 = (i0         ) &^ mask_26 in
  let output1 = (i1 >>^ 2ul ) &^ mask_26 in
  let output2 = (i2 >>^ 4ul ) &^ mask_26 in
  let output3 = (i3 >>^ 6ul ) &^ mask_26 in
  let output4 = (i4 >>^ 8ul) in
  UInt.logand_mask (v i0) 26;
  UInt.logand_mask (v (i1 >>^ 2ul)) 26;
  UInt.logand_mask (v (i2 >>^ 4ul)) 26;
  UInt.logand_mask (v (i3 >>^ 6ul)) 26;
  let s = create_5 output0 output1 output2 output3 output4 in
  Hacl.Spec.Poly1305_32.Lemmas.lemma_fexpand (reveal_sbytes input);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  s


#reset-options "--z3rlimit 20 --max_fuel 0 --z3refresh"

inline_for_extraction
let shift_mask (k:Hacl.UInt128.t) (x:UInt32.t{UInt32.v x < 128}) : Tot (z:Hacl.UInt32.t{v z = (Hacl.UInt128.v k / pow2 (UInt32.v x)) % pow2 26}) =
  UInt.logand_mask #32 ((Hacl.UInt128.v k / pow2 (UInt32.v x)) % pow2 32) 26;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v k / pow2 (UInt32.v x)) 26 32;
  let z = sint128_to_sint32 (Hacl.UInt128.(k >>^ x)) in
  assert(v z = Hacl.UInt128.v k / pow2 (UInt32.v x) % pow2 32);
  Limb.(z &^ mask_26)

inline_for_extraction
let shift_mask' (k:Hacl.UInt128.t) : Tot (z:Hacl.UInt32.t{v z = (Hacl.UInt128.v k) % pow2 26}) =
  UInt.logand_mask #32 ((Hacl.UInt128.v k) % pow2 32) 26;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v k) 26 32;
  let z = sint128_to_sint32 (Hacl.UInt128.(k)) in
  assert(v z = Hacl.UInt128.v k % pow2 32);
  Limb.(z &^ mask_26)


#reset-options "--z3rlimit 200 --max_fuel 0 --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native"

val poly1305_encode_r_spec: key:Seq.seq H8.t{Seq.length key = 16} -> GTot (s':seqelem{red_26 s'
  /\ seval s' = UInt.logand #128 (hlittle_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff})
let poly1305_encode_r_spec key =
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  let k = load128_le_spec key in
  let k_clamped = Hacl.UInt128.(k &^ clamp_mask) in
  let r0 = shift_mask' k_clamped in
  let r1 = shift_mask k_clamped 26ul in
  let r2 = shift_mask k_clamped 52ul in
  let r3 = shift_mask k_clamped 78ul in
  let r4 = shift_mask k_clamped 104ul in
  Math.Lemmas.lemma_div_lt (Hacl.UInt128.v k_clamped) 128 104;
  Math.Lemmas.pow2_le_compat 26 24;
  Math.Lemmas.small_modulo_lemma_1 (Hacl.UInt128.v k_clamped / pow2 104) (pow2 26);
  Hacl.Spec.Poly1305_32.Lemmas.lemma_k (Hacl.UInt128.v k_clamped);
  assert(Hacl.UInt128.v k_clamped = ((Hacl.UInt128.v k_clamped) % pow2 26)
                                    + pow2 26 * ((Hacl.UInt128.v k_clamped / pow2 26) % pow2 26)
                                    + pow2 52 * ((Hacl.UInt128.v k_clamped / pow2 52) % pow2 26)
                                    + pow2 78 * ((Hacl.UInt128.v k_clamped / pow2 78) % pow2 26)
                                    + pow2 104 * ((Hacl.UInt128.v k_clamped / pow2 104)));
  assert(v r0 = (Hacl.UInt128.v k_clamped) % pow2 26);
  assert(v r1 = ((Hacl.UInt128.v k_clamped / pow2 26) % pow2 26));
  assert(v r2 = ((Hacl.UInt128.v k_clamped / pow2 52) % pow2 26));
  assert(v r3 = ((Hacl.UInt128.v k_clamped / pow2 78) % pow2 26));
  assert(v r4 = ((Hacl.UInt128.v k_clamped / pow2 104)));
  assert(Hacl.UInt128.v k_clamped = v r0
                                    + pow2 26 * v r1
                                    + pow2 52 * v r2
                                    + pow2 78 * v r3
                                    + pow2 104 * v r4);
  let s = create_5 r0 r1 r2 r3 r4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  s


#reset-options "--z3rlimit 50 --max_fuel 0"

val toField_plus_2_128_spec: m:word_16 -> GTot (s:seqelem{red_26 s /\ seval s = hlittle_endian m + pow2 128})
let toField_plus_2_128_spec m =
  let b  = fexpand_spec m in
  let b4 = Seq.index b 4 in
  cut (v b4 < pow2 24);
  let open Hacl.Bignum.Limb in
  assert_norm (pow2 24 = 0x1000000);
  assert_norm (0 = 0x1000000 % pow2 24);
  UInt.logor_disjoint (0x1000000) (v b4) 24;
  assert_norm (pow2 24 + pow2 24 < pow2 26);
  let b4' = uint32_to_limb 0x1000000ul |^ b4 in
  let m' = Seq.upd b 4 b4' in
  cut (Seq.index m' 0 == Seq.index b 0 /\ Seq.index m' 1 == Seq.index b 1
     /\ Seq.index m' 2 == Seq.index b 2
     /\ Seq.index m' 3 == Seq.index b 3
     /\ v (Seq.index m' 4) = v (Seq.index b 4) + pow2 24);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 m';
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 b;
  Math.Lemmas.distributivity_add_right (pow2 104) (v (Seq.index b 4)) (pow2 24);
  Math.Lemmas.pow2_plus 104 24;
  m'


#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_start_spec: unit -> Tot (s:seqelem{Seq.index s 0 == limb_zero /\ Seq.index s 1 == limb_zero /\ Seq.index s 2 == limb_zero /\ Seq.index s 3 == limb_zero /\  Seq.index s 4 == limb_zero /\   selem s = 0 /\ red_y s /\ seval s = 0})
let poly1305_start_spec () =
  let s = Seq.create len limb_zero in
  lemma_seval_def (s) 5;
  lemma_seval_def (s) 4;
  lemma_seval_def (s) 3;
  lemma_seval_def (s) 2;
  lemma_seval_def (s) 1;
  lemma_seval_def (s) 0;
  s


#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 16} ->
  GTot (st:poly1305_state_{red_26 (MkState?.r st) /\ red_y (MkState?.h st)
    /\ seval (MkState?.r st) = UInt.logand #128 (hlittle_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff
    /\ seval (MkState?.h st) = 0})
let poly1305_init_spec key =
  let r = poly1305_encode_r_spec key in
  let h = poly1305_start_spec () in
  MkState r h (Seq.createEmpty)


val poly1305_update_spec: st:poly1305_state_{red_26 (MkState?.r st) /\ red_y (MkState?.h st)} ->
  m:word_16 ->
  GTot (st':poly1305_state_{red_26 (MkState?.r st') /\ red_y (MkState?.h st')
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
  st:poly1305_state_{red_26 (MkState?.r st) /\ red_y (MkState?.h st)} ->
  m:Seq.seq H8.t ->
  rem':U64.t{U64.v rem' = Seq.length m /\ U64.v rem' < 16} ->
  GTot (st':poly1305_state_{red_26 (MkState?.r st') /\ red_y (MkState?.h st')
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
  let block  = fexpand_spec m'' in
  let acc = MkState?.h st in
  let r = MkState?.r st in
  let log = Seq.append (Seq.create 1 (reveal_sbytes m)) (MkState?.log st) in
  let acc' = add_and_multiply_tot acc block r in
  MkState r acc' log


#reset-options "--max_fuel 0"

inline_for_extraction let p26m5 : p:limb{v p = pow2 26 - 5} =
  assert_norm(pow2 26 - 5 = 0x3fffffb); uint32_to_sint32 0x3fffffbul

inline_for_extraction let p26m1 : p:limb{v p = pow2 26 - 1} =
  assert_norm(pow2 26 - 1 = 0x3ffffff); uint32_to_sint32 0x3fffffful


#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_poly_last_pass: s:seqelem{bounds s p26 p26 p26 p26 p26} -> Lemma
  (requires (bounds s p26 p26 p26 p26 p26 /\
    (let a0' = Seq.index s 0 in let a1' = Seq.index s 1 in let a2' = Seq.index s 2 in
     let a3' = Seq.index s 3 in let a4' = Seq.index s 4 in
     (v a0' <= 4 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0)
     \/ (v a0' < pow2 26 - 5 \/ v a1' <> pow2 26 - 1 \/ v a2' <> pow2 26 - 1  \/ v a3' <> pow2 26 - 1  \/ v a4' <> pow2 26 - 1) )))
  (ensures (seval s = seval s % prime))
let lemma_poly_last_pass s =
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  assert_norm(pow2 26 = 0x4000000); assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000); assert_norm(pow2 104 = 0x100000000000000000000000000);
  assert_norm(pow2 26 - 5 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
              + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1) = pow2 130 - 5);
  let a0' = Seq.index s 0 in let a1' = Seq.index s 1 in let a2' = Seq.index s 2 in
  let a3' = Seq.index s 3 in let a4' = Seq.index s 4 in
  if v a0' <= 4 && v a1' = 0 && v a2' = 0 && v a3' = 0 && v a4' = 0 then Math.Lemmas.modulo_lemma (seval s) prime
  else (
    assert (v a0' + pow2 26 * v a1' + pow2 52 * v a2' + pow2 78 * v a3' + pow2 104 * v a4' < pow2 26 - 5 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
              + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1));
    Math.Lemmas.modulo_lemma (seval s) prime)

val lemma_poly_last_pass': a0:limb -> a1:limb -> a2:limb -> a3:limb -> a4:limb -> Lemma
  (requires (let open Hacl.Bignum.Limb in
    v a0 >= pow2 26 - 5 /\ v a1 = pow2 26 - 1 /\ v a2 = pow2 26 - 1 /\ v a3 = pow2 26 - 1 /\ v a4 = pow2 26 - 1))
  (ensures (let open Hacl.Bignum.Limb in
    (v a0 - (pow2 26 - 5) + pow2 26 * (v a1 - (pow2 26 - 1)) + pow2 52 * (v a2 - (pow2 26 - 1)) + pow2 78 * (v a3 - (pow2 26 - 1)) + pow2 104 * (v a4 - (pow2 26 - 1))) % prime
    = (v a0 + pow2 26 * (v a1) + pow2 52 * (v a2) + pow2 78 * v a3 + pow2 104 * v a4) % prime))
let lemma_poly_last_pass' a0 a1 a2 a3 a4 =
  assert_norm(pow2 130 - 5 = 0x3fffffffffffffffffffffffffffffffb);
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  Math.Lemmas.distributivity_add_right (pow2  26) (v a1) (pow2 26 - 1);
  Math.Lemmas.distributivity_add_right (pow2  52) (v a2) (pow2 26 - 1);
  Math.Lemmas.distributivity_add_right (pow2  78) (v a3) (pow2 26 - 1);
  Math.Lemmas.distributivity_add_right (pow2 104) (v a4) (pow2 26 - 1);
  assert_norm(pow2 26 - 5 + pow2 26 * (pow2 26 - 1) + pow2 52 * (pow2 26 - 1)
              + pow2 78 * (pow2 26 - 1) + pow2 104 * (pow2 26 - 1)
              = pow2 130 - 5);
  Math.Lemmas.lemma_mod_plus (v a0 + pow2 26 * (v a1) + pow2 52 * (v a2) + pow2 78 * v a3 + pow2 104 * v a4) 1 prime

val lemma_poly_last_pass'': a0:limb -> a1:limb -> a2:limb -> a3:limb -> a4:limb -> Lemma
  (requires (true))
  (ensures (let open Hacl.Bignum.Limb in
    (v a0 >= pow2 26 - 5 /\ v a1 = pow2 26 - 1 /\ v a2 = pow2 26 - 1 /\ v a3 = pow2 26 - 1 /\ v a4 = pow2 26 - 1) ==>
    ((v a0 - (pow2 26 - 5) + pow2 26 * (v a1 - (pow2 26 - 1)) + pow2 52 * (v a2 - (pow2 26 - 1)) + pow2 78 * (v a3 - (pow2 26 - 1)) + pow2 104 * (v a4 - (pow2 26 - 1))) % prime
    = (v a0 + pow2 26 * (v a1) + pow2 52 * (v a2) + pow2 78 * (v a3) + pow2 104 * (v a4)) % prime)))
let lemma_poly_last_pass'' a0 a1 a2 a3 a4 =
  if (v a0 >= pow2 26 - 5 && v a1 = pow2 26 - 1 && v a2 = pow2 26 - 1 && v a3 = pow2 26 - 1 && v a4 = pow2 26 - 1)
  then lemma_poly_last_pass' a0 a1 a2 a3 a4


#reset-options "--max_fuel 0 --z3rlimit 100"

val poly1305_last_pass_spec_: acc:seqelem{bounds acc p26 p26 p26 p26 p26} -> Tot (acc':seqelem{
  bounds acc' p26 p26 p26 p26 p26 /\  seval acc' = seval acc % prime})
let poly1305_last_pass_spec_ acc =
  let a0 = Seq.index acc 0 in
  let a1 = Seq.index acc 1 in
  let a2 = Seq.index acc 2 in
  let a3 = Seq.index acc 3 in
  let a4 = Seq.index acc 4 in
  let open Hacl.Bignum.Limb in
  let mask0 = gte_mask a0 p26m5 in
  let mask1 = eq_mask  a1 p26m1 in
  let mask2 = eq_mask  a2 p26m1 in
  let mask3 = eq_mask  a3 p26m1 in
  let mask4 = eq_mask  a4 p26m1 in
  let mask  = mask0 &^ mask1 &^ mask2 &^ mask3 &^ mask4 in
  UInt.logand_lemma_1 (v mask0); UInt.logand_lemma_1 (v mask1); UInt.logand_lemma_1 (v mask2);
  UInt.logand_lemma_1 (v mask3); UInt.logand_lemma_1 (v mask4);
  UInt.logand_lemma_2 (v mask0); UInt.logand_lemma_2 (v mask1); UInt.logand_lemma_2 (v mask2);
  UInt.logand_lemma_2 (v mask3); UInt.logand_lemma_2 (v mask4);
  UInt.logand_associative (v mask0) (v mask1) (v mask2);
  cut (v mask = UInt.ones 64 ==> (v a0 >= pow2 26 - 5 /\ v a1 = pow2 26 - 1 /\ v a2 = pow2 26 - 1 /\ v a3 = pow2 26 - 1 /\ v a4 = pow2 26 - 1));
  UInt.logand_lemma_1 (v p26m5); UInt.logand_lemma_1 (v p26m1); UInt.logand_lemma_1 (v p26m1);
  UInt.logand_lemma_2 (v p26m5); UInt.logand_lemma_2 (v p26m1); UInt.logand_lemma_2 (v p26m1);
  let a0' = a0 -^ (p26m5 &^ mask) in
  let a1' = a1 -^ (p26m1 &^ mask) in
  let a2' = a2 -^ (p26m1 &^ mask) in
  let a3' = a3 -^ (p26m1 &^ mask) in
  let a4' = a4 -^ (p26m1 &^ mask) in
  cut ( (v a0 >= pow2 26 - 5 /\ v a1 = pow2 26 - 1 /\ v a2 = pow2 26 - 1 /\ v a3 = pow2 26 - 1 /\ v a4 = pow2 26 - 1) ==> (v a0' <= 4 /\ v a1' = 0 /\ v a2' = 0 /\ v a3' = 0 /\ v a4' = 0) );
  cut ( (v a0 < pow2 26 - 5 \/ v a1 <> pow2 26 - 1 \/ v a2 <> pow2 26 - 1 \/ v a3 <> pow2 26 - 1 \/ v a4 <> pow2 26 - 1) ==> (v a0' = v a0 /\ v a1' = v a1 /\ v a2' = v a2 /\ v a3' = v a3 /\ v a4' = v a4) );
  let acc' = create_5 a0' a1' a2' a3' a4' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 acc';
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 acc;
  lemma_poly_last_pass acc';
  lemma_poly_last_pass'' a0 a1 a2 a3 a4;
  cut (bounds acc' p26 p26 p26 p26 p26);
  Math.Lemmas.modulo_lemma (seval acc') prime;
  acc'


#reset-options "--max_fuel 0 --z3rlimit 100"

private val lemma_carry_local: x:nat -> y:nat -> n:nat -> Lemma
  (pow2 n * x + pow2 (n+26) * y = pow2 n * (x % (pow2 26)) + pow2 (n+26) * ((x / pow2 26) + y))
private let lemma_carry_local x y n =
  Math.Lemmas.lemma_div_mod x (pow2 26);
  Math.Lemmas.pow2_plus n 26;
  Math.Lemmas.distributivity_add_right (pow2 n) (pow2 26 * (x / pow2 26)) (x % pow2 26);
  Math.Lemmas.distributivity_add_right (pow2 (n + 26)) (x / pow2 26) y


val fcontract_first_carry_pass: input:seqelem{red_y input} ->
  GTot (s':seqelem{bounds s' p26 p26 p26 p26 (pow2 32) /\ seval s' = seval input})
let fcontract_first_carry_pass s =
  let open Hacl.UInt32 in
  assert_norm(pow2 26 + pow2 13 = 0x4002000);
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  let t1' = t1 +^ (t0 >>^ 26ul) in
  let t0' = t0 &^ mask_26 in
  UInt.logand_mask (v t0) 26;
  lemma_carry_local (v t0) (v t1) 0;
  cut (v t0' + pow2 26 * v t1' + pow2 52 * v t2 + pow2 78 * v t3 + pow2 104 * v t4 = Hacl.Spec.Bignum.Bigint.seval s);
  let t2' = t2 +^ (t1' >>^ 26ul) in
  let t1'' = t1' &^ mask_26 in
  UInt.logand_mask (v t1') 26;
  lemma_carry_local (v t1') (v t2) 26;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2' + pow2 78 * v t3 + pow2 104 * v t4
       = v t0' + pow2 26 * v t1' + pow2 52 * v t2 + pow2 78 * v t3 + pow2 104 * v t4);
  let t3' = t3 +^ (t2' >>^ 26ul) in
  let t2'' = t2' &^ mask_26 in
  UInt.logand_mask (v t2') 26;
  lemma_carry_local (v t2') (v t3) 52;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78 * v t3' + pow2 104 * v t4
       = v t0' + pow2 26 * v t1'' + pow2 52 * v t2' + pow2 78 * v t3 + pow2 104 * v t4);
  let t4' = t4 +^ (t3' >>^ 26ul) in
  let t3'' = t3' &^ mask_26 in
  UInt.logand_mask (v t3') 26;
  lemma_carry_local (v t3') (v t4) 78;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78 * v t3' + pow2 104 * v t4
       = v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78 * v t3'' + pow2 104 * v t4');
  let s' = create_5 t0' t1'' t2'' t3'' t4' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  s'


val fcontract_first_carry_full: input:seqelem{red_y input} ->
  GTot (s':seqelem{bounds s' (pow2 27) p26 p26 p26 p26
    /\ selem s' = selem input})
let fcontract_first_carry_full s =
  let s' = fcontract_first_carry_pass s in
  assert_norm(5 * (pow2 32 / pow2 26) + pow2 26 < pow2 27);
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s';
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s';
  let s'' = Hacl.Spec.Bignum.Modulo.carry_top_spec s' in
  s''


private let lemma_div_26 (a:nat{a <= pow2 26}) : Lemma (a / pow2 26 = 1 ==> (a = pow2 26 /\ a % pow2 26 = 0)) = assert_norm((pow2 26 - 1) / pow2 26 = 0); assert_norm(pow2 26 % pow2 26 = 0)

val fcontract_second_carry_pass: input:seqelem{bounds input (pow2 27) p26 p26 p26 p26} ->
  GTot (s':seqelem{bounds s' p26 p26 p26 p26 (p26 + 1)
    /\ (v (Seq.index s' 4) = p26 ==> v (Seq.index s' 1) < 2) /\ seval s' = seval input})
let fcontract_second_carry_pass s =
  let open Hacl.UInt32 in
  assert_norm(pow2 26 = 0x4000000);
  assert_norm(pow2 27 = 0x8000000);
  assert_norm(pow2 52 = 0x10000000000000);
  assert_norm(pow2 78 = 0x40000000000000000000);
  assert_norm(pow2 104 = 0x100000000000000000000000000);
  assert_norm(pow2 0 = 1);
  let t0 = Seq.index s 0 in
  let t1 = Seq.index s 1 in
  let t2 = Seq.index s 2 in
  let t3 = Seq.index s 3 in
  let t4 = Seq.index s 4 in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s;
  let t1' = t1 +^ (t0 >>^ 26ul) in
  assert_norm((pow2 27 - 1) / pow2 26 = 1);
  lemma_div_26 (v t1');
  let t0' = t0 &^ mask_26 in
  UInt.logand_mask (v t0) 26;
  lemma_carry_local (v t0) (v t1) 0;
  cut (v t0' + pow2 26 * v t1' + pow2 52 * v t2 + pow2 78 * v t3 + pow2 104 * v t4 = Hacl.Spec.Bignum.Bigint.seval s);
  let t2' = t2 +^ (t1' >>^ 26ul) in
  lemma_div_26 (v t2');
  let t1'' = t1' &^ mask_26 in
  UInt.logand_mask (v t1') 26;
  lemma_carry_local (v t1') (v t2) 26;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2' + pow2 78 * v t3 + pow2 104 * v t4
       = v t0' + pow2 26 * v t1' + pow2 52 * v t2 + pow2 78 * v t3 + pow2 104 * v t4);
  let t3' = t3 +^ (t2' >>^ 26ul) in
  lemma_div_26 (v t3');
  let t2'' = t2' &^ mask_26 in
  UInt.logand_mask (v t2') 26;
  lemma_carry_local (v t2') (v t3) 52;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78 * v t3' + pow2 104 * v t4
       = v t0' + pow2 26 * v t1'' + pow2 52 * v t2' + pow2 78 * v t3 + pow2 104 * v t4);
  let t4' = t4 +^ (t3' >>^ 26ul) in
  lemma_div_26 (v t4');
  let t3'' = t3' &^ mask_26 in
  UInt.logand_mask (v t3') 26;
  lemma_carry_local (v t3') (v t4) 78;
  cut (v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78 * v t3' + pow2 104 * v t4
       = v t0' + pow2 26 * v t1'' + pow2 52 * v t2'' + pow2 78  * v t3'' + pow2 104 * v t4');
  let s' = create_5 t0' t1'' t2'' t3'' t4' in
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 s';
  s'


val fcontract_second_carry_full: input:seqelem{bounds input (pow2 27) p26 p26 p26 p26} ->
  GTot (s':seqelem{bounds s' p26 p26 p26 p26 p26 /\ selem s' = selem input})
let fcontract_second_carry_full input =
  let s' = fcontract_second_carry_pass input in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec_ s';
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec s';
  let s'' = Hacl.Spec.Bignum.Modulo.carry_top_spec s' in
  Hacl.Spec.Bignum.Fproduct.carry_0_to_1_spec s''

#reset-options "--max_fuel 0 --z3rlimit 20"

val poly1305_last_pass_spec: acc:seqelem{red_y acc} -> GTot (acc':seqelem{
    seval acc' = seval acc % prime
    /\ bounds acc' p26 p26 p26 p26 p26})
let poly1305_last_pass_spec acc =
  last_pass_is_fine acc;
  lemma_carried_is_fine_to_carry acc;
  let acc1 = Hacl.Spec.Bignum.Fproduct.carry_limb_spec acc in
  assert (bounds acc1 p26 p26 p26 p26 (py + p6));
  lemma_carried_is_fine_to_carry_top acc1;
  let acc2 = Hacl.Spec.Bignum.Modulo.carry_top_spec acc1 in
  Hacl.Spec.Bignum.Modulo.lemma_carry_top_spec acc1;
  assert_norm(p26+5*((py+p6)/p26) < pow2 27);
  let acc3 = fcontract_first_carry_full acc2 in
  let acc4 = fcontract_second_carry_full acc3 in
  let acc5 = poly1305_last_pass_spec_ acc4 in
  acc5


#reset-options "--max_fuel 0 --z3rlimit 200"

val poly1305_finish_spec:
  st:poly1305_state_{red_26 (MkState?.r st) /\ red_y (MkState?.h st)} ->
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
  let open Hacl.UInt128 in
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
private let lemma_mod_distr acc block r0 =
  let open FStar.Math.Lemmas in
  lemma_mod_mul_distr_l (acc + block) r0 prime;
  lemma_mod_mul_distr_l r0 ((acc + block) % prime) prime;
  lemma_mod_plus_distr_l acc block prime;
  lemma_mod_plus_distr_l block (acc % prime) prime


#reset-options "--max_fuel 0  --z3rlimit 100"

val poly1305_update_last_spec:
  st:poly1305_state_{red_26 (MkState?.r st) /\ red_y (MkState?.h st)} ->
  m:word ->
  rem':U64.t{U64.v rem' = length m /\ length m < 16} ->
  GTot (a:seqelem{
      (let acc = selem (MkState?.h st) in
       let acc' = seval a in
       let r   = selem (MkState?.r st) in
       let m'   = (hlittle_endian m + pow2 (8*length m)) % prime in
       bounds a p26 p26 p26 p26 p26
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
  acc:seqelem{bounds acc p26 p26 p26 p26 p26} ->
  key_s:word_16{Seq.length key_s = 16} ->
  GTot (mac:word_16{
    let acc = seval acc in
    let k   = hlittle_endian key_s in
    hlittle_endian mac == (acc + k) % pow2 128})
let poly1305_finish_spec' acc key_s =
  let k' = load128_le_spec key_s in
  let open Hacl.UInt128 in
  let acc' = bignum_to_128 acc in
  let mac = acc' +%^ k' in
  let mac = store128_le_spec mac in
  mac
