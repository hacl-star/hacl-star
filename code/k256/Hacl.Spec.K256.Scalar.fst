module Hacl.Spec.K256.Scalar

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module SD = Hacl.Spec.Bignum.Definitions

module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let qelem4 = uint64 & uint64 & uint64 & uint64

noextract
let qas_nat4 (f:qelem4) =
  let (f0, f1, f2, f3) = f in
  v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192


val qas_nat4_is_qas_nat (f:lseq uint64 4) :
  Lemma (SD.bn_v f == qas_nat4 (f.[0], f.[1], f.[2], f.[3]))
let qas_nat4_is_qas_nat f =
  SD.bn_eval_unfold_i f 4;
  SD.bn_eval_unfold_i f 3;
  SD.bn_eval_unfold_i f 2;
  SD.bn_eval_unfold_i f 1;
  SD.bn_eval0 f


inline_for_extraction noextract
let is_qelem_zero_vartime4 ((f0,f1,f2,f3): qelem4) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 f0 =. 0uL &&
  u64_to_UInt64 f1 =. 0uL &&
  u64_to_UInt64 f2 =. 0uL &&
  u64_to_UInt64 f3 =. 0uL


inline_for_extraction noextract
let is_qelem_lt_q_vartime4 ((a0,a1,a2,a3): qelem4) : bool =
  let open Lib.RawIntTypes in
  if u64_to_UInt64 a3 <. 0xffffffffffffffffuL then true
  else begin
    if u64_to_UInt64 a2 <. 0xfffffffffffffffeuL then true
    else begin
      if u64_to_UInt64 a2 >. 0xfffffffffffffffeuL then false
      else begin
        if u64_to_UInt64 a1 <. 0xbaaedce6af48a03buL then true
        else begin
          if u64_to_UInt64 a1 >. 0xbaaedce6af48a03buL then false
          else u64_to_UInt64 a0 <. 0xbfd25e8cd0364141uL
        end
      end
    end
  end


inline_for_extraction noextract
let is_qelem_eq_vartime4 ((a0,a1,a2,a3): qelem4) ((b0,b1,b2,b3): qelem4) : bool =
  let open Lib.RawIntTypes in
  u64_to_UInt64 a0 =. u64_to_UInt64 b0 &&
  u64_to_UInt64 a1 =. u64_to_UInt64 b1 &&
  u64_to_UInt64 a2 =. u64_to_UInt64 b2 &&
  u64_to_UInt64 a3 =. u64_to_UInt64 b3


val qas_nat4_inj (f1 f2:qelem4) : Lemma
  (requires qas_nat4 f1 = qas_nat4 f2)
  (ensures
   (let (a0,a1,a2,a3) = f1 in
    let (b0,b1,b2,b3) = f2 in
    a0 == b0 /\ a1 == b1 /\ a2 == b2 /\ a3 == b3))

let qas_nat4_inj f1 f2 =
  let (a0,a1,a2,a3) = f1 in
  let (b0,b1,b2,b3) = f2 in
  let bf1 = create4 a0 a1 a2 a3 in
  let bf2 = create4 b0 b1 b2 b3 in
  qas_nat4_is_qas_nat bf1;
  qas_nat4_is_qas_nat bf2;
  SD.bn_eval_inj 4 bf1 bf2


#push-options "--ifuel 1"
val is_qelem_zero_vartime4_lemma: f:qelem4 ->
  Lemma (is_qelem_zero_vartime4 f == (qas_nat4 f = 0))
let is_qelem_zero_vartime4_lemma f = ()

val is_qelem_lt_q_vartime4_lemma: f:qelem4 ->
  Lemma (is_qelem_lt_q_vartime4 f == (qas_nat4 f < S.q))

let is_qelem_lt_q_vartime4_lemma f =
  assert_norm (0xbfd25e8cd0364141 + 0xbaaedce6af48a03b * pow2 64 +
    0xfffffffffffffffe * pow2 128 + 0xffffffffffffffff * pow2 192 = S.q)

val is_qelem_eq_vartime4_lemma: f1:qelem4 -> f2:qelem4 ->
  Lemma (is_qelem_eq_vartime4 f1 f2 == (qas_nat4 f1 = qas_nat4 f2))
let is_qelem_eq_vartime4_lemma f1 f2 =
  if qas_nat4 f1 = qas_nat4 f2 then qas_nat4_inj f1 f2
#pop-options
