module MPFR.Lib.Clz

open FStar.Mul
open FStar.UInt64
open FStar.UInt

open MPFR.Dyadic
open MPFR.Spec.Lib
open MPFR.Spec.Sub1
open MPFR.Spec.Round
open MPFR.Maths

open MPFR.Lib
open MPFR.Exceptions

open MPFR.Exceptions.Lemma
open MPFR.Sub1sp1.Lemma
open MPFR.Add1sp1
open MPFR.Add1sp1.Lemma


module U32 = FStar.UInt32


inline_for_extraction
val count_leading_zeros:
  a:u64{not (a=^0uL)} -> Tot (cnt:u32{U32.v cnt<32 /\ v (a<<^cnt)>=pow2 63 /\ v a*pow2 (U32.v cnt)<pow2 64 /\ U32.v cnt=64-(nbits (v a))})
