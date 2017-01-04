module Hacl.Spec.Bignum.Crecip


open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


val crecip_pre: s:seqelem -> GTot Type

val crecip_tot: s:seqelem{crecip_pre s} -> Tot (s':seqelem{crecip_pre s'})
