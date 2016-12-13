module Hacl.Bignum.Modulo.Spec


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

val add_zero_pre: seqelem -> GTot Type0

val add_zero_spec: s:seqelem{add_zero_pre s} -> Tot seqelem

val carry_top_pre: seqelem -> GTot Type0

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem

val reduce_pre: seqelem -> GTot Type0

val reduce_spec: s:seqelem{reduce_pre s} -> Tot seqelem

val carry_top_wide_pre: seqelem_wide -> GTot Type0

val carry_top_wide_spec: s:seqelem_wide{carry_top_wide_pre s} -> Tot seqelem_wide
