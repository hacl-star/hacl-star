module Hacl.Bignum.Parameters

open FStar.HyperStack
open FStar.Buffer

(** The values of the prime for modular arithmetic **)
val prime: pos

(** Size of a word on the platform (32 or 64bits) **)
val word_size: ws:pos{ws = 32 \/ ws = 64}

(** Concrete platform word with side-channel protection **)
inline_for_extraction let limb = if word_size = 32 then Hacl.UInt32.t else Hacl.UInt64.t
inline_for_extraction let wide = if word_size = 32 then Hacl.UInt64.t else Hacl.UInt128.t
inline_for_extraction let ctr  = FStar.UInt32.t


val v: limb -> GTot nat
val w: wide -> GTot nat


(** Number of limbs of a bigint **)
val len: pos
inline_for_extraction val clen: l:FStar.UInt32.t{FStar.UInt32.v l = len}

type felem = b:buffer limb{length b = len}
type felem_wide = b:buffer wide{length b = len}


(** Associates a weight in bits to each limb of the bigint *)
(* val template: idx:nat{idx < len} -> Tot pos *)
(* val ctemplate: *)
(*   idx:FStar.UInt32.t{FStar.UInt32.v idx < len} -> *)
(*   Tot (x:FStar.UInt32.t{template (FStar.UInt32.v idx) = FStar.UInt32.v x}) *)
val limb_size: pos
inline_for_extraction val climb_size: l:FStar.UInt32.t{limb_size = FStar.UInt32.v l}

(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reduced_after_mul: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_l: h:mem -> b:felem -> GTot Type0
val reduced_before_mul_r: h:mem -> b:felem -> GTot Type0
val reduced_wide: h:mem -> b:felem_wide -> GTot Type0

(** Predicate associated to 'workable' bigintegers, restored after each bigint computation **)
val reducible: h:mem -> b:felem -> GTot Type0
