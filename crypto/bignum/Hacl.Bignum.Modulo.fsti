module Hacl.Bignum.Modulo


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32


type seqelem = s:Seq.seq limb{Seq.length s = len}
type seqelem_wide = s:Seq.seq wide{Seq.length s = len}

val add_zero_pre: seqelem -> GTot Type0

val add_zero_spec: s:seqelem{add_zero_pre s} -> Tot seqelem

val add_zero:
  b:felem ->
  Stack unit
    (requires (fun h -> live h b /\ add_zero_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ add_zero_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == add_zero_spec (as_seq h0 b)
      /\ eval h1 b % prime = eval h0 b % prime))

val shift_reduce_pre: seqelem -> GTot Type0


val shift_reduced_spec: s:seqelem{shift_reduce_pre s} -> Tot seqelem


val shift_reduce:
  b:felem ->
  Stack unit
    (requires (fun h -> live h b /\ shift_reduce_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ shift_reduce_pre (as_seq h0 b) /\ modifies_1 b h0 h1 /\ live h1 b
      /\ as_seq h1 b == shift_reduced_spec (as_seq h0 b)))


val carry_top_pre: seqelem -> GTot Type0

val carry_top_spec: s:seqelem{carry_top_pre s} -> Tot seqelem


val carry_top:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ carry_top_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ carry_top_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == carry_top_spec (as_seq h0 b)))


val reduce_pre: seqelem -> GTot Type0

val reduce_spec: s:seqelem{reduce_pre s} -> Tot seqelem


val reduce:
  b:felem ->
  Stack unit
  (requires (fun h -> live h b /\ reduce_pre (as_seq h b)))
  (ensures (fun h0 _ h1 -> live h0 b /\ reduce_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
    /\ as_seq h1 b == reduce_spec (as_seq h0 b)))

val reduce_wide_pre: seqelem_wide -> GTot Type0

val reduce_wide_spec: s:seqelem_wide{reduce_wide_pre s} -> Tot seqelem_wide

val reduce_wide:
  b:felem_wide ->
  Stack unit
    (requires (fun h -> live h b /\ reduce_wide_pre (as_seq h b)))
    (ensures (fun h0 _ h1 -> live h0 b /\ reduce_wide_pre (as_seq h0 b) /\ live h1 b /\ modifies_1 b h0 h1
      /\ as_seq h1 b == reduce_wide_spec (as_seq h0 b)))
