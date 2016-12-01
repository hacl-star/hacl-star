module Hacl.Bignum.Modulo


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32


val shift_reduce:
  b:felem ->
  i:ctr{U32.v i < len} ->
  Stack unit
    (requires (fun h -> live h b /\ reduced h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ reduced h1 b /\ modifies_1 b h0 h1 /\ live h1 b
      /\ eval h1 b % prime = eval h0 b * (template (U32.v i)) % prime))

val add_zero:
  b:felem ->
  Stack unit
    (requires (fun h -> live h b /\ reduced h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
      /\ eval h1 b % prime = eval h0 b % prime
      (* TODO: more fine grained condition or do an extra reduction step *)
    ))

val carry_top:
  b:felem ->
  Stack unit
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

val reduce:
  b:felem ->
  Stack unit
  (requires (fun h -> true))
  (ensures (fun _ _ _ -> true))

val reduce_wide:
  b:felem_wide ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun _ _ _ -> true))
