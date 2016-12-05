module Hacl.Bignum.Bigint


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Bignum.Wide

module U32 = FStar.UInt32

val bitweight: n:nat{n < len} -> Tot nat
let rec bitweight n = if n = 0 then 0 else limb_size + bitweight (n- 1)


val eval_: h:mem -> b:felem{live h b} -> i:nat{i <= len} -> GTot nat
let rec eval_ h b i =
  if i = 0 then 0
  else pow2 (limb_size * (i - 1)) * Hacl.Bignum.Limb.v (get h b (i - 1)) + eval_ h b (i-1)
(* let rec eval_ h b i = *)
(*   if i = 0 then 0 *)
(*   else pow2 (bitweight (i - 1)) * Hacl.Bignum.Limb.v (get h b (i - 1)) + eval_ h b (i-1) *)


val eval: h:mem -> b:felem{live h b} -> GTot nat
let eval h b = eval_ h b len


val eval_wide_: h:mem -> b:felem_wide{live h b} -> i:nat{i <= len} -> GTot nat
let rec eval_wide_ h b i =
  if i = 0 then 0
  else pow2 (limb_size * (i - 1)) * Hacl.Bignum.Wide.v (get h b (i-1)) + eval_wide_ h b (i-1)


val eval_wide: h:mem -> b:felem_wide{live h b} -> GTot nat
let eval_wide h b = eval_wide_ h b len
