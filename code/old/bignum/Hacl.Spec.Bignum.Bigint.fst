module Hacl.Spec.Bignum.Bigint

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Constants
open Hacl.Spec.Bignum.Field
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Bignum.Wide

module U32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 50"

val bitweight: n:nat{n < len} -> Tot nat
let rec bitweight n = if n = 0 then 0 else limb_size + bitweight (n- 1)


val eval_: h:mem -> b:felem{live h b} -> i:nat{i <= len} -> GTot nat
let rec eval_ h b i =
  if i = 0 then 0
  else pow2 (limb_size * (i - 1)) * Hacl.Bignum.Limb.v (get h b (i - 1)) + eval_ h b (i-1)


val eval: h:mem -> b:felem{live h b} -> GTot nat
let eval h b = eval_ h b len

let get_elem h b = eval h b % prime

val eval_wide_: h:mem -> b:felem_wide{live h b} -> i:nat{i <= len} -> GTot nat
let rec eval_wide_ h b i =
  if i = 0 then 0
  else pow2 (limb_size * (i - 1)) * Hacl.Bignum.Wide.v (get h b (i-1)) + eval_wide_ h b (i-1)


val eval_wide: h:mem -> b:felem_wide{live h b} -> GTot nat
let eval_wide h b = eval_wide_ h b len


val seval_: b:seqelem -> i:nat{i <= len} -> GTot nat
let rec seval_ b i =
  if i = 0 then 0 else pow2 (limb_size * (i-1)) * Hacl.Bignum.Limb.v (Seq.index b (i-1)) + seval_ b (i-1)

val seval: b:seqelem -> GTot nat
let seval b = seval_ b len


val seval_wide_: b:seqelem_wide -> i:nat{i <= len} -> GTot nat
let rec seval_wide_ b i =
  if i = 0 then 0 else pow2 (limb_size * (i-1)) * Hacl.Bignum.Wide.v (Seq.index b (i-1)) + seval_wide_ b (i-1)

val seval_wide: b:seqelem_wide -> GTot nat
let seval_wide b = seval_wide_ b len


val lemma_eval_: h:mem -> b:felem{live h b} -> i:nat{i <= len} -> Lemma
  (requires (true))
  (ensures (seval_ (as_seq h b) i = eval_ h b i))
let rec lemma_eval_ h b i =
  if i = 0 then ()
  else (lemma_eval_ h b (i-1))

val lemma_eval: h:mem -> b:felem{live h b} -> Lemma
  (requires (true))
  (ensures (seval (as_seq h b) = eval h b))
  [SMTPat (eval h b)]
let lemma_eval h b = lemma_eval_ h b len


val lemma_eval_wide_: h:mem -> b:felem_wide{live h b} -> i:nat{i <= len} -> Lemma
  (requires (true))
  (ensures (seval_wide_ (as_seq h b) i = eval_wide_ h b i))
let rec lemma_eval_wide_ h b i =
  if i = 0 then () else lemma_eval_wide_ h b (i-1)

val lemma_eval_wide: h:mem -> b:felem_wide{live h b} -> Lemma
  (requires (true))
  (ensures (seval_wide (as_seq h b) = eval_wide h b))
  [SMTPat (eval_wide h b)]
let lemma_eval_wide h b = lemma_eval_wide_ h b len


val lemma_seval_def: s:seqelem -> i:nat{i <= len} -> Lemma
  ((i > 0 ==> seval_ s i = pow2 (limb_size * (i-1)) * Hacl.Bignum.Limb.v (Seq.index s (i-1)) + seval_ s (i-1))
    /\ (i = 0 ==> seval_ s i = 0))
let lemma_seval_def s i = ()


val lemma_seval_wide_def: s:seqelem_wide -> i:nat{i <= len} -> Lemma
  ((i > 0 ==> seval_wide_ s i = pow2 (limb_size * (i-1)) * w (Seq.index s (i-1)) + seval_wide_ s (i-1))
    /\ (i = 0 ==> seval_wide_ s i = 0))
let lemma_seval_wide_def s i = ()
