module Hacl.Spec.Bignum.Fdifference

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb

module U32 = FStar.UInt32

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let gte_limbs (a:seqelem) (b:seqelem) (l:nat{l <= len}) : GTot Type0 =
  (forall (i:nat). {:pattern (Seq.index a i) \/ (Seq.index b i)} i < l ==> v (Seq.index b i) >= v (Seq.index a i))


private
let lemma_mod (a:nat) (b:nat) : Lemma (requires (b >= a /\ b < pow2 n))
                                    (ensures ((b - a) % pow2 n = b - a))
                                    [SMTPat ((b - a) % pow2 n)]
  = Math.Lemmas.modulo_lemma (b - a) (pow2 n)

val fdifference_spec:
  a:seqelem -> b:seqelem{gte_limbs a b len} ->
  Tot (s:seqelem{
    (forall (i:nat). {:pattern (v (Seq.index s i))} i < len ==> v (Seq.index s i) = v (Seq.index b i) - v (Seq.index a i))})
let fdifference_spec a b =
  Spec.Loops.seq_map2 (fun x y -> y -%^ x) a b


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

val lemma_fdifference_eval_:  a:seqelem -> b:seqelem ->
  ctr:nat{ctr <= len /\ gte_limbs a b len} ->
  Lemma (seval_ (fdifference_spec a b) ctr = seval_ b ctr - seval_ a ctr)
let rec lemma_fdifference_eval_ s s' ctr =
  if ctr = 0 then ()
  else lemma_fdifference_eval_ s s' (ctr-1)

val lemma_fdifference_eval:  a:seqelem -> b:seqelem{gte_limbs a b len} ->
  Lemma (seval_ (fdifference_spec a b) len = seval_ b len - seval_ a len)
let rec lemma_fdifference_eval s s' = lemma_fdifference_eval_ s s' len
