module Hacl.Spec.Bignum.Fsum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let red (s:seqelem) (l:nat{l <= len}) = (forall (i:nat). {:pattern (v (Seq.index s i))} (i < l)
                                                 ==> v (Seq.index s i) < pow2 (n - 1))

private
let lemma_mod (a:nat) (b:nat) : Lemma (requires (a < pow2 (n-1) /\ b < pow2 (n-1)))
                                    (ensures ((a + b) % pow2 n = a + b))
                                    [SMTPat ((a + b) % pow2 n)]
  = Math.Lemmas.pow2_double_sum (n-1);
    Math.Lemmas.modulo_lemma (a+b) (pow2 n)

val fsum_spec:
  s:seqelem{red s len} -> s':seqelem{red s' len} ->
  Tot (s'':seqelem{(forall (i:nat). {:pattern (v (Seq.index s'' i))}
                              i < len ==> v (Seq.index s'' i) = v (Seq.index s i) + v (Seq.index s' i))})
let fsum_spec a b =
  Spec.Loops.seq_map2 (fun x y -> x +%^ y) a b

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

private
val lemma_fsum_eval_: s:seqelem -> s':seqelem -> ctr:nat{ctr <= len /\ red s len /\ red s' len} ->
  Lemma (seval_ (fsum_spec s s') ctr = seval_ s ctr + seval_ s' ctr)
let rec lemma_fsum_eval_ s s' ctr =
  if ctr = 0 then ()
  else lemma_fsum_eval_ s s' (ctr-1)

val lemma_fsum_eval: s:seqelem -> s':seqelem{red s len /\ red s' len} ->
  Lemma (seval (fsum_spec s s') = seval s + seval s')
let lemma_fsum_eval s s' = lemma_fsum_eval_ s s' len
