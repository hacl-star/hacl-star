(* demo at https://www.fstar-lang.org/tutorial/ *)

module Integers


(** Several definitions of the factorial function **)

(* factorial function (non-tail version) *)
let rec factorial (n:nat) : Tot nat =
  if n = 0 then 1 else op_Multiply (factorial (n-1)) n

(* tail-rec factorial with accumulator *)
let rec factorial_tail_aux (n:nat) (accu:nat) : Tot nat =
  if n = 0 then accu
  else factorial_tail_aux (n-1) (op_Multiply n accu)
let factorial_tail (n:nat) : Tot nat =
  factorial_tail_aux n 1

(*tail-rec factorial with cps *)
let rec factorial_cps_aux (n:nat) (f:nat->Tot nat) : Tot nat =
  if n = 0 then f 1
  else factorial_cps_aux (n-1) (fun res -> f (op_Multiply res n))
let factorial_cps (n:nat) : Tot nat =
  factorial_cps_aux n (fun res -> res)



(** Equivalence of the several definitions **)

(* correctness of the accumulator version, formalised with a local auxiliary lemma *)
let correctness_factorial_tail_raw (n:nat) : Lemma
  (requires True)
  (ensures factorial_tail n = factorial n) =

  let rec induction_lemma (n:nat) (accu:nat) : Lemma
    (requires True)
    (ensures op_Multiply (factorial n) accu = factorial_tail_aux n accu) =
    if n = 0 then ()
    else induction_lemma (n-1) (op_Multiply n accu) in

  induction_lemma n 1


(* correctness of the accumulator version, formalised with a separated auxiliary lemma *)
let rec correctness_factorial_tail_aux (n:nat) (accu:nat) : Lemma
  (requires True)
  (ensures factorial_tail_aux n accu = (op_Multiply (factorial n) accu)) =
  if n = 0 then ()
  else correctness_factorial_tail_aux (n-1) (op_Multiply n accu)
let correctness_factorial_tail (n:nat) : Lemma
  (requires True)
  (ensures factorial_tail n = factorial n) =
  correctness_factorial_tail_aux n 1


(* correctness of the cps version, formalised with a local auxiliary lemma *)
let correctness_factorial_cps_raw (n:nat) : Lemma
  (requires True)
  (ensures factorial_cps n = factorial n) =

  let rec induction_lemma (n:nat) (f:nat->nat) : Lemma
    (requires True)
    (ensures factorial_cps_aux n f = f (factorial n)) =
    if n = 0 then ()
    else induction_lemma (n-1) (fun res -> f (op_Multiply res n)) in

  induction_lemma n (fun res -> res)


(* correctness of the cps version, formalised with a separated auxiliary lemma
/!\ FStar does not manage to prove the auxiliary lemma *)
let rec correctness_factorial_cps_aux (n:nat) (f:nat->nat) : Lemma
    (requires True)
    (ensures factorial_cps_aux n f = f (factorial n)) =
    if n = 0 then ()
    else correctness_factorial_cps_aux (n-1) (fun res -> f (op_Multiply res n))
let correctness_factorial_cps (n:nat) : Lemma
  (requires True)
  (ensures factorial_cps n = factorial n) =
  correctness_factorial_cps_aux n (fun res -> res)
