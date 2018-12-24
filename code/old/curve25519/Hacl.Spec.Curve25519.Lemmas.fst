module Hacl.Spec.Curve25519.Lemmas

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Spec.Curve25519

#reset-options "--max_fuel 0"

val montgomery_ladder_step: init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr > 0 /\ ctr <= 256} ->  Tot (proj_point * proj_point)
let montgomery_ladder_step init x xp1 k ctr =
  let ctr' = ctr - 1 in
  let (x', xp1') =
    if ith_bit k ctr' = 1 then (
      let nqp2, nqp1 = add_and_double init xp1 x in
      nqp1, nqp2
    ) else add_and_double init x xp1 in
  (x', xp1')

#reset-options "--max_fuel 0"

val montgomery_ladder_def_0:
  init:elem ->
  x:proj_point ->
  xp1:proj_point ->
  k:scalar ->
  Lemma (montgomery_ladder_ init x xp1 k 0 == x)
#reset-options
let montgomery_ladder_def_0 init x xp1 k = ()

#reset-options "--max_fuel 0"

val montgomery_ladder_def_1:
  init:elem ->
  x:proj_point ->
  xp1:proj_point ->
  k:scalar ->
  ctr:nat{ctr > 0 /\ ctr <= 256} ->
  Lemma (montgomery_ladder_ init x xp1 k ctr == (let (x', xp1') = montgomery_ladder_step init x xp1 k ctr in montgomery_ladder_ init x' xp1' k (ctr - 1)))
#reset-options
let montgomery_ladder_def_1 init x xp1 k ctr = ()

#reset-options "--max_fuel 0 --z3rlimit 20"

val montgomery_ladder_small_step: init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> i:nat{i >= 8 /\ i <= 256} -> Tot (proj_point * proj_point)
let montgomery_ladder_small_step init x xp1 k i =
  let open FStar.Mul in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-1) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-2) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-3) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-4) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-5) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-6) in
  let x, xp1 = montgomery_ladder_step init x xp1 k (i-7) in
  x, xp1

val montgomery_ladder_big: init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr <= 32} -> Tot (proj_point) (decreases ctr)
let rec montgomery_ladder_big init x xp1 k ctr =
  if ctr = 0 then x
  else (
    cut (ctr > 0); cut (op_Multiply ctr 8 >= 8);
    let i = ctr - 1 in
    let x, xp1 = montgomery_ladder_small_step init x xp1 k (op_Multiply ctr 8) in
    montgomery_ladder_big init x xp1 k i
  )

#reset-options "--max_fuel 0"

val montgomery_ladder_big_def_0: init:elem -> x:proj_point -> xp1:proj_point -> k:scalar ->
  Lemma (montgomery_ladder_big init x xp1 k 0 == x)
#reset-options
let montgomery_ladder_big_def_0 init x xp1 k = ()

#reset-options "--max_fuel 0"

val montgomery_ladder_big_def_1:
  init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr > 0 /\ ctr <= 32} ->
  Lemma (montgomery_ladder_big init x xp1 k ctr == (let x, xp1 = montgomery_ladder_small_step init x xp1 k (op_Multiply ctr 8) in montgomery_ladder_big init x xp1 k (ctr-1)))
#reset-options
let montgomery_ladder_big_def_1 init x xp1 k ctr = ()

#reset-options "--max_fuel 0"

val lemma_montgomery_ladder_gte_8:
  init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr >= 8 /\ ctr <= 256} ->
  Lemma (montgomery_ladder_ init x xp1 k ctr ==
         (let x, xp1 = montgomery_ladder_small_step init x xp1 k ctr in
          montgomery_ladder_ init x xp1 k (ctr-8)))
#reset-options "--max_fuel 0 --z3rlimit 100"
let rec lemma_montgomery_ladder_gte_8 init x xp1 k ctr =
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr;
  let x, xp1 = montgomery_ladder_step init x xp1 k ctr in
  let ctr = ctr - 1 in
  montgomery_ladder_def_1 init x xp1 k ctr


#reset-options "--max_fuel 0"

private let lemma_mul_0 (a:int) : Lemma (op_Multiply a 0 = 0 /\ op_Multiply 0 a = 0) = ()
private let lemma_mul_8 (a:int{a > 0}) : Lemma (op_Multiply a 8 - 8 = op_Multiply (a-1) 8
  /\ op_Multiply (a-1) 8 >= 0) =
    Math.Lemmas.distributivity_sub_left a 1 8


val lemma_montgomery_ladder_8:
  init:elem -> x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr <= 32} ->
  Lemma (requires (True))
        (ensures (montgomery_ladder_big init x xp1 k ctr == montgomery_ladder_ init x xp1 k (op_Multiply 8 ctr)))
        (decreases ctr)
#reset-options "--max_fuel 0 --z3rlimit 100"
let rec lemma_montgomery_ladder_8 init x xp1 k ctr =
  if ctr = 0 then (
    lemma_mul_0 8;
    montgomery_ladder_def_0 init x xp1 k;
    montgomery_ladder_big_def_0 init x xp1 k
  ) else (
    cut (ctr > 0);
    let ctr':nat = ctr - 1 in
    lemma_mul_8 ctr;
    cut (op_Multiply ctr 8 >= 8);
    montgomery_ladder_big_def_1 init x xp1 k ctr;
    lemma_montgomery_ladder_gte_8 init x xp1 k (op_Multiply ctr 8);
    let x, xp1 = montgomery_ladder_small_step init x xp1 k (op_Multiply ctr 8) in
    lemma_montgomery_ladder_8 init x xp1 k ctr'
  )

val lemma_div_8: ctr:pos -> Lemma
  (let ctr8 = op_Multiply ctr 8 in
   (ctr8 - 1) / 8 = ctr - 1
   /\ (ctr8 - 2) / 8 = ctr - 1
   /\ (ctr8 - 3) / 8 = ctr - 1
   /\ (ctr8 - 4) / 8 = ctr - 1
   /\ (ctr8 - 5) / 8 = ctr - 1
   /\ (ctr8 - 6) / 8 = ctr - 1
   /\ (ctr8 - 7) / 8 = ctr - 1
   /\ (ctr8 - 8) / 8 = ctr - 1)
let lemma_div_8 ctr = ()

val lemma_small_step_eq:
  init:elem ->
  x:proj_point -> xp1:proj_point -> k:scalar -> ctr:nat{ctr > 0 /\ ctr <= 32} ->
  Lemma (montgomery_ladder_small_step init x xp1 k FStar.Mul.(8 * ctr)
    == Hacl.Spec.EC.Ladder.Lemmas.small_loop_unrolled3 init x xp1 (Seq.index k (ctr-1)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let lemma_small_step_eq init x xp1 k ctr =
  lemma_div_8 ctr;
  let b = Seq.index k (ctr-1) in
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 1ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 2ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 3ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 4ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 5ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 6ul;
  Hacl.Spec.EC.Ladder.Lemmas.lemma_byte_bit b 7ul
