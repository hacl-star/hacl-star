module Hacl.Spec.EC.Ladder

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum
open Hacl.Spec.EC.Point
open Hacl.Spec.EC.AddAndDouble
open Hacl.Spec.EC.AddAndDouble2
open Hacl.Spec.EC.Format

module U32 = FStar.UInt32
module H8 = Hacl.UInt8

type uint8_s = Seq.seq H8.t

let spoint_513' = q:spoint{red_513 (fst q)}


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val cmult_small_loop_step_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  (* i:ctr{U32.v i <= 8 /\ U32.v i - 1 >= 0} -> *)
  GTot (nq2:(spoint_513 * nqpq2:spoint_513){
    let bit  = (H8.v byte / pow2 7) % 2 in
    let nq   = Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq)) in
    let nqpq = Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq)) in
    let q    = selem (fst q) in
    let nq', nqpq' =
      if bit = 1 then let a, b = Spec.Curve25519.add_and_double q nqpq nq in b,a
      else Spec.Curve25519.add_and_double q nq nqpq in
    let nq'' = Spec.Curve25519.Proj (selem (fst (fst nq2))) (selem (snd (fst nq2))) in
    let nqpq'' = Spec.Curve25519.Proj (selem (fst (snd nq2))) (selem (snd (snd nq2))) in
    (nq', nqpq') == (nq'', nqpq'')
  })
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
let cmult_small_loop_step_spec nq nqpq q byt (* i *) =
  assert_norm((pow2 8 - 1) / pow2 7 < 2);
  (* cut (U32.v i - 1 >= 0); *)
  (* let i' = U32.(i -^ 1ul) in *)
  Math.Lemmas.lemma_div_lt (H8.v byt) 8 7;
  assert_norm(pow2 1 = 2); Math.Lemmas.modulo_lemma (H8.v byt / pow2 7) 2;
  let bit = byte_to_limb (H8.(byt >>^ 7ul)) in
  cut (v bit = 0 \/ v bit = 1);
  cut (v bit = (H8.v byt / pow2 7) % 2);
  let nq', nqpq' = swap_conditional_spec nq nqpq bit in
  let nqx = sgetx nq' in
  let nqz = sgetz nq' in
  let nqpqx = sgetx nqpq' in
  let nqpqz = sgetz nqpq' in
  Hacl.Spec.EC.AddAndDouble3.lemma_fmonty_split nqx nqz nqpqx nqpqz (sgetx q);
  let nq2x, nq2z, nqpq2x, nqpq2z = fmonty_tot nqx nqz nqpqx nqpqz (sgetx q) in
  let nq2', nqpq2' = swap_conditional_spec (nq2x, nq2z) (nqpq2x, nqpq2z) bit in
  (nq2', nqpq2')

open Hacl.Spec.Endianness

val cmult_small_loop_double_step_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  (* i:ctr{U32.v i <= 4 /\ U32.v i > 0} -> *)
  GTot (t:(spoint_513 * spoint_513){
    let nq   = Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq)) in
    let nqpq = Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq)) in
    let nq'' = Spec.Curve25519.Proj (selem (fst (fst t))) (selem (snd (fst t))) in
    let nqpq'' = Spec.Curve25519.Proj (selem (fst (snd t))) (selem (snd (snd t))) in
    let nq', nqpq' = Hacl.Spec.EC.Ladder.Lemmas.double_step (selem (fst q)) nq nqpq (h8_to_u8 byte) in
    (nq', nqpq') == (nq'', nqpq'')
  })
let cmult_small_loop_double_step_spec nq nqpq q byt (* i  *)=
  let nq2', nqpq2' = cmult_small_loop_step_spec nq nqpq q byt (* i *) in
  let byt = H8.(byt <<^ 1ul) in
  cmult_small_loop_step_spec nq2' nqpq2' q byt


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

val cmult_small_loop_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  i:ctr{U32.v i <= 4} ->
  GTot (t:(spoint_513 * spoint_513){
    let nq   = Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq)) in
    let nqpq = Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq)) in
    let nq'' = Spec.Curve25519.Proj (selem (fst (fst t))) (selem (snd (fst t))) in
    let nqpq'' = Spec.Curve25519.Proj (selem (fst (snd t))) (selem (snd (snd t))) in
    let nq', nqpq' = Hacl.Spec.EC.Ladder.Lemmas.small_loop (selem (fst q)) nq nqpq (h8_to_u8 byte) (U32.v i) in
    (nq', nqpq') == (nq'', nqpq'')
  })
  (decreases (U32.v i))
let rec cmult_small_loop_spec nq nqpq q byt i =
  if (U32.(i =^ 0ul)) then (
    Hacl.Spec.EC.Ladder.Lemmas.lemma_small_loop_def_0 (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (h8_to_u8 byt);
    (nq, nqpq)
  ) else (
    cut (U32.v i > 0);
    let i' = U32.(i -^ 1ul) in
    let nq', nqpq' = cmult_small_loop_double_step_spec nq nqpq q byt (* i *) in
    Hacl.Spec.EC.Ladder.Lemmas.lemma_small_loop_def_1 (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (h8_to_u8 byt) (U32.v i);
    let byt' = H8.(byt <<^ 2ul) in
    cmult_small_loop_spec nq' nqpq' q byt' i'
  )


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val cmult_big_loop_spec:
  n:uint8_s{Seq.length n = 32} ->
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  i:U32.t{U32.v i <= 32} ->
  GTot (t:(spoint_513){
    let nq   = Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq)) in
    let nqpq = Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq)) in
    let nq'' = Spec.Curve25519.Proj (selem (fst (t))) (selem (snd (t))) in
    let n    = reveal_sbytes n in
    let nq' = Hacl.Spec.Curve25519.Lemmas.montgomery_ladder_big (selem (fst q)) nq nqpq n (U32.v i) in
    nq' == nq''
  })
  (decreases (U32.v i))
#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"
let rec cmult_big_loop_spec n nq nqpq q i =
  if (U32.(i =^ 0ul)) then (
    Hacl.Spec.Curve25519.Lemmas.montgomery_ladder_big_def_0 (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (reveal_sbytes n);
    nq
  )
  else (
    cut (U32.v i > 0);
    let i' = U32.(i -^ 1ul) in
    let byte = Seq.index n (U32.v i') in
    let nq2, nqpq2 = cmult_small_loop_spec nq nqpq q byte 4ul in
    Hacl.Spec.EC.Ladder.Lemmas.lemma_small_loop_unrolled3 (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (h8_to_u8 byte);
    Hacl.Spec.Curve25519.Lemmas.lemma_small_step_eq (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (reveal_sbytes n) (U32.v i);
    Hacl.Spec.Curve25519.Lemmas.montgomery_ladder_big_def_1 (selem (fst q)) (Spec.Curve25519.Proj (selem (fst nq)) (selem (snd nq))) (Spec.Curve25519.Proj (selem (fst nqpq)) (selem (snd nqpq))) (reveal_sbytes n) (U32.v i);
    cmult_big_loop_spec n nq2 nqpq2 q i'
  )


val cmult_spec: scalar:uint8_s{Seq.length scalar = keylen} ->
  q:spoint_513{selem (snd q) = one} ->
  GTot (result:spoint_513{
    let r = Spec.Curve25519.Proj (selem (fst result)) (selem (snd result)) in
    r == Spec.Curve25519.montgomery_ladder (selem (fst q)) (reveal_sbytes scalar)
  })
let cmult_spec n q =
  let nq = point_inf () in
  Hacl.Spec.Curve25519.Lemmas.lemma_montgomery_ladder_8 (selem (fst q)) (Spec.Curve25519.Proj one zero) (Spec.Curve25519.Proj (selem (fst q)) (selem (snd q))) (reveal_sbytes n) 32;
  cmult_big_loop_spec n nq q q 32ul
