module Hacl.Spec.EC.Ladder

open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Bignum.Limb
open Hacl.Spec.EC.Point
open Hacl.Spec.EC.AddAndDouble
open Hacl.Spec.EC.AddAndDouble2
open Hacl.Spec.EC.Format

module U32 = FStar.UInt32
module H8 = Hacl.UInt8

type uint8_s = Seq.seq H8.t

let spoint_513' = q:spoint{red_513 (fst q)}

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val cmult_small_loop_step_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i > 0} ->
  Tot (nq2:spoint_513 * nqpq2:spoint_513)
  (decreases (U32.v i))
let cmult_small_loop_step_spec nq nqpq q byt i =
  let i' = U32.(i -^ 1ul) in
  let bit = byte_to_limb (H8.(byt >>^ 7ul)) in
  Math.Lemmas.lemma_div_lt (H8.v byt) 8 7;
  assert_norm(pow2 1 = 2); cut (v bit = 0 \/ v bit = 1);
  let nq', nqpq' = swap_conditional_spec nq nqpq bit in
  let nqx = sgetx nq' in
  let nqz = sgetz nq' in
  let nqpqx = sgetx nqpq' in
  let nqpqz = sgetz nqpq' in
  let nq2x, nq2z, nqpq2x, nqpq2z = fmonty_tot nqx nqz nqpqx nqpqz (sgetx q) in
  let nq2', nqpq2' = swap_conditional_spec (nq2x, nq2z) (nqpq2x, nqpq2z) bit in
  nq2', nqpq2'


val cmult_small_loop_double_step_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i > 1} ->
  Tot (nq2:spoint_513 * nqpq2:spoint_513)
  (decreases (U32.v i))
let cmult_small_loop_double_step_spec nq nqpq q byt i =
  let nq2', nqpq2' = cmult_small_loop_step_spec nq nqpq q byt i in
  let byt = H8.(byt <<^ 1ul) in
  let nq', nqpq'   = cmult_small_loop_step_spec nq2' nqpq2' q byt U32.(i-^1ul) in
  nq', nqpq'


val cmult_small_loop_spec:
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  byte:H8.t ->
  i:ctr{U32.v i <= 8 /\ U32.v i % 2 = 0} ->
  Tot (nq2:spoint_513 * nqpq2:spoint_513)
  (decreases (U32.v i))
let rec cmult_small_loop_spec nq nqpq q byt i =
  if (U32.(i =^ 0ul)) then (nq, nqpq)
  else (
    let i' = U32.(i -^ 2ul) in
    cut (U32.v i >= 2);
    cut (U32.v i' % 2 = 0);
    let nq', nqpq' = cmult_small_loop_double_step_spec nq nqpq q byt i in
    let byt' = H8.(byt <<^ 2ul) in
    cmult_small_loop_spec nq' nqpq' q byt' i'
    (* cut (U32.v i > 0); *)
    (* let i' = U32.(i -^ 1ul) in *)
    (* let bit = byte_to_limb (H8.(byt >>^ 7ul)) in *)
    (* Math.Lemmas.lemma_div_lt (H8.v byt) 8 7; *)
    (* assert_norm(pow2 1 = 2); cut (v bit = 0 \/ v bit = 1); *)
    (* let nq', nqpq' = swap_conditional_spec nq nqpq bit in *)
    (* let nqx = sgetx nq' in *)
    (* let nqz = sgetz nq' in *)
    (* let nqpqx = sgetx nqpq' in *)
    (* let nqpqz = sgetz nqpq' in *)
    (* let nq2x, nq2z, nqpq2x, nqpq2z = fmonty_tot nqx nqz nqpqx nqpqz (sgetx q) in *)
    (* let nq2', nqpq2' = swap_conditional_spec (nq2x, nq2z) (nqpq2x, nqpq2z) bit in *)
    (* let byt = H8.(byt <<^ 1ul) in *)
    (* cmult_small_loop_spec nq2' nqpq2' q byt i' *)
  )


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val cmult_big_loop_spec:
  n:uint8_s{Seq.length n = 32} ->
  nq:spoint_513 ->
  nqpq:spoint_513 ->
  q:spoint_513' ->
  i:U32.t{U32.v i <= 32} ->
  Tot (nq2:spoint_513 * nqpq2:spoint_513)
  (decreases (U32.v i))
let rec cmult_big_loop_spec n nq nqpq q i =
  if (U32.(i =^ 0ul)) then (nq, nqpq)
  else (
    let i = U32.(i -^ 1ul) in
    let byte = Seq.index n (U32.v i) in
    let nq2, nqpq2 = cmult_small_loop_spec nq nqpq q byte 8ul in
    cmult_big_loop_spec n nq2 nqpq2 q i
  )


val cmult_spec: scalar:uint8_s{Seq.length scalar = keylen} -> q:spoint_513 -> Tot (result:spoint_513)
let cmult_spec n q =
  let nq = point_inf () in
  let nq2, nqpq2 = cmult_big_loop_spec n nq q q 32ul in
  nq2
