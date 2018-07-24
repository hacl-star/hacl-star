module Spec.Frodo.Pack

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params

module Seq = Lib.Sequence

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives -Spec.* +Spec.Frodo +Spec.Frodo.Params'"

val frodo_pack:
    n1: size_nat
  -> n2: size_nat{n1 * n2 < max_size_t /\ n2 % 8 = 0}
  -> a: matrix n1 n2
  -> d: size_nat{d * n1 * n2 / 8 < max_size_t /\ d <= 16}
  -> lbytes (d * n1 * n2 / 8)
let frodo_pack n1 n2 a d =
  let maskd = (u128 1 <<. u32 d) -. u128 1 in
  let resLen = d * n1 * n2 / 8 in
  let res = Seq.create resLen (u8 0) in
  repeati n1
  (fun i res ->
    repeati (n2 / 8)
    (fun j res ->
      let templong = repeati 8
      (fun k templong ->
        let aij = a.(i, 8 * j + k) in
        templong |. ((to_u128 aij &. maskd) <<. u32 (7 * d - d * k))
      ) (u128 0) in
      lemma_matrix_index_repeati n1 n2 d i j;
      update_sub res ((i * n2 / 8 + j) * d) d (Seq.sub (uint_to_bytes_be templong) (16 - d) d)
    ) res
  ) res

val frodo_unpack:
    n1: size_nat
  -> n2: size_nat{n1 * n2 < max_size_t /\ n2 % 8 = 0}
  -> d: size_nat{d * n1 * n2 / 8 < max_size_t /\ d <= 16}
  -> b: lbytes (d * n1 * n2 / 8)
  -> matrix n1 n2
let frodo_unpack n1 n2 d b =
  let maskd = (u128 1 <<. u32 d) -. u128 1 in
  let res = create n1 n2 in
  let v16 = Seq.create 16 (u8 0) in
  repeati n1
  (fun i res ->
    repeati (n2 / 8)
    (fun j res ->
      lemma_matrix_index_repeati n1 n2 d i j;
      let vij = Seq.sub b ((i * n2 / 8 + j) * d) d in
      let v16 = uint_from_bytes_be (update_sub v16 (16 - d) d vij) in
      repeati 8
      (fun k res ->
        res.(i, 8 * j + k) <- to_u16 ((v16 >>. u32 (7 * d - d * k)) &. maskd)
      ) res
    ) res
  ) res
