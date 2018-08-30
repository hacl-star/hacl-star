module Spec.Frodo.Pack

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix

module Seq = Lib.Sequence

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives -Spec.* +Spec.Frodo +Spec.Frodo.Params' --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped"

private
val shiftleft_bounds: d:size_nat{d <= 16} ->
  Lemma (
    7 * d < bits U128 /\
    6 * d < bits U128 /\
    5 * d < bits U128 /\
    4 * d < bits U128 /\
    3 * d < bits U128 /\
    2 * d < bits U128 /\
    1 * d < bits U128 /\
    0 * d < bits U128)
let shiftleft_bounds d = ()

inline_for_extraction noextract
val frodo_pack_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> a:matrix n1 n2
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t /\ d <= 16}
  -> i:size_nat{i < n1}
  -> res:lbytes (d * n1 * n2 / 8)
  -> lbytes (d * n1 * n2 / 8)
let frodo_pack_inner #n1 #n2 a d i res =
  let maskd = to_u16 (u32 1 <<. u32 d) -. u16 1 in  
  repeati (n2 / 8)
  (fun j res ->
    Lemmas.lemma_matrix_index_repeati n1 n2 d i j;
    let start = (i * (n2 / 8) + j) * d in
    assert_spinoff (start + d <= d * n1 * n2 / 8);
    let aij0 = a.(i, 8 * j + 0) &. maskd in
    let aij1 = a.(i, 8 * j + 1) &. maskd in
    let aij2 = a.(i, 8 * j + 2) &. maskd in
    let aij3 = a.(i, 8 * j + 3) &. maskd in
    let aij4 = a.(i, 8 * j + 4) &. maskd in
    let aij5 = a.(i, 8 * j + 5) &. maskd in
    let aij6 = a.(i, 8 * j + 6) &. maskd in
    let aij7 = a.(i, 8 * j + 7) &. maskd in
    let templong =
         to_u128 aij0 <<. u32 (7 * d)
      |. to_u128 aij1 <<. u32 (6 * d)
      |. to_u128 aij2 <<. u32 (5 * d)
      |. to_u128 aij3 <<. u32 (4 * d)
      |. to_u128 aij4 <<. u32 (3 * d)
      |. to_u128 aij5 <<. u32 (2 * d)
      |. to_u128 aij6 <<. u32 (1 * d)
      |. to_u128 aij7 <<. u32 (0 * d)
    in
    let v16 = uint_to_bytes_be templong in
    let src = Seq.sub v16 (16 - d) d in
    update_sub res start d src)
  res

val frodo_pack:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> a:matrix n1 n2
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t /\ d <= 16}
  -> lbytes (d * n1 * n2 / 8)
let frodo_pack #n1 #n2 a d =
  let res = Seq.create (d * n1 * n2 / 8) (u8 0) in
  repeati n1 (frodo_pack_inner a d) res

/// Unpack

inline_for_extraction noextract
val frodo_unpack_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t /\ d <= 16}
  -> b:lbytes (d * n1 * n2 / 8)
  -> i:size_nat{i < n1}
  -> res:matrix n1 n2
  -> matrix n1 n2
let frodo_unpack_inner #n1 #n2 d b i res =
  shiftleft_bounds d;
  let maskd = to_u16 (u32 1 <<. u32 d) -. u16 1 in
  let v16 = Seq.create 16 (u8 0) in
  repeati (n2 / 8)
  (fun j res ->
    Lemmas.lemma_matrix_index_repeati n1 n2 d i j;
    let start:size_nat = (i * n2 / 8 + j) * d in
    assert (start + d <= length b);
    let vij = Seq.sub b start d in
    let src = update_sub v16 (16 - d) d vij in
    let templong = uint_from_bytes_be src in
    let res = res.(i, 8 * j + 0) <- to_u16 (templong >>. u32 (7 * d)) &. maskd in
    let res = res.(i, 8 * j + 1) <- to_u16 (templong >>. u32 (6 * d)) &. maskd in
    let res = res.(i, 8 * j + 2) <- to_u16 (templong >>. u32 (5 * d)) &. maskd in
    let res = res.(i, 8 * j + 3) <- to_u16 (templong >>. u32 (4 * d)) &. maskd in
    let res = res.(i, 8 * j + 4) <- to_u16 (templong >>. u32 (3 * d)) &. maskd in
    let res = res.(i, 8 * j + 5) <- to_u16 (templong >>. u32 (2 * d)) &. maskd in
    let res = res.(i, 8 * j + 6) <- to_u16 (templong >>. u32 (1 * d)) &. maskd in
    let res = res.(i, 8 * j + 7) <- to_u16 (templong >>. u32 (0 * d)) &. maskd in
    res)
  res

val frodo_unpack:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t /\ d <= 16}
  -> b:lbytes (d * n1 * n2 / 8)
  -> matrix n1 n2
let frodo_unpack #n1 #n2 d b =
  let res = create n1 n2 in
  repeati n1 (frodo_unpack_inner #n1 #n2 d b) res
