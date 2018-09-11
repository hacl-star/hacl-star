module Spec.Frodo.Pack

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix

module Seq = Lib.Sequence

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar +FStar.Pervasives -Spec +Spec.Frodo +Spec.Frodo.Params'"

val frodo_pack8:
    a:lseq uint16 8
  -> d:size_nat{d <= 16}
  -> lbytes d
let frodo_pack8 a d =
  let maskd = to_u16 (u32 1 <<. u32 d) -. u16 1 in
  let a0 = Seq.index a 0 &. maskd in
  let a1 = Seq.index a 1 &. maskd in
  let a2 = Seq.index a 2 &. maskd in
  let a3 = Seq.index a 3 &. maskd in
  let a4 = Seq.index a 4 &. maskd in
  let a5 = Seq.index a 5 &. maskd in
  let a6 = Seq.index a 6 &. maskd in
  let a7 = Seq.index a 7 &. maskd in
  let templong =
       to_u128 a0 <<. u32 (7 * d)
    |. to_u128 a1 <<. u32 (6 * d)
    |. to_u128 a2 <<. u32 (5 * d)
    |. to_u128 a3 <<. u32 (4 * d)
    |. to_u128 a4 <<. u32 (3 * d)
    |. to_u128 a5 <<. u32 (2 * d)
    |. to_u128 a6 <<. u32 (1 * d)
    |. to_u128 a7 <<. u32 (0 * d)
  in
  let v16 = uint_to_bytes_be templong in
  Seq.sub v16 (16 - d) d

val update_sub:
    #a:Type
  -> #len:size_nat
  -> i:lseq a len
  -> start:size_nat
  -> n:size_nat{start + n <= len}
  -> x:lseq a n
  -> o:lseq a len{
    Seq.equal (Seq.sub o start n) x /\
    (forall (a:size_nat) (len:size_nat).{:pattern (Seq.sub o a len)}
      a + len <= start ==> Seq.equal (Seq.sub o a len) (Seq.sub i a len))}
let update_sub #a #len i start n x =
  update_sub #a #len i start n x

val frodo_pack:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> a:matrix n1 n2
  -> d:size_nat{d * (n1 * n2 / 8) <= max_size_t /\ d <= 16}
  -> res:lbytes (d * (n1 * n2 / 8)){
    forall (j:nat{j < n1 * n2 / 8}).
      let a8 = Seq.sub #uint16 a (8 * j) 8 in
      Seq.equal (Seq.sub res (d * j) d) (frodo_pack8 a8 d)}
let frodo_pack #n1 #n2 a d =
  repeati_inductive (n1 * n2 / 8)
  (fun i res ->
    (forall (j:nat{j < i}).
      let a8 = Seq.sub #uint16 a (8 * j) 8 in
      d * j + d <= d * (n1 * n2 / 8) /\
      Seq.equal (Seq.sub res (d * j) d) (frodo_pack8 a8 d)))
  (fun i res ->
    assert_spinoff (d * i + d <= d * (n1 * n2 / 8));
    let a8 = Seq.sub #uint16 a (8 * i) 8 in
    update_sub res (d * i) d (frodo_pack8 a8 d))
  (Seq.create (d * (n1 * n2 / 8)) (u8 0))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

val bar:
    n:size_nat
  -> d:size_nat{d * n <= max_size_t}
  -> b1:lbytes (d * n)
  -> b2:lbytes (d * n)
  -> Lemma
    (requires
      forall (j:nat{j < n}).
        d * j + d <= d * n /\
        FStar.Seq.equal
          (FStar.Seq.slice b1 (d * j) (d * j + d))
          (FStar.Seq.slice b2 (d * j) (d * j + d)))
    (ensures Seq.equal b1 b2)
let bar n d b1 b2 =
  let open FStar.Seq in
  let f (i:nat{i < d * n}) : Lemma (index b1 i == index b2 i) =
    let j = i / d in
    assert (
      d * j + d <= d * n /\
      equal (slice b1 (d * j) (d * j + d)) (slice b2 (d * j) (d * j + d)));
    assert (
      index (slice b1 (d * j) (d * j + d)) (i % d) ==
      index (slice b2 (d * j) (d * j + d)) (i % d))
  in
  Classical.forall_intro f


/// Unpack

val frodo_unpack_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ n2 % 8 = 0}
  -> d:size_nat{d * n1 <= max_size_t /\ d * n1 * n2 / 8 <= max_size_t /\ d <= 16}
  -> b:lbytes (d * n1 * n2 / 8)
  -> i:size_nat{i < n1}
  -> res:matrix n1 n2
  -> matrix n1 n2
let frodo_unpack_inner #n1 #n2 d b i res =
  admit();
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
