module Spec.ECDSA.Lemmas

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open FStar.Mul

open FStar.Math.Lemmas
open FStar.Math.Lib

#set-options "--fuel 0 --ifuel 0 --z3rlimit 100"


val lemma_scalar_ith: sc:lbytes 32 -> k:nat{k < 32} -> Lemma
  (v sc.[k] == nat_from_intseq_le sc / pow2 (8 * k) % pow2 8)

let lemma_scalar_ith sc k =
  index_nat_to_intseq_le #U8 #SEC 32 (nat_from_intseq_le sc) k;
  nat_from_intseq_le_inj sc (nat_to_intseq_le 32 (nat_from_intseq_le sc))


val lemma_euclidian_for_ithbit: k: nat -> i: nat
  -> Lemma (k / (pow2 (8 * (i / 8)) * pow2 (i % 8)) == k / pow2 i)

let lemma_euclidian_for_ithbit k i =
  lemma_div_def i 8;
  pow2_plus (8 * (i / 8)) (i % 8)


#push-options "--fuel 1"

val index_seq_of_list_cons: #a:Type -> x:a -> l:list a -> i:nat{i < List.Tot.length l} -> Lemma
  (Seq.index (Seq.seq_of_list (x::l)) (i+1) == Seq.index (Seq.seq_of_list l) i)

let index_seq_of_list_cons #a x l i =
  assert (Seq.index (Seq.seq_of_list (x::l)) (i+1) == List.Tot.index (x::l) (i+1))

#push-options "--ifuel 1"

val nat_from_intlist_le: #t:inttype{unsigned t} -> #l:secrecy_level -> list (uint_t t l) -> nat

let rec nat_from_intlist_le #t #l = function
  | [] -> 0
  | hd :: tl -> v hd + pow2 (bits t) * nat_from_intlist_le tl

val nat_from_intlist_be: #t:inttype{unsigned t} -> #l:secrecy_level -> list (uint_t t l) -> nat

let rec nat_from_intlist_be #t #l = function
  | [] -> 0
  | hd :: tl -> pow2 (FStar.List.Tot.Base.length tl * bits t) * v hd + nat_from_intlist_be tl


val nat_from_intlist_seq_be: #t: inttype {unsigned t} -> #l: secrecy_level
  -> len: size_nat -> b: list (uint_t t l) {FStar.List.Tot.Base.length b = len}
  -> Lemma (nat_from_intlist_be b == nat_from_intseq_be (of_list b))

let rec nat_from_intlist_seq_be #t #l len b =
  match b with
  | [] -> ()
  | hd :: tl ->
    begin
      let s = of_list b in
      Classical.forall_intro (index_seq_of_list_cons hd tl);
      assert (equal (of_list tl) (slice s 1 len));
      assert (index s 0 == List.Tot.index b 0);
      nat_from_intlist_seq_be (len - 1) tl;
      nat_from_intseq_be_lemma0 (slice s 0 1);
      nat_from_intseq_be_slice_lemma s 1
      end

#pop-options


val nat_from_intlist_seq_le: #t:inttype{unsigned t} -> #l:secrecy_level
  -> len:size_nat -> b:list (uint_t t l){List.Tot.length b = len}
  -> Lemma (nat_from_intlist_le b == nat_from_intseq_le (of_list b))

let rec nat_from_intlist_seq_le #t #l len b =
  match b with
  | [] -> ()
  | hd :: tl ->
    begin
    let s = of_list b in
    Classical.forall_intro (index_seq_of_list_cons hd tl);
    assert (equal (of_list tl) (slice s 1 len));
    assert (index s 0 == List.Tot.index b 0);
    nat_from_intseq_le_lemma0 (slice s 0 1);
    nat_from_intseq_le_slice_lemma s 1;
    nat_from_intlist_seq_le (len - 1) tl
    end


#pop-options


val modulo_distributivity_mult: a: int -> b: int -> c: pos -> 
  Lemma ((a * b) % c = ((a % c) * (b % c)) % c)

let modulo_distributivity_mult a b c = 
  lemma_mod_mul_distr_l a b c;
  lemma_mod_mul_distr_r (a % c) b c