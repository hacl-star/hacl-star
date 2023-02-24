module Hacl.Impl.P256.Constants

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.P256
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

open Hacl.Spec.P256.Felem

#set-options "--z3rlimit 50"

inline_for_extraction noextract
let p256_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == S.prime)
  } =
  [@inline_let]
  let x =
    [ u64 0xffffffffffffffff; u64 0xffffffff; u64 0; u64 0xffffffff00000001] in
    assert_norm (0xffffffffffffffff + 0xffffffff * pow2 64 + 0xffffffff00000001 * pow2 192 == S.prime);
  x


inline_for_extraction noextract
let p256_order_prime_list : x:list uint64{List.Tot.length x == 4 /\
  (
    let l0 = uint_v (List.Tot.index x 0) in
    let l1 = uint_v (List.Tot.index x 1) in
    let l2 = uint_v (List.Tot.index x 2) in
    let l3 = uint_v (List.Tot.index x 3) in
    l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 == S.order)
  } =
  [@inline_let]
  let x =
    [ u64 17562291160714782033; u64 13611842547513532036; u64 18446744073709551615; u64 18446744069414584320 ] in
    assert_norm (17562291160714782033 + 13611842547513532036 * pow2 64 + 18446744073709551615* pow2 128 + 18446744069414584320 * pow2 192 == S.order);
  x


let prime_buffer: x: glbuffer uint64 4ul {
  witnessed #uint64 #(size 4) x (LSeq.of_list p256_prime_list) /\
  recallable x /\
  felem_seq_as_nat (LSeq.of_list (p256_prime_list)) == S.prime} =

  assert_norm (felem_seq_as_nat (LSeq.of_list (p256_prime_list)) == S.prime);
  createL_global p256_prime_list


let primeorder_buffer: x: glbuffer uint64 (size 4) {
  witnessed #uint64 #(size 4) x (LSeq.of_list p256_order_prime_list) /\
  recallable x /\
  felem_seq_as_nat (LSeq.of_list (p256_order_prime_list)) == S.order} =
  createL_global p256_order_prime_list


//--------------------------------
// TODO: rm

#push-options "--ifuel 1"
val nat_from_intlist_le: #t:inttype{unsigned t} -> #l:secrecy_level -> list (uint_t t l) -> nat
let rec nat_from_intlist_le #t #l = function
  | [] -> 0
  | hd :: tl -> v hd + pow2 (bits t) * nat_from_intlist_le tl

val nat_from_intlist_be: #t:inttype{unsigned t} -> #l:secrecy_level -> list (uint_t t l) -> nat
let rec nat_from_intlist_be #t #l = function
  | [] -> 0
  | hd :: tl -> pow2 (FStar.List.Tot.Base.length tl * bits t) * v hd + nat_from_intlist_be tl
#pop-options


#push-options "--fuel 1"
val index_seq_of_list_cons: #a:Type -> x:a -> l:list a -> i:nat{i < List.Tot.length l} -> Lemma
  (Seq.index (Seq.seq_of_list (x::l)) (i+1) == Seq.index (Seq.seq_of_list l) i)

let index_seq_of_list_cons #a x l i =
  assert (Seq.index (Seq.seq_of_list (x::l)) (i+1) == List.Tot.index (x::l) (i+1))

val nat_from_intlist_seq_le: #t:inttype{unsigned t} -> #l:secrecy_level
  -> len:size_nat -> b:list (uint_t t l){List.Tot.length b = len}
  -> Lemma (nat_from_intlist_le b == BSeq.nat_from_intseq_le (LSeq.of_list b))

let rec nat_from_intlist_seq_le #t #l len b =
  match b with
  | [] -> ()
  | hd :: tl ->
    begin
    let s = LSeq.of_list b in
    Classical.forall_intro (index_seq_of_list_cons hd tl);
    assert (LSeq.equal (LSeq.of_list tl) (LSeq.slice s 1 len));
    assert (LSeq.index s 0 == List.Tot.index b 0);
    BSeq.nat_from_intseq_le_lemma0 (LSeq.slice s 0 1);
    BSeq.nat_from_intseq_le_slice_lemma s 1;
    nat_from_intlist_seq_le (len - 1) tl
    end


val nat_from_intlist_seq_be: #t: inttype {unsigned t} -> #l: secrecy_level
  -> len: size_nat -> b: list (uint_t t l) {FStar.List.Tot.Base.length b = len}
  -> Lemma (nat_from_intlist_be b == BSeq.nat_from_intseq_be (LSeq.of_list b))

let rec nat_from_intlist_seq_be #t #l len b =
  match b with
  | [] -> ()
  | hd :: tl ->
    begin
      let s = LSeq.of_list b in
      Classical.forall_intro (index_seq_of_list_cons hd tl);
      assert (LSeq.equal (LSeq.of_list tl) (LSeq.slice s 1 len));
      assert (LSeq.index s 0 == List.Tot.index b 0);
      nat_from_intlist_seq_be (len - 1) tl;
      BSeq.nat_from_intseq_be_lemma0 (LSeq.slice s 0 1);
      BSeq.nat_from_intseq_be_slice_lemma s 1
      end
#pop-options


unfold let order_inverse_list: list uint8 =
 [
   u8 79;  u8 37;  u8 99;  u8 252; u8 194; u8 202; u8 185; u8 243;
   u8 132; u8 158; u8 23;  u8 167; u8 173; u8 250; u8 230; u8 188;
   u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
   u8 0;   u8 0;   u8 0;   u8 0;   u8 255; u8 255; u8 255; u8 255
 ]


let order_inverse_seq: s:LSeq.lseq uint8 32{BSeq.nat_from_intseq_le s == S.order - 2} =
  assert_norm (List.Tot.length order_inverse_list == 32);
  nat_from_intlist_seq_le 32 order_inverse_list;
  assert_norm (nat_from_intlist_le order_inverse_list == S.order - 2);
  LSeq.of_list order_inverse_list


unfold let order_list: list uint8 =
 [
  u8 255; u8 255; u8 255; u8 255; u8 0;  u8 0;   u8 0;   u8 0;
  u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255; u8 255;
  u8 188; u8 230; u8 250; u8 173; u8 167; u8 23; u8 158; u8 132;
  u8 243; u8 185; u8 202; u8 194; u8 252; u8 99; u8 37; u8 81
 ]


let order_seq: s:LSeq.lseq uint8 32{BSeq.nat_from_intseq_be s == S.order} =
  assert_norm (List.Tot.length order_list == 32);
  nat_from_intlist_seq_be 32 order_list;
  assert_norm (nat_from_intlist_be order_list == S.order);
  LSeq.of_list order_list


// NOTE: used in Hacl.Impl.ECDSA.MM.Exponent.fst
let order_inverse_buffer: x: glbuffer uint8 32ul {witnessed x order_inverse_seq /\ recallable x} =
  createL_global order_inverse_list


let order_buffer: x: glbuffer uint8 32ul {witnessed x order_seq /\ recallable x} =
  createL_global order_list
