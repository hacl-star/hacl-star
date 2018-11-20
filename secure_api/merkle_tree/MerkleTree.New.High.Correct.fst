module MerkleTree.New.High.Correct

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec
open MerkleTree.New.High

open FStar.Classical
open FStar.Ghost
open FStar.Seq

module List = FStar.List.Tot
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

module EHS = EverCrypt.Hash
module MTS = MerkleTree.Spec

/// Facts about "2"

val remainder_2_not_1_div:
  n:nat -> 
  Lemma (requires (n % 2 <> 1))
        (ensures (n / 2 = (n + 1) / 2))
let remainder_2_not_1_div n = ()

val remainder_2_1_div:
  n:nat -> 
  Lemma (requires (n % 2 = 1))
        (ensures (n / 2 + 1 = (n + 1) / 2))
let remainder_2_1_div n = ()  

// val is_pow2: n:nat -> GTot bool
// let rec is_pow2 n =
//   if n = 0 then false
//   else if n = 1 then true
//   else if n % 2 = 0 then is_pow2 (n / 2)
//   else false

// val pow2_ceil: 
//   n:nat -> GTot (c:nat{n <= pow2 c})
// let rec pow2_ceil n =
//   if n <= 1 then 0
//   else 1 + pow2_ceil ((n + 1) / 2)

// val pow2_is_pow2: 
//   n:nat -> Lemma (is_pow2 (pow2 n)) [SMTPat (pow2 n)]
// let rec pow2_is_pow2 n =
//   if n = 0 then () else pow2_is_pow2 (n-1)

// val pow2_ceil_inc_1:
//   n:nat ->
//   Lemma (requires (not (is_pow2 n)))
//         (ensures (pow2_ceil n = pow2_ceil (n + 1)))
// #reset-options "--z3rlimit 10"
// let rec pow2_ceil_inc_1 n =
//   if n <= 1 then ()
//   else if n % 2 = 0 then pow2_ceil_inc_1 (n / 2)
//   else (assert (pow2_ceil n = 1 + pow2_ceil ((n + 1) / 2));
//        assert (pow2_ceil (n + 1) = 1 + pow2_ceil (n / 2 + 1)))

// val pow2_ceil_inc_2:
//   n:nat ->
//   Lemma (requires (is_pow2 n))
//         (ensures (pow2_ceil n + 1 = pow2_ceil (n + 1)))
// let rec pow2_ceil_inc_2 n =
//   if n <= 1 then ()
//   else if n % 2 = 0 
//   then (assert (pow2_ceil n = 1 + pow2_ceil (n / 2));
//        assert (pow2_ceil (n + 1) = 1 + pow2_ceil (n / 2 + 1));
//        pow2_ceil_inc_2 (n / 2))
//   else ()

/// Connection to Merkle tree specification

// It is more natural to have a *relation* between a high-level Merkle tree and
// a spec, since the high-level does not hold some elements that are never used
// for generating Merkle paths, e.g., rightmost hashes (`MT?.rhs`). Even with
// `MT?.rhs` the high-level design is not equal to a full Merkle tree with some
// right paddings.
//
// For example, when `MT?.j = 5`, `MT?.hs` has hashes below:
// ----------------------------|
//       | [0] [1] [2] [3] [4] |
// hs[2] | h03                 |
// hs[1] | h01 h23             |
// hs[0] | h0  h1  h2  h3  h4  |
// -----------------------------
// After calculating rightmost hashes, `MT?.rhs` has hashes below:
// ------------|
// rhs[2] | h4 |
// rhs[1] | .  |
// rhs[0] | .  |
// ------------|
// The spec has hashes and right-pads below (P is a pad):
// ----------------------------------------|
// spec[3] | h04                           |
// spec[2] | h03 h4                        |
// spec[1] | h01 h23 h4  P                 |
// spec[0] | h0  h1  h2  h3  h4  P   P   P |
// ----------------------------------------|
// This is intuitively because `MT?.hs` and `MT?.rhs` have minimal required 
// hashes to calculate Merkle paths for {h0, ..., h5}.
//

val hash_seq_lift: 
  hs:hash_seq -> 
  GTot (shs:MTS.hash_seq{S.length shs = S.length hs})
       (decreases (S.length hs))
let rec hash_seq_lift hs =
  if S.length hs = 0 then S.empty
  else S.cons (HRaw (S.head hs)) (hash_seq_lift (S.tail hs))

val create_pads: len:nat -> GTot (pads:MTS.hash_seq{S.length pads = len})
let create_pads len = S.create len HPad

val hash_seq_spec_rel:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_seq ->
  hs:hash_seq{S.length hs = j - S.length olds} ->
  smt:MTS.merkle_tree n ->
  GTot Type0
let hash_seq_spec_rel j n olds hs smt =
  S.equal (hash_seq_lift (S.append olds hs))
          (S.slice smt 0 j)

val hash_ss_length_spec:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n} ->
  GTot Type0
let rec hash_ss_length_spec j n olds hs =
  if n = 0 then true
  else (S.length (S.head hs) = j - S.length (S.head olds) /\
       hash_ss_length_spec (j / 2) (n - 1) (S.tail olds) (S.tail hs))

val hash_ss_spec_rel:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  smt:MTS.merkle_tree n ->
  GTot Type0
let rec hash_ss_spec_rel j n olds hs smt =
  if n = 0 then true
  else (hash_seq_spec_rel j n (S.head olds) (S.head hs) smt /\
       hash_ss_spec_rel (j / 2) (n - 1) 
         (S.tail olds) (S.tail hs) (mt_next_lv smt))

val hash_seq_lift_to_spec:
  fhs:hash_seq ->
  n:nat{S.length fhs <= pow2 n} ->
  GTot (MTS.merkle_tree n)
let hash_seq_lift_to_spec fhs n =
  S.append (hash_seq_lift fhs) (create_pads (pow2 n - S.length fhs))

val hash_ss_spec_:
  j:nat -> n:nat{n > 0 && j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  GTot Type0
let hash_ss_spec_ j n olds hs =
  hash_ss_spec_rel j n olds hs 
    (hash_seq_lift_to_spec (S.append (S.head olds) (S.head hs)) n)

// TODO: make a pure `exists` term for better elimination.
val hash_ss_spec:
  j:nat -> n:nat{j <= pow2 n} ->
  hs:hash_ss{S.length hs = n} ->
  GTot Type0
let hash_ss_spec j n hs =
  if n = 0 then True
  else begin
    exists (olds:hash_ss{S.length olds = n}).
      hash_ss_length_spec j n olds hs /\
      hash_ss_spec_ j n olds hs
  end

val hash_ss_spec_intro:
  j:nat -> n:nat{n > 0 && j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  Lemma (requires (hash_ss_spec_ j n olds hs))
        (ensures (hash_ss_spec j n hs))
let hash_ss_spec_intro j n olds hs =
  exists_intro
    (fun (olds:hash_ss{S.length olds = n /\ hash_ss_length_spec j n olds hs}) ->
      hash_ss_spec_ j n olds hs) olds

// val hash_ss_spec_elim:
//   j:nat -> n:nat{n > 0 && j <= pow2 n} ->
//   hs:hash_ss{S.length hs = n} ->
//   goal:Type0 ->
//   ex:(
//     olds:hash_ss{S.length olds = n /\ hash_ss_length_spec j n olds hs} ->
//     goal) ->
//   Lemma (requires (hash_ss_spec j n hs))
//         (ensures goal)
// let hash_ss_spec_elim j n hs goal ex =

// joonwonc: which is better: to calculate `n` from `j` or just `n = 32`?
val mt_wf_spec: mt:merkle_tree{mt_not_empty mt} -> GTot Type0
let mt_wf_spec mt =
  hash_ss_spec (MT?.j mt) 32 (MT?.hs mt)

/// Correctness of insertion

val insert_wf_spec:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  olds:hash_ss{S.length olds = 32 - lv} ->
  Lemma (requires (hash_ss_length_spec j (32 - lv) olds (S.slice hs lv 32) /\
                  hash_ss_spec_ j (32 - lv) olds (S.slice hs lv 32)))
        (ensures (hash_ss_length_spec (j + 1) (32 - lv) olds
                   (S.slice (insert_ lv i j hs acc) lv 32) /\
                 hash_ss_spec_ (j + 1) (32 - lv) olds
                   (S.slice (insert_ lv i j hs acc) lv 32)))
        (decreases j)
#reset-options "--z3rlimit 10 --max_fuel 1"
let rec insert_wf_spec lv i j hs acc olds =
  let ihs = insert_ lv i j hs acc in
  if j % 2 = 1
  then begin
    remainder_2_1_div j;
    // let nacc = hash_2 (S.last (S.index hs lv)) acc in
    // insert_wf_spec (lv + 1) (i / 2) (j / 2) hs nacc (S.tail olds);
    admit ()
  end
  else begin
    remainder_2_not_1_div j;
    assert (S.equal (S.slice hs (lv + 1) 32) (S.slice ihs (lv + 1) 32));
    let spec_base = hash_seq_lift_to_spec
                      (S.append (S.head olds) (S.index hs lv)) (32 - lv) in
    assert (hash_seq_spec_rel j (32 - lv) 
             (S.head olds) (S.index hs lv) spec_base);
    assert (hash_ss_spec_rel (j / 2) (32 - (lv + 1)) 
             (S.tail olds) (S.slice hs (lv + 1) 32)
             (mt_next_lv spec_base));
    assert (hash_ss_spec_rel ((j + 1) / 2) (32 - (lv + 1)) 
             (S.tail olds) (S.slice (insert_ lv i j hs acc) (lv + 1) 32)
             (mt_next_lv spec_base));
    let ispec_base = hash_seq_lift_to_spec
                        (S.append (S.head olds) (S.index ihs lv)) (32 - lv) in
    assume (hash_ss_spec_rel ((j + 1) / 2) (32 - (lv + 1)) 
             (S.tail olds) (S.slice (insert_ lv i j hs acc) (lv + 1) 32)
             (mt_next_lv ispec_base))
  end

// val mt_insert_wf_spec_0:
//   mt:merkle_tree{mt_wf_elts mt /\ mt_empty mt} ->
//   v:hash ->
//   Lemma (mt_wf_spec (mt_insert mt v))
// let mt_insert_wf_spec_0 mt v =
//   admit ()

// val mt_insert_wf_spec_1:
//   mt:merkle_tree{mt_wf_elts mt /\ mt_not_empty mt /\ mt_not_full mt} ->
//   v:hash ->
//   Lemma (requires (mt_wf_spec mt))
//         (ensures (mt_wf_spec (mt_insert mt v)))
// let mt_insert_wf_spec_1 mt v =
//   exists_elim
//     (mt_wf_spec (mt_insert mt v))
//     #(olds:hash_ss{S.length olds = 32})
//     #(fun (olds:hash_ss{S.length olds = 32}) ->
//         hash_ss_length_spec (MT?.j mt) 32 olds (MT?.hs mt) /\
//         hash_ss_spec_ (MT?.j mt) 32 olds (MT?.hs mt))
//     (mt_wf_spec mt)
//     (fun olds -> 
//       insert_wf_spec 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v olds)

// val mt_insert_wf_spec:
//   mt:merkle_tree{mt_wf_elts mt /\ mt_not_full mt} ->
//   v:hash ->
//   Lemma (requires (mt_empty mt \/ mt_wf_spec mt))
//         (ensures (mt_wf_spec (mt_insert mt v)))
// let mt_insert_wf_spec mt v =
//   if mt_empty mt
//   then mt_insert_wf_spec_0 mt v
//   else mt_insert_wf_spec_1 mt v

/// Correctness of `mt_get_root` and `mt_get_path`

/// Correctness of flushing

/// Correctness of path verification


