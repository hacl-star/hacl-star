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

val hash_seq_spec_rel_equiv:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_seq ->
  hs:hash_seq{S.length hs = j - S.length olds} ->
  smt1:MTS.merkle_tree n -> smt2:MTS.merkle_tree n ->
  Lemma (requires (hash_seq_spec_rel j n olds hs smt1 /\
                  S.equal (S.slice smt1 0 j) (S.slice smt2 0 j)))
        (ensures (hash_seq_spec_rel j n olds hs smt2))
let hash_seq_spec_rel_equiv j n olds hs smt1 smt2 = ()

val hash_ss_length_spec:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n} ->
  GTot Type0
let rec hash_ss_length_spec j n olds hs =
  if n = 0 then true
  else (S.length (S.append (S.head olds) (S.head hs)) = j /\
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

val hash_ss_spec_rel_equiv:
  j:nat -> n:nat{j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  smt1:MTS.merkle_tree n -> smt2:MTS.merkle_tree n ->
  Lemma (requires (hash_ss_spec_rel j n olds hs smt1 /\
                  S.equal (S.slice smt1 0 j) (S.slice smt2 0 j)))
        (ensures (hash_ss_spec_rel j n olds hs smt2))
let rec hash_ss_spec_rel_equiv j n olds hs smt1 smt2 =
  if n = 0 then ()
  else (mt_next_lv_equiv j n smt1 smt2;
       hash_ss_spec_rel_equiv (j / 2) (n - 1) (S.tail olds) (S.tail hs)
                              (mt_next_lv smt1) (mt_next_lv smt2))

val hash_seq_lift_to_spec:
  fhs:hash_seq ->
  n:nat{S.length fhs <= pow2 n} ->
  GTot (MTS.merkle_tree n)
let hash_seq_lift_to_spec fhs n =
  S.append (hash_seq_lift fhs) (create_pads (pow2 n - S.length fhs))

val hash_seq_lift_to_spec_slice_eq:
  fhs1:hash_seq -> fhs2:hash_seq ->
  n:nat{S.length fhs1 <= pow2 n && S.length fhs2 <= pow2 n} ->
  i:nat{i <= S.length fhs1 && i <= S.length fhs2} ->
  Lemma (requires (S.equal (S.slice fhs1 0 i) (S.slice fhs2 0 i)))
        (ensures (S.equal (S.slice (hash_seq_lift_to_spec fhs1 n) 0 i)
                          (S.slice (hash_seq_lift_to_spec fhs2 n) 0 i)))
let hash_seq_lift_to_spec_slice_eq fhs1 fhs2 n i =
  admit ()

val hash_ss_spec_:
  j:nat -> n:nat{n > 0 && j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  GTot Type0
let hash_ss_spec_ j n olds hs =
  hash_ss_spec_rel j n olds hs 
    (hash_seq_lift_to_spec (S.append (S.head olds) (S.head hs)) n)

val hash_ss_spec_rec:
  j:nat -> n:nat{n > 1 && j <= pow2 n} ->
  olds:hash_ss{S.length olds = n} ->
  hs:hash_ss{S.length hs = n /\ hash_ss_length_spec j n olds hs} ->
  Lemma (requires (hash_ss_spec_ j n olds hs))
        (ensures (hash_ss_spec_ (j / 2) (n - 1) (S.tail olds) (S.tail hs)))
let hash_ss_spec_rec j n olds hs =
  let spec_base = hash_seq_lift_to_spec (S.append (S.head olds) (S.head hs)) n in
  assert (hash_seq_spec_rel (j / 2) (n - 1)
           (S.head (S.tail olds)) (S.head (S.tail hs)) (mt_next_lv spec_base));
  assert (S.equal (S.slice (mt_next_lv spec_base) 0 (j / 2))
                  (S.slice (hash_seq_lift_to_spec
                             (S.append (S.head (S.tail olds)) 
                                       (S.head (S.tail hs))) (n - 1)) 0 (j / 2)));
  hash_ss_spec_rel_equiv (j / 2) (n - 1) (S.tail olds) (S.tail hs)
    (mt_next_lv spec_base)
    (hash_seq_lift_to_spec 
      (S.append (S.head (S.tail olds)) (S.head (S.tail hs))) (n - 1))

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

private val seq_equal_slice_index:
  #a:Type -> 
  s1:S.seq a -> s2:S.seq a ->
  n:nat -> m:nat{n <= m && m <= S.length s1 && m <= S.length s2} ->
  i:nat{n <= i && i < m} ->
  Lemma (requires (S.equal (S.slice s1 n m) (S.slice s2 n m)))
        (ensures (S.index s1 i == S.index s2 i))
private let seq_equal_slice_index #a s1 s2 n m i =
  lemma_index_slice s1 n m (i - n);
  lemma_index_slice s2 n m (i - n)

private val seq_equal_slice_more:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  n:nat -> m:nat{n <= m && m <= S.length s1 && m <= S.length s2} ->
  k:nat{n <= k} -> l:nat{k <= l && l <= m} ->
  Lemma (requires (S.equal (S.slice s1 n m) (S.slice s2 n m)))
        (ensures (S.equal (S.slice s1 k l) (S.slice s2 k l)))
private let seq_equal_slice_more #a s1 s2 n m k l =
  slice_slice s1 n m (k - n) (l - n);
  slice_slice s2 n m (k - n) (l - n)

val hash_ss_insert_modified:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  v:hash ->
  Lemma (S.equal (S.slice hs 0 lv)
                 (S.slice (hash_ss_insert lv i j hs v) 0 lv) /\
        S.equal (S.slice hs (lv + 1) 32)
                 (S.slice (hash_ss_insert lv i j hs v) (lv + 1) 32) /\
        S.equal (S.index (hash_ss_insert lv i j hs v) lv)
                (S.snoc (S.index hs lv) v))
let hash_ss_insert_modified lv i j hs v = ()

val insert_modified:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires True)
        (ensures (S.equal (S.slice (insert_ lv i j hs acc) 0 lv)
                          (S.slice hs 0 lv)))
        (decreases j)
let rec insert_modified lv i j hs acc =
  let ihs = hash_ss_insert lv i j hs acc in
  hash_ss_insert_modified lv i j hs acc;
  if j % 2 = 1
  then (let nacc = hash_2 (S.last (S.index hs lv)) acc in
       insert_modified (lv + 1) (i / 2) (j / 2) ihs nacc;
       seq_equal_slice_more (insert_ (lv + 1) (i / 2) (j / 2) ihs nacc) ihs
         0 (lv + 1) 0 lv)
  else ()

val insert_head:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (S.equal (S.index (insert_ lv i j hs acc) lv)
                 (S.index (hash_ss_insert lv i j hs acc) lv))
let insert_head lv i j hs acc =
  if j % 2 = 1
  then (let ihs = hash_ss_insert lv i j hs acc in
       let nacc = hash_2 (S.last (S.index hs lv)) acc in
       assert (S.equal (S.index (insert_ lv i j hs acc) lv)
                       (S.index (insert_ (lv + 1) (i / 2) (j / 2) ihs nacc) lv));
       insert_modified (lv + 1) (i / 2) (j / 2) ihs nacc;
       assert (S.equal (S.slice (insert_ (lv + 1) (i / 2) (j / 2) ihs nacc) 0 (lv + 1))
                       (S.slice ihs 0 (lv + 1)));
       seq_equal_slice_index
         (insert_ (lv + 1) (i / 2) (j / 2) ihs nacc) ihs
         0 (lv + 1) lv
  )
  else ()

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
#reset-options "--z3rlimit 20 --max_fuel 1"
let rec insert_wf_spec lv i j hs acc olds =
  let ihs = insert_ lv i j hs acc in
  insert_head lv i j hs acc;
  hash_ss_insert_modified lv i j hs acc;
  let spec_base = 
    hash_seq_lift_to_spec
      (S.append (S.head olds) (S.index hs lv)) (32 - lv) in

  if j % 2 = 1
  then begin
    remainder_2_1_div j;
    admit ()
  end
  
  else begin
    remainder_2_not_1_div j;
    let ispec_base =
      hash_seq_lift_to_spec
        (S.append (S.head olds) (S.index ihs lv)) (32 - lv) in
    // Since original `olds` and `hs[lv]` are unchanged after the insertion,
    // below assertion holds.
    assert (S.equal (S.slice (S.append (S.head olds) (S.index hs lv)) 0 j)
                    (S.slice (S.append (S.head olds) (S.index ihs lv)) 0 j));
    hash_seq_lift_to_spec_slice_eq
      (S.append (S.head olds) (S.index hs lv))
      (S.append (S.head olds) (S.index ihs lv))
      (32 - lv) j;
    mt_next_lv_equiv j (32 - lv) spec_base ispec_base;
    hash_ss_spec_rel_equiv ((j + 1) / 2) (32 - (lv + 1))
      (S.tail olds) (S.slice ihs (lv + 1) 32)
      (mt_next_lv spec_base) (mt_next_lv ispec_base)
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


