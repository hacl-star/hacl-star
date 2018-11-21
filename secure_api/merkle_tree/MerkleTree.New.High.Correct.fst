module MerkleTree.New.High.Correct

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec
open MerkleTree.New.High

open FStar.Classical
open FStar.Mul
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

/// Invariants of high-level Merkle tree design

val mt_hashes_lth_inv:
  lv:nat{lv <= 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_hashes_lth_inv lv j fhs =
  if lv = 32 then true
  else (S.length (S.index fhs lv) == j /\
       mt_hashes_lth_inv (lv + 1) (j / 2) fhs)

val mt_hashes_next_rel:
  j:nat ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  GTot Type0
let mt_hashes_next_rel j hs nhs =
  forall (i:nat{i < j / 2}).
    S.index nhs i == 
    hash_2 (S.index hs (2 * i)) (S.index hs (2 * i + 1))

val mt_hashes_inv:
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32 /\ mt_hashes_lth_inv lv j fhs} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_hashes_inv lv j fhs =
  if lv = 31 then true
  else (mt_hashes_next_rel j (S.index fhs lv) (S.index fhs (lv + 1)) /\
       mt_hashes_inv (lv + 1) (j / 2) fhs)

val merge_hs:
  hs1:hash_ss ->
  hs2:hash_ss{S.length hs1 = S.length hs2} ->
  GTot (mhs:hash_ss{S.length mhs = S.length hs1})
       (decreases (S.length hs1))
let rec merge_hs hs1 hs2 =
  if S.length hs1 = 0 then S.empty
  else (S.cons (S.append (S.head hs1) (S.head hs2))
               (merge_hs (S.tail hs1) (S.tail hs2)))

val merge_hs_index:
  hs1:hash_ss ->
  hs2:hash_ss{S.length hs1 = S.length hs2} ->
  i:nat{i < S.length hs1} ->
  Lemma (requires True)
        (ensures (S.equal (S.index (merge_hs hs1 hs2) i)
                          (S.append (S.index hs1 i) (S.index hs2 i))))
        (decreases (S.length hs1))
        [SMTPat (S.index (merge_hs hs1 hs2) i)]
let rec merge_hs_index hs1 hs2 i =
  if S.length hs1 = 0 then ()
  else if i = 0 then ()
  else merge_hs_index (S.tail hs1) (S.tail hs2) (i - 1)

val mt_olds_inv:
  lv:nat{lv <= 32} ->
  i:nat ->
  olds:hash_ss{S.length olds = 32} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_olds_inv lv i olds =
  if lv = 32 then true
  else (let ofs = offset_of i in
       S.length (S.index olds lv) == ofs /\
       mt_olds_inv (lv + 1) (i / 2) olds)

val mt_olds_hs_lth_inv_ok:
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  Lemma (requires True)
        (ensures (mt_hashes_lth_inv lv j (merge_hs olds hs)))
        (decreases (32 - lv))
let rec mt_olds_hs_lth_inv_ok lv i j olds hs =
  if lv = 32 then ()
  else (mt_olds_hs_lth_inv_ok (lv + 1) (i / 2) (j / 2) olds hs)

val mt_olds_hs_inv:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  GTot Type0
let mt_olds_hs_inv lv i j olds hs =
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_inv lv j (merge_hs olds hs)

// joonwonc: some other invariants (e.g., about `MT?.rhs`) will be added later.
val mt_inv: 
  mt:merkle_tree{mt_wf_elts mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  GTot Type0
let mt_inv mt olds =
  mt_olds_hs_inv 0 (MT?.i mt) (MT?.j mt) olds (MT?.hs mt)

/// Correctness of insertion

assume val insert_hs_wf_elts:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (hs_wf_elts lv hs i j))
        (ensures (hs_wf_elts lv (insert_ lv i j hs acc) i (j + 1)))

val mt_insert_mt_wf_elts:
  mt:merkle_tree{mt_wf_elts mt /\ mt_not_full mt} ->
  v:hash ->
  Lemma (requires (mt_wf_elts mt))
        (ensures (mt_wf_elts (mt_insert mt v)))
let mt_insert_mt_wf_elts mt v =
  insert_hs_wf_elts 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v

val insert_inv_preserved:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (mt_olds_hs_inv lv i j olds hs))
        (ensures (insert_hs_wf_elts lv i j hs acc;
                 mt_olds_hs_inv lv i (j + 1) olds (insert_ lv i j hs acc)))
let rec insert_inv_preserved lv i j olds hs acc =
  admit ()

val mt_insert_inv_preserved:
  mt:merkle_tree{mt_wf_elts mt /\ mt_not_full mt} -> v:hash ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  Lemma (requires (mt_inv mt olds))
        (ensures (mt_insert_mt_wf_elts mt v;
                 mt_inv (mt_insert mt v) olds))
let mt_insert_inv_preserved mt v olds =
  insert_inv_preserved 0 (MT?.i mt) (MT?.j mt) olds (MT?.hs mt) v

/// Correctness of `mt_get_root` and `mt_get_path`

/// Correctness of flushing

/// Correctness of path verification


