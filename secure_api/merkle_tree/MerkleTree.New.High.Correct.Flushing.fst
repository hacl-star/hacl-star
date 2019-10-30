module MerkleTree.New.High.Correct.Flushing

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec
open MerkleTree.New.High
open MerkleTree.New.High.Correct.Base

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

/// Correctness of flushing

val mt_flush_to_olds:
  lv:nat{lv < 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{j >= i /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv pi olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs pi j} ->
  GTot (folds:hash_ss{
         S.length folds = 32 /\
         S.equal (S.slice olds 0 lv) (S.slice folds 0 lv) /\
         mt_olds_inv lv i folds})
       (decreases i)
let rec mt_flush_to_olds lv pi i j olds hs =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then olds (* no updates *)
  else (let nolds = 
         S.upd olds lv
           (S.append (S.index olds lv)
                     (S.slice (S.index hs lv) 0 (oi - opi))) in
       mt_olds_inv_equiv (lv + 1) (pi / 2) olds nolds;
       mt_flush_to_olds (lv + 1) (pi / 2) (i / 2) (j / 2) nolds hs)

val mt_flush_to_olds_hs_equiv:
  lv:nat{lv < 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{j >= i /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv pi olds} ->
  hs1:hash_ss{S.length hs1 = 32 /\ hs_wf_elts lv hs1 pi j} ->
  hs2:hash_ss{S.length hs2 = 32 /\ hs_wf_elts lv hs2 pi j} ->
  Lemma (requires (S.equal (S.slice hs1 lv 32) (S.slice hs2 lv 32)))
        (ensures (S.equal (mt_flush_to_olds lv pi i j olds hs1)
                          (mt_flush_to_olds lv pi i j olds hs2)))
        (decreases i)
let rec mt_flush_to_olds_hs_equiv lv pi i j olds hs1 hs2 =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then ()
  else (assert (S.index hs1 lv == S.index hs2 lv);
       let nolds = 
         S.upd olds lv
           (S.append (S.index olds lv)
                     (S.slice (S.index hs1 lv) 0 (oi - opi))) in
       mt_olds_inv_equiv (lv + 1) (pi / 2) olds nolds;
       mt_flush_to_olds_hs_equiv
         (lv + 1) (pi / 2) (i / 2) (j / 2) nolds hs1 hs2)

val mt_flush_to_merge_preserved:
  lv:nat{lv < 32} ->
  pi:nat -> i:nat{i >= pi} ->
  j:nat{j >= i /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv pi olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs pi j} ->
  Lemma (requires True)
        (ensures (S.equal (merge_hs olds hs)
                          (merge_hs
                            (mt_flush_to_olds lv pi i j olds hs) 
                            (mt_flush_to_ lv hs pi i j))))
        (decreases i)
#reset-options "--z3rlimit 40 --max_fuel 2"
let rec mt_flush_to_merge_preserved lv pi i j olds hs =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then ()
  else begin
    let nolds = S.upd olds lv
                  (S.append (S.index olds lv)
                    (S.slice (S.index hs lv) 0 (oi - opi))) in
    let nhs = S.upd hs lv
                (S.slice (S.index hs lv) (oi - opi) (j - opi)) in
    mt_olds_inv_equiv (lv + 1) (pi / 2) olds nolds;
    hs_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
    mt_flush_to_merge_preserved
      (lv + 1) (pi / 2) (i / 2) (j / 2) nolds nhs;
    mt_flush_to_olds_hs_equiv
      (lv + 1) (pi / 2) (i / 2) (j / 2) nolds hs nhs;
    assert (S.equal (merge_hs nolds nhs)
                    (merge_hs
                      (mt_flush_to_olds lv pi i j olds hs)
                      (mt_flush_to_ lv hs pi i j)));
    merge_hs_upd olds hs lv
      (S.append (S.index olds lv) (S.slice (S.index hs lv) 0 (oi - opi)))
      (S.slice (S.index hs lv) (oi - opi) (j - opi));
    assert (S.equal (merge_hs olds hs) (merge_hs nolds nhs))
  end
#reset-options

val mt_flush_to_inv_preserved_:
  lv:nat{lv < 32} ->
  pi:nat -> i:nat{i >= pi} ->
  j:nat{j >= i /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv pi olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs pi j} ->
  Lemma (requires (mt_olds_hs_inv lv pi j olds hs))
        (ensures (mt_olds_hs_inv lv i j 
                   (mt_flush_to_olds lv pi i j olds hs) 
                   (mt_flush_to_ lv hs pi i j)))
let mt_flush_to_inv_preserved_ lv pi i j olds hs =
  mt_flush_to_merge_preserved lv pi i j olds hs;
  mt_olds_hs_lth_inv_ok lv pi j olds hs;
  mt_hashes_lth_inv_equiv lv j
    (merge_hs olds hs)
    (merge_hs (mt_flush_to_olds lv pi i j olds hs) 
              (mt_flush_to_ lv hs pi i j));
  mt_hashes_inv_equiv lv j
    (merge_hs olds hs)
    (merge_hs (mt_flush_to_olds lv pi i j olds hs) 
              (mt_flush_to_ lv hs pi i j))

val mt_flush_to_inv_preserved:
  mt:merkle_tree{mt_wf_elts mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  idx:nat{idx >= MT?.i mt /\ idx < MT?.j mt} ->
  Lemma (requires (mt_inv mt olds))
        (ensures (mt_inv (mt_flush_to mt idx)
                         (mt_flush_to_olds 0 (MT?.i mt) idx (MT?.j mt) olds (MT?.hs mt))))
let mt_flush_to_inv_preserved mt olds idx =
  mt_flush_to_inv_preserved_ 0 (MT?.i mt) idx (MT?.j mt) olds (MT?.hs mt);
  mt_flush_to_merge_preserved 0 (MT?.i mt) idx (MT?.j mt) olds (MT?.hs mt)

val mt_flush_inv_preserved:
  mt:merkle_tree{mt_wf_elts mt /\ MT?.j mt > MT?.i mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  Lemma (requires (mt_inv mt olds))
        (ensures (mt_inv (mt_flush mt)
                         (mt_flush_to_olds
                           0 (MT?.i mt) (MT?.j mt - 1) (MT?.j mt)
                           olds (MT?.hs mt))))
let mt_flush_inv_preserved mt olds =
  mt_flush_to_inv_preserved mt olds (MT?.j mt - 1)

