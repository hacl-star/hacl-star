module MerkleTree.New.High.Correct.Path

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

/// Correctness of path generation

val path_spec:
  k:nat ->
  j:nat{k <= j} ->
  actd:bool ->
  p:path{S.length p = mt_path_length k j actd} ->
  GTot (sp:S.seq MTS.hash{S.length sp = log2c j})
       (decreases (S.length p))
#reset-options "--z3rlimit 10"
let rec path_spec k j actd p =
  if S.length p = 0 then S.empty
  else if j = 0 then S.empty
  else (S.cons
         (if k % 2 = 0
         then (if j = k || (j = k + 1 && not actd) 
              then HPad else HRaw (S.head p))
         else HRaw (S.head p))
         (path_spec (k / 2) (j / 2) (actd || (j % 2 = 1)) (S.tail p)))
#reset-options

// val mt_get_path_acc:
//   i:nat -> 
//   j:nat{i <= j} ->
//     hs_wf_elts lv hs i j} ->
//   hs:hash_ss{S.length hs = 32} ->
//   rhs:hash_seq{S.length rhs = 32} ->
//   k:nat{i <= k && k <= j} ->
//   p:path ->
//   actd:bool ->
//   GTot (np:path{S.length np = S.length p + mt_path_length k j actd})
//        (decreases (32 - lv))

// #reset-options "--z3rlimit 10"
// val mt_get_path_sim:
//   lv:nat{lv <= 32} ->
//   i:nat -> 
//   j:nat{i <= j /\ j < pow2 (32 - lv)} ->
//   olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
//   hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
//   rhs:hash_seq{S.length rhs = 32} ->
//   k:nat{i <= k && k <= j} ->
//   p:path ->
//   actd:bool ->
//   Lemma (requires (j > 0))
//         (ensures (mt_olds_hs_lth_inv_ok lv i j olds hs;
//                  S.equal (path_spec k j actd
//                            (S.slice (mt_get_path_ lv hs rhs i j k p actd)
//                            (S.length p) (S.length p + mt_path_length k j actd)))
//                          (MTS.mt_get_path #(log2c j)
//                            (hash_seq_spec (S.index (merge_hs olds hs) lv)) k)))
//         (decreases j)
  

