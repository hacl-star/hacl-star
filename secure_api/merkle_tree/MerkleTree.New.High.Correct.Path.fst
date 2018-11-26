module MerkleTree.New.High.Correct.Path

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec
open MerkleTree.New.High
open MerkleTree.New.High.Correct.Base
// Need to use some facts of `mt_get_root`
open MerkleTree.New.High.Correct.Rhs 

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

#reset-options "--z3rlimit 10" // default for this file

/// Correctness of path generation

val path_spec:
  k:nat ->
  j:nat{k <= j} ->
  actd:bool ->
  p:path{S.length p = mt_path_length k j actd} ->
  GTot (sp:S.seq MTS.hash{S.length sp = log2c j})
       (decreases (S.length p))
#reset-options "--z3rlimit 20"
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

val mt_get_path_step_acc:
  j:nat{j > 0} ->
  chs:hash_seq{S.length chs = j} ->
  crh:hash ->
  k:nat{k <= j} ->
  actd:bool ->
  GTot (option hash)
let mt_get_path_step_acc j chs crh k actd =
  if k % 2 = 1
  then Some (S.index chs (k - 1))
  else (if k = j then None
       else if k + 1 = j
	    then (if actd then Some crh else None)
	    else Some (S.index chs (k + 1)))

val mt_get_path_acc:
  j:nat ->
  fhs:hash_ss{S.length fhs = log2c j /\ mt_hashes_lth_inv_log j fhs} ->
  rhs:hash_seq{S.length rhs = log2c j} ->
  k:nat{k <= j} ->
  actd:bool ->
  GTot (np:path{S.length np = mt_path_length k j actd})
       (decreases j)
#reset-options "--z3rlimit 20"
let rec mt_get_path_acc j fhs rhs k actd =
  if j = 0 then S.empty
  else 
    (let sp = mt_get_path_step_acc j (S.head fhs) (S.head rhs) k actd in
    let rp = mt_get_path_acc (j / 2) (S.tail fhs) (S.tail rhs) (k / 2)
                             (actd || j % 2 = 1) in
    if Some? sp 
    then (S.cons (Some?.v sp) rp)
    else rp)

val mt_get_path_step_acc_consistent:
  lv:nat{lv <= 32} ->
  i:nat -> 
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  Lemma (requires (j <> 0))
        (ensures
          (log2c_bound j (32 - lv);
          mt_olds_hs_lth_inv_ok lv i j olds hs;
          mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
          (match mt_get_path_step_acc j
                   (S.index (merge_hs olds hs) lv) (S.index rhs lv)
                   k actd with
          | Some v -> 
            S.equal (mt_get_path_step lv hs rhs i j k p actd) (path_insert p v)
          | None -> 
            S.equal (mt_get_path_step lv hs rhs i j k p actd) p)))
let mt_get_path_step_acc_consistent lv i j olds hs rhs k p actd = ()

val mt_get_path_acc_consistent:
  lv:nat{lv <= 32} ->
  i:nat -> 
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  Lemma (requires True)
        (ensures
          (log2c_bound j (32 - lv);
          mt_olds_hs_lth_inv_ok lv i j olds hs;
          mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
          S.equal (mt_get_path_acc j 
                    (S.slice (merge_hs olds hs) lv (lv + log2c j))
                    (S.slice rhs lv (lv + log2c j)) k actd)
                  (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                    (S.length p) (S.length p + mt_path_length k j actd))))
        (decreases j)
#reset-options "--z3rlimit 20 --max_fuel 1"
let rec mt_get_path_acc_consistent lv i j olds hs rhs k p actd =
  log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);

  if j = 0 then ()
  else begin
    mt_get_path_step_acc_consistent lv i j olds hs rhs k p actd;
    mt_get_path_acc_consistent (lv + 1) (i / 2) (j / 2)
      olds hs rhs (k / 2) (mt_get_path_step lv hs rhs i j k p actd)
      (if j % 2 = 0 then actd else true);

    // (match mt_get_path_step_acc j (S.index (merge_hs olds hs) lv) 
    //         (S.index rhs lv) k actd with
    // | Some v -> begin
    //   assert (S.equal (mt_get_path_step lv hs rhs i j k p actd) (path_insert p v));
    //   assert (S.equal (mt_get_path_ lv hs rhs i j k p actd)
    //                   (mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2)
    //                                 (path_insert p v)
    //                                 (if j % 2 = 0 then actd else true)))
    // end
    // | None -> begin
    //   assert (S.equal (mt_get_path_step lv hs rhs i j k p actd) p);
    //   assert (S.equal (mt_get_path_ lv hs rhs i j k p actd)
    //                   (mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) p
    //                                 (if j % 2 = 0 then actd else true)))
    // end);
    admit ()
  end
#reset-options "--z3rlimit 10"

val mt_get_path_acc_inv_ok:
  j:nat ->
  fhs:hash_ss{S.length fhs = log2c j} ->
  rhs:hash_seq{S.length rhs = log2c j} ->
  k:nat{k <= j} ->
  acc:hash -> actd:bool ->
  Lemma (requires (j > 0 /\
                  mt_hashes_lth_inv_log j fhs /\
                  mt_hashes_inv_log j fhs /\
                  mt_rhs_inv j (hash_seq_spec_full (S.head fhs) acc actd) rhs actd))
        (ensures (S.equal (path_spec k j actd (mt_get_path_acc j fhs rhs k actd))
                          (MTS.mt_get_path #(log2c j)
                            (hash_seq_spec_full (S.head fhs) acc actd) k)))
        (decreases j)
let mt_get_path_acc_inv_ok j fhs rhs k acc actd =
  admit ()

val mt_get_path_inv_ok_:
  lv:nat{lv <= 32} ->
  i:nat -> 
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  acc:hash -> actd:bool ->
  Lemma (requires (log2c_bound j (32 - lv);
                  mt_olds_hs_lth_inv_ok lv i j olds hs;
                  (j > 0 /\
                  mt_hashes_inv lv j (merge_hs olds hs) /\
                  mt_rhs_inv j 
                    (hash_seq_spec_full (S.index (merge_hs olds hs) lv) acc actd)
                    (S.slice rhs lv (lv + log2c j)) actd)))
        (ensures (S.equal (path_spec k j actd 
                            (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                              (S.length p) (S.length p + mt_path_length k j actd)))
                          (MTS.mt_get_path #(log2c j)
                            (hash_seq_spec_full
                              (S.index (merge_hs olds hs) lv) acc actd) k)))
let mt_get_path_inv_ok_ lv i j olds hs rhs k p acc actd =
  log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
  mt_hashes_inv_log_converted_ lv j (merge_hs olds hs);

  mt_get_path_acc_consistent lv i j olds hs rhs k p actd;
  mt_get_path_acc_inv_ok j 
    (S.slice (merge_hs olds hs) lv (lv + log2c j))
    (S.slice rhs lv (lv + log2c j))
    k acc actd

val mt_get_path_inv_ok:
  mt:merkle_tree{mt_wf_elts mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  idx:nat{MT?.i mt <= idx && idx < MT?.j mt} ->
  drt:hash ->
  Lemma (requires (MT?.j mt > 0 /\ mt_inv mt olds))
        (ensures (let j, p, rt = mt_get_path mt idx drt in
                 j == MT?.j mt /\
                 mt_root_inv (mt_base mt olds) hash_init false rt /\
                 S.head p == S.index (mt_base mt olds) idx /\
                 (assert (S.length (S.tail p) == mt_path_length idx (MT?.j mt) false);
                 S.equal (path_spec idx (MT?.j mt) false (S.tail p))
                         (MTS.mt_get_path #(log2c j) (mt_spec mt olds) idx))))
let mt_get_path_inv_ok mt olds idx drt =
  let j, p, rt = mt_get_path mt idx drt in
  mt_get_root_inv_ok mt drt olds;
  assert (j == MT?.j mt);
  assert (mt_root_inv (mt_base mt olds) hash_init false rt);

  let ofs = offset_of (MT?.i mt) in
  let umt, _ = mt_get_root mt drt in
  let ip = path_insert S.empty (S.index (mt_base mt olds) idx) in
  mt_get_path_unchanged 0 (MT?.hs umt) (MT?.rhs umt) 
    (MT?.i umt) (MT?.j umt) idx ip false;
  assert (S.head ip == S.head (S.slice p 0 (S.length ip)));
  assert (S.head ip == S.head p);
  assert (S.head p == S.index (mt_base mt olds) idx);

  assert (S.length (S.tail p) == mt_path_length idx (MT?.j mt) false);
  mt_get_path_inv_ok_ 0 (MT?.i umt) (MT?.j umt)
    olds (MT?.hs umt) (MT?.rhs umt) idx ip hash_init false

