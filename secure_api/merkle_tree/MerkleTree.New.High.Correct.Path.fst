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

#reset-options "--z3rlimit 20" // default for this file

/// Correctness of path generation

val path_spec:
  k:nat ->
  j:nat{k <= j} ->
  actd:bool ->
  p:path{S.length p = mt_path_length k j actd} ->
  GTot (sp:S.seq MTS.hash{S.length sp = log2c j})
       (decreases j)
let rec path_spec k j actd p =
  if j = 0 then S.empty
  else (if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd)
            then S.cons HPad (path_spec (k / 2) (j / 2) (actd || (j % 2 = 1)) p)
            else S.cons (HRaw (S.head p))
                   (path_spec (k / 2) (j / 2) (actd || (j % 2 = 1)) (S.tail p)))
       else S.cons (HRaw (S.head p))
              (path_spec (k / 2) (j / 2) (actd || (j % 2 = 1)) (S.tail p)))

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
            S.equal (mt_get_path_step lv hs rhs i j k S.empty actd)
                    (S.cons v S.empty)
          | None ->
            S.equal (mt_get_path_step lv hs rhs i j k S.empty actd)
                    S.empty)))
let mt_get_path_step_acc_consistent lv i j olds hs rhs k actd = ()

private val seq_cons_append:
  #a:Type -> hd:a -> tl:S.seq a ->
  Lemma (S.equal (S.append (S.cons hd S.empty) tl)
                 (S.cons hd tl))
private let seq_cons_append #a hd tl = ()

val mt_get_path_acc_consistent:
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  k:nat{i <= k && k <= j} ->
  actd:bool ->
  Lemma (requires True)
        (ensures
          (log2c_bound j (32 - lv);
          mt_olds_hs_lth_inv_ok lv i j olds hs;
          mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
          S.equal (mt_get_path_acc j
                    (S.slice (merge_hs olds hs) lv (lv + log2c j))
                    (S.slice rhs lv (lv + log2c j)) k actd)
                  (mt_get_path_ lv hs rhs i j k S.empty actd)))
        (decreases j)

#reset-options "--z3rlimit 800 --max_fuel 1 --max_ifuel 0"
let rec mt_get_path_acc_consistent lv i j olds hs rhs k actd =
  log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);

  if j = 0 then ()
  else begin
    let nactd = if j % 2 = 0 then actd else true in
    let nactd_ = actd || j % 2 = 1 in
    assert (nactd == nactd_);

    let pa = mt_get_path_acc j
               (S.slice (merge_hs olds hs) lv (lv + log2c j))
               (S.slice rhs lv (lv + log2c j)) k actd in
    let p = mt_get_path_ lv hs rhs i j k S.empty actd in

    log2c_div j; log2c_bound (j / 2) (32 - (lv + 1));
    assert (mt_hashes_lth_inv (lv + 1) (j / 2) (merge_hs olds hs));
    assert (mt_hashes_lth_inv_log (j / 2)
             (S.slice (merge_hs olds hs) (lv + 1) (lv + 1 + log2c (j / 2))));
    let npsa = mt_get_path_step_acc j
                 (S.index (merge_hs olds hs) lv) (S.index rhs lv) k actd in
    let npa = mt_get_path_acc (j / 2)
                (S.slice (merge_hs olds hs) (lv + 1) (lv + 1 + log2c (j / 2)))
                (S.slice rhs (lv + 1) (lv + 1 + log2c (j / 2))) (k / 2) nactd_ in
    let nps = mt_get_path_step lv hs rhs i j k S.empty actd in
    let np = mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) nps nactd in
    let npe = mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) S.empty nactd in
    mt_get_path_pull (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) nps nactd;
    assert (S.equal p np);
    assert (S.equal np (S.append nps npe));
    assert (S.equal p (S.append nps npe));
    assert (S.equal pa (if Some? npsa
                       then S.cons (Some?.v npsa) npa
                       else npa));

    mt_get_path_acc_consistent (lv + 1) (i / 2) (j / 2)
      olds hs rhs (k / 2) nactd;
    assert (S.equal npa npe);

    mt_get_path_step_acc_consistent lv i j olds hs rhs k actd;
    if Some? npsa
    then begin
      assert (S.equal nps (S.cons (Some?.v npsa) S.empty));
      assert (S.equal p (S.append (S.cons (Some?.v npsa) S.empty) npa));
      assert (S.equal pa (S.cons (Some?.v npsa) npa));
      seq_cons_append (Some?.v npsa) npa;
      assert (S.equal pa p)
    end
    else begin
      assert (S.equal nps S.empty);
      S.append_empty_l npe;
      assert (S.equal p npe);
      assert (S.equal pa npa);
      assert (S.equal pa p)
    end
  end
#reset-options "--z3rlimit 20"

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
#reset-options "--z3rlimit 80 --max_fuel 1"
let rec mt_get_path_acc_inv_ok j fhs rhs k acc actd =
  // Below dummy `let` is necessary to provide guidance to the SMT solver.
  let _ = mt_get_path_step_acc j (S.head fhs) (S.head rhs) k actd in
  let smt = hash_seq_spec_full (S.head fhs) acc actd in
  let nacc = (if j % 2 = 0 then acc
             else if actd
             then hash_2 (S.last (S.head fhs)) acc
             else S.last (S.head fhs)) in
  let nactd = actd || j % 2 = 1 in

  if j = 1 then (if k = 0 then () else ())
  else begin
    mt_hashes_lth_inv_log_next j fhs;
    hash_seq_spec_full_next j (S.head fhs) (S.head (S.tail fhs)) acc actd nacc nactd;
    mt_get_path_acc_inv_ok (j / 2) (S.tail fhs) (S.tail rhs) (k / 2) nacc nactd;
    if k % 2 = 0
    then begin
      if k = j || (k + 1 = j && not actd)
      then assert (S.index smt (k + 1) == HPad)
      else if k + 1 = j
      then assert (S.index smt (k + 1) == HRaw (S.head rhs))
      else hash_seq_spec_full_index_raw (S.head fhs) acc actd (k + 1)
    end
    else begin
      hash_seq_spec_full_index_raw (S.head fhs) acc actd (k - 1)
    end
  end

#reset-options "--max_fuel 1 --initial_fuel 1 --max_ifuel 0 --z3rlimit 60"
val mt_get_path_inv_ok_:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{j > 0 /\ i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  acc:hash -> actd:bool ->
  Lemma (requires (log2c_div j; log2c_bound j (32 - lv);
                  mt_olds_hs_lth_inv_ok lv i j olds hs;
                  (mt_hashes_inv lv j (merge_hs olds hs) /\
		  (let t1 = hash_seq_spec_full (S.index (merge_hs olds hs) lv) acc actd in
		   let t2 = S.slice rhs lv (lv + log2c j) in
                   mt_rhs_inv j t1 t2 actd))))
        (ensures (S.equal (path_spec k j actd
                            (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                              (S.length p) (S.length p + mt_path_length k j actd)))
                          (MTS.mt_get_path #(log2c j)
                            (hash_seq_spec_full
                              (S.index (merge_hs olds hs) lv) acc actd) k)))
#reset-options "--z3rlimit 40 --max_fuel 0"
let mt_get_path_inv_ok_ lv i j olds hs rhs k p acc actd =
  log2c_div j; log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
  mt_hashes_inv_log_converted_ lv j (merge_hs olds hs);

  mt_get_path_acc_consistent lv i j olds hs rhs k actd;
  mt_get_path_slice lv hs rhs i j k p actd;
  mt_get_path_acc_inv_ok j
    (S.slice (merge_hs olds hs) lv (lv + log2c j))
    (S.slice rhs lv (lv + log2c j))
    k acc actd
#reset-options "--z3rlimit 20"

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
#reset-options "--z3rlimit 40"
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

val mt_verify_ok_:
  k:nat ->
  j:nat{k <= j} ->
  p:path ->
  ppos:nat ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (ppos + mt_path_length k j actd <= S.length p))
        (ensures (HRaw (mt_verify_ k j p ppos acc actd) ==
                 MTS.mt_verify_ #(log2c j)
                   (path_spec k j actd
                     (S.slice p ppos (ppos + mt_path_length k j actd)))
                   k (HRaw acc)))
        (decreases j)
#reset-options "--z3rlimit 40 --max_fuel 1"
let rec mt_verify_ok_ k j p ppos acc actd =
  if j = 0 then ()
  else begin
    log2c_div j;
    let vi = mt_verify_ k j p ppos acc actd in
    let plen = mt_path_length k j actd in
    let vs = MTS.mt_verify_ #(log2c j)
               (path_spec k j actd (S.slice p ppos (ppos + plen)))
               k (HRaw acc) in
    let nactd = actd || (j % 2 = 1) in
    let nplen = mt_path_length (k / 2) (j / 2) nactd in

    if k % 2 = 0
    then begin
      if j = k || (j = k + 1 && not actd)
      then begin
        assert (vi == mt_verify_ (k / 2) (j / 2) p ppos acc nactd);
        assert (plen == nplen);
        assert (S.equal (path_spec k j actd (S.slice p ppos (ppos + plen)))
                        (S.cons HPad
                          (path_spec (k / 2) (j / 2) nactd
                            (S.slice p ppos (ppos + plen)))));
        assert (vs ==
               MTS.mt_verify_ #(log2c (j / 2))
                 (path_spec (k / 2) (j / 2) nactd (S.slice p ppos (ppos + plen)))
                 (k / 2) (HRaw acc));
        mt_verify_ok_ (k / 2) (j / 2) p ppos acc nactd
      end
      else begin
        let nacc = hash_2 acc (S.index p ppos) in
        assert (vi == mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd);
        assert (plen == nplen + 1);
        assert (S.equal (S.tail (S.slice p ppos (ppos + plen)))
                        (S.slice p (ppos + 1) (ppos + 1 + nplen)));
        assert (S.equal (path_spec k j actd (S.slice p ppos (ppos + plen)))
                        (S.cons (HRaw (S.index p ppos))
                          (path_spec (k / 2) (j / 2) nactd
                            (S.slice p (ppos + 1) (ppos + 1 + nplen)))));
        assert (vs ==
               MTS.mt_verify_ #(log2c (j / 2))
                 (path_spec (k / 2) (j / 2) nactd
                   (S.slice p (ppos + 1) (ppos + 1 + nplen)))
                 (k / 2) (HRaw nacc));
        mt_verify_ok_ (k / 2) (j / 2) p (ppos + 1) nacc nactd
      end
    end
    else begin
      let nacc = hash_2 (S.index p ppos) acc in
      assert (vi == mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd);
      assert (plen == 1 + nplen);
      assert (S.equal (S.tail (S.slice p ppos (ppos + plen)))
                      (S.slice p (ppos + 1) (ppos + 1 + nplen)));
      assert (S.equal (path_spec k j actd (S.slice p ppos (ppos + plen)))
                      (S.cons (HRaw (S.index p ppos))
                        (path_spec (k / 2) (j / 2) nactd
                          (S.slice p (ppos + 1) (ppos + 1 + nplen)))));
      assert (vs ==
             MTS.mt_verify_ #(log2c (j / 2))
               (path_spec (k / 2) (j / 2) nactd
                 (S.slice p (ppos + 1) (ppos + 1 + nplen)))
               (k / 2) (HRaw nacc));
      mt_verify_ok_ (k / 2) (j / 2) p (ppos + 1) nacc nactd
    end
  end
#reset-options "--z3rlimit 20"

val mt_verify_ok:
  k:nat ->
  j:nat{k < j} ->
  p:path{S.length p = 1 + mt_path_length k j false} ->
  rt:hash ->
  Lemma (mt_verify k j p rt <==>
        MTS.mt_verify #(log2c j)
          (path_spec k j false (S.tail p)) k (HRaw (S.head p)) (HRaw rt))
let mt_verify_ok k j p rt =
  mt_verify_ok_ k j p 1 (S.head p) false
