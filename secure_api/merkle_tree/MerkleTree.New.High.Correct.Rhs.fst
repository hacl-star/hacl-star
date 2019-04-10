module MerkleTree.New.High.Correct.Rhs

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

/// Correctness of rightmost hashes

// Another version of `construct_rhs` that recursively 
// accumulates rightmost hashes.
val construct_rhs_acc:
  j:nat ->
  fhs:hash_ss{
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log j fhs} ->
  acc:hash ->
  actd:bool ->
  GTot (rhs:hash_seq{S.length rhs = log2c j} * hash) (decreases j)
#reset-options "--z3rlimit 10"
let rec construct_rhs_acc j fhs acc actd =
  if j = 0 then (S.empty, acc)
  else begin
    if j % 2 = 0
    then (let nrhsh = construct_rhs_acc (j / 2) (S.tail fhs) acc actd in
         (S.cons hash_init (fst nrhsh), snd nrhsh))
    else (let rhd = if actd then acc else hash_init in
         let nacc = if actd 
                    then hash_2 (S.last (S.head fhs)) acc
                    else S.last (S.head fhs) in
         let nrhsh = construct_rhs_acc (j / 2) (S.tail fhs) nacc true in
         (S.cons rhd (fst nrhsh), snd nrhsh))
  end

val construct_rhs_acc_odd:
  j:nat ->
  fhs:hash_ss{
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log j fhs} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (j % 2 <> 0))
        (ensures (let rrf = construct_rhs_acc j fhs acc actd in
                 let nacc = if actd 
                            then hash_2 (S.last (S.head fhs)) acc
                            else S.last (S.head fhs) in
                 let nrrf = construct_rhs_acc (j / 2) (S.tail fhs) nacc true in
                 S.equal (S.tail (fst rrf)) (fst nrrf) /\
                 snd rrf == snd nrrf))
let construct_rhs_acc_odd j fhs acc actd = ()  

val construct_rhs_acc_inv_ok_0:
  fhs:hash_ss{
    S.length fhs = 1 /\
    mt_hashes_lth_inv_log 1 fhs /\
    mt_hashes_inv_log 1 fhs} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_acc 1 fhs acc actd in
                 mt_rhs_inv 1
                   (hash_seq_spec_full (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #1
                   (hash_seq_spec_full (S.head fhs) acc actd) ==
                 HRaw (snd crhs)))
let construct_rhs_acc_inv_ok_0 fhs acc actd = ()

val construct_rhs_acc_inv_ok:
  j:nat{j > 0} ->
  fhs:hash_ss{
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log j fhs /\
    mt_hashes_inv_log j fhs} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_acc j fhs acc actd in
                 mt_rhs_inv j
                   (hash_seq_spec_full (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #(log2c j)
                   (hash_seq_spec_full (S.head fhs) acc actd) == 
                 HRaw (snd crhs)))
        (decreases j)
#reset-options "--z3rlimit 240 --max_fuel 2"
let rec construct_rhs_acc_inv_ok j fhs acc actd =
  if j = 1 then construct_rhs_acc_inv_ok_0 fhs acc actd

  else if j % 2 = 0 then begin
    construct_rhs_acc_inv_ok (j / 2) (S.tail fhs) acc actd;
    let rcrhs = construct_rhs_acc (j / 2) (S.tail fhs) acc actd in
    assert (mt_rhs_inv (j / 2)
             (hash_seq_spec_full (S.head (S.tail fhs)) acc actd)
             (fst rcrhs) actd);
    assert (MTS.mt_get_root #(log2c j - 1)
             (hash_seq_spec_full (S.head (S.tail fhs)) acc actd) ==
           HRaw (snd rcrhs));

    let crhs = (S.cons hash_init (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next j fhs;
    hash_seq_spec_full_even_next
      j (S.head fhs) (S.head (S.tail fhs)) acc actd;
    assert (mt_rhs_inv (j / 2)
             (mt_next_lv #(log2c j)
               (hash_seq_spec_full (S.head fhs) acc actd))
             (fst rcrhs) actd);

    assert (mt_rhs_inv j
             (hash_seq_spec_full (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #(log2c j)
             (hash_seq_spec_full (S.head fhs) acc actd) ==
           HRaw (snd rcrhs))
  end

  else begin
    let rhd = if actd then acc else hash_init in
    let nacc = if actd 
               then hash_2 (S.last (S.head fhs)) acc
               else S.last (S.head fhs) in
    construct_rhs_acc_inv_ok (j / 2) (S.tail fhs) nacc true;
    let rcrhs = construct_rhs_acc (j / 2) (S.tail fhs) nacc true in
    assert (mt_rhs_inv (j / 2)
             (hash_seq_spec_full (S.head (S.tail fhs)) nacc true)
             (fst rcrhs) true);
    assert (MTS.mt_get_root #(log2c j - 1)
             (hash_seq_spec_full (S.head (S.tail fhs)) nacc true) ==
           HRaw (snd rcrhs));

    let crhs = (S.cons rhd (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next j fhs;
    hash_seq_spec_full_odd_next
      j (S.head fhs) (S.head (S.tail fhs)) acc actd nacc;
    (if actd then hash_seq_spec_full_case_true (S.head fhs) acc);
    assert (if actd
           then (S.index (hash_seq_spec_full (S.head fhs) acc actd) j ==
                HRaw rhd)
           else true);
    assert (mt_rhs_inv (j / 2)
             (mt_next_lv #(log2c j)
               (hash_seq_spec_full (S.head fhs) acc actd))
             (fst rcrhs) true);

    assert (mt_rhs_inv j
             (hash_seq_spec_full (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #(log2c j)
             (hash_seq_spec_full (S.head fhs) acc actd) == 
           HRaw (snd crhs))
  end
#reset-options

val rhs_equiv:
  j:nat ->
  rhs1:hash_seq{S.length rhs1 = log2c j} ->
  rhs2:hash_seq{S.length rhs2 = log2c j} ->
  actd:bool ->
  GTot Type0 (decreases j)
let rec rhs_equiv j rhs1 rhs2 actd =
  if j = 0 then true
  else if j % 2 = 0 
  then rhs_equiv (j / 2) (S.tail rhs1) (S.tail rhs2) actd
  else ((if actd then S.head rhs1 == S.head rhs2 else true) /\
       rhs_equiv (j / 2) (S.tail rhs1) (S.tail rhs2) true)

val rhs_equiv_inv_preserved:
  j:nat ->
  smt:MTS.merkle_tree (log2c j) ->
  rhs1:hash_seq{S.length rhs1 = log2c j} ->
  rhs2:hash_seq{S.length rhs2 = log2c j} ->
  actd:bool ->
  Lemma (requires (mt_rhs_inv j smt rhs1 actd /\
                  rhs_equiv j rhs1 rhs2 actd))
        (ensures (mt_rhs_inv j smt rhs2 actd))
        (decreases j)
#reset-options "--z3rlimit 10 --max_fuel 1"
let rec rhs_equiv_inv_preserved j smt rhs1 rhs2 actd =
  if j = 0 then ()
  else if j % 2 = 0 
  then rhs_equiv_inv_preserved (j / 2) (mt_next_lv #(log2c j) smt)
         (S.tail rhs1) (S.tail rhs2) actd
  else begin
    (if actd
    then (assert (S.index smt j == HRaw (S.head rhs1));
         assert (S.head rhs1 == S.head rhs2))
    else ());
    rhs_equiv_inv_preserved (j / 2) (mt_next_lv #(log2c j) smt)
      (S.tail rhs1) (S.tail rhs2) true
  end
#reset-options

#reset-options "--z3rlimit 20"
val construct_rhs_acc_consistent:
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures
          (log2c_bound j (32 - lv);
          mt_olds_hs_lth_inv_ok lv i j olds hs;
          mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
          (let rrf = construct_rhs_acc j
                       (S.slice (merge_hs olds hs) lv (lv + log2c j)) acc actd in
          let rr = construct_rhs lv hs rhs i j acc actd in
          rhs_equiv j (fst rrf) (S.slice (fst rr) lv (lv + log2c j)) actd /\
          snd rrf == snd rr)))
        (decreases j)
#reset-options "--z3rlimit 240 --max_fuel 1"
let rec construct_rhs_acc_consistent lv i j olds hs rhs acc actd =
  log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
  let rrf = construct_rhs_acc j
              (S.slice (merge_hs olds hs) lv (lv + log2c j)) acc actd in
  let rr = construct_rhs lv hs rhs i j acc actd in
  construct_rhs_unchanged lv hs rhs i j acc actd;
  assert (S.equal (S.slice rhs 0 lv) (S.slice (fst rr) 0 lv));

  if j = 0 then ()
  else begin
    log2c_div j; log2c_bound (j / 2) (32 - (lv + 1));
    mt_olds_hs_lth_inv_ok (lv + 1) (i / 2) (j / 2) olds hs;
    mt_hashes_lth_inv_log_converted_ (lv + 1) (j / 2) (merge_hs olds hs);
    
    if j % 2 = 0 then begin
      construct_rhs_acc_consistent (lv + 1) (i / 2) (j / 2)
        olds hs rhs acc actd
    end
    else begin
      let rhd = if actd then acc else hash_init in
      let nacc = if actd
                 then hash_2 (S.last (S.index hs lv)) acc
                 else S.last (S.index hs lv) in
      assert (S.equal (S.tail (S.slice (merge_hs olds hs) lv (lv + log2c j)))
                      (S.slice (merge_hs olds hs) 
                        (lv + 1) (lv + 1 + log2c (j / 2))));

      // Recursion step for `construct_rhs_acc`
      let nrrf = construct_rhs_acc (j / 2)
                   (S.slice (merge_hs olds hs) (lv + 1) (lv + 1 + (log2c (j / 2))))
                   nacc true in
      construct_rhs_acc_odd j (S.slice (merge_hs olds hs) lv (lv + log2c j)) acc actd;

      // Recursion step for `construct_rhs`
      assert (hs_wf_elts (lv + 1) hs (i / 2) (j / 2));
      let nrhs = if actd then S.upd rhs lv acc else rhs in
      let nrr = construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true in
      construct_rhs_odd lv hs rhs i j acc actd;
      construct_rhs_unchanged (lv + 1) hs nrhs (i / 2) (j / 2) nacc true;
      assert (S.equal (S.slice nrhs 0 (lv + 1)) (S.slice (fst nrr) 0 (lv + 1)));
      assert (S.index (fst nrr) lv == S.index nrhs lv);

      // Recursion for the proof
      construct_rhs_acc_consistent (lv + 1) (i / 2) (j / 2)
        olds hs nrhs nacc true;
      assert (rhs_equiv (j / 2) (fst nrrf)
               (S.slice (fst nrr) (lv + 1) (lv + 1 + log2c (j / 2))) true);
      assert (snd nrrf == snd nrr);

      // All together
      (if actd
      then (assert (S.head (fst rrf) == rhd);
           assert (rhd == acc);
           assert (S.index (fst rr) lv == S.index nrhs lv);
           assert (S.index nrhs lv == acc);
           assert (S.head (fst rrf) == S.index (fst rr) lv))
      else ());

      assert (if actd then S.head (fst rrf) == S.index (fst rr) lv else true);
      assert (rhs_equiv (j / 2) (S.tail (fst rrf))
               (S.slice (fst rr) (lv + 1) (lv + 1 + log2c (j / 2))) true);
      assert (rhs_equiv j (fst rrf) (S.slice (fst rr) lv (lv + log2c j)) actd);
      assert (snd rrf == snd rr)
    end
  end
#reset-options

#reset-options "--z3rlimit 20"
val construct_rhs_inv_ok:
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{j > 0 /\ i <= j /\ j < pow2 (32 - lv)} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (mt_olds_hs_lth_inv_ok lv i j olds hs;
                  mt_hashes_inv lv j (merge_hs olds hs)))
        (ensures (log2c_bound j (32 - lv);
                 mt_olds_hs_lth_inv_ok lv i j olds hs;
                 (let crhs = construct_rhs lv hs rhs i j acc actd in
                 mt_rhs_inv j
                   (hash_seq_spec_full (S.index (merge_hs olds hs) lv) acc actd)
                   (S.slice (fst crhs) lv (lv + log2c j)) actd /\
                 MTS.mt_get_root #(log2c j)
                   (hash_seq_spec_full (S.index (merge_hs olds hs) lv) acc actd) == 
                 HRaw (snd crhs))))
#reset-options "--z3rlimit 40"
let construct_rhs_inv_ok lv i j olds hs rhs acc actd =
  log2c_div j; log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ lv j (merge_hs olds hs);
  mt_hashes_inv_log_converted_ lv j (merge_hs olds hs);
  let crhs = construct_rhs lv hs rhs i j acc actd in
  let crhsf = construct_rhs_acc j
                (S.slice (merge_hs olds hs) lv (lv + log2c j)) acc actd in
  construct_rhs_acc_consistent lv i j olds hs rhs acc actd;
  construct_rhs_acc_inv_ok j
    (S.slice (merge_hs olds hs) lv (lv + log2c j)) acc actd;
  rhs_equiv_inv_preserved j
    (hash_seq_spec_full (S.index (merge_hs olds hs) lv) acc actd)
    (fst crhsf) (S.slice (fst crhs) lv (lv + log2c j)) actd
#reset-options

#reset-options "--z3rlimit 10"
val construct_rhs_base_inv_ok:
  i:nat -> j:nat{j > 0 /\ i <= j /\ j < pow2 32} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts 0 hs i j} ->
  rhs:hash_seq{S.length rhs = 32} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (mt_olds_hs_lth_inv_ok 0 i j olds hs;
                  mt_hashes_inv 0 j (merge_hs olds hs)))
        (ensures (log2c_bound j 32;
                 mt_olds_hs_lth_inv_ok 0 i j olds hs;
                 (let crhs = construct_rhs 0 hs rhs i j acc actd in
                 mt_rhs_inv j
                   (hash_seq_spec_full (S.head (merge_hs olds hs)) acc actd)
                   (S.slice (fst crhs) 0 (log2c j)) actd /\
                 MTS.mt_get_root #(log2c j)
                   (hash_seq_spec_full (S.head (merge_hs olds hs)) acc actd) == 
                 HRaw (snd crhs))))
let construct_rhs_base_inv_ok i j olds hs rhs acc actd =
  construct_rhs_inv_ok 0 i j olds hs rhs acc actd
#reset-options

val construct_rhs_init_ignored:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{  
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc1:hash -> acc2:hash ->
  Lemma (requires (j > 0))
        (ensures (let rr1 = construct_rhs lv hs rhs i j acc1 false in
                 let rr2 = construct_rhs lv hs rhs i j acc2 false in
                 S.equal (fst rr1) (fst rr2) /\ snd rr1 == snd rr2))
        (decreases j)
let rec construct_rhs_init_ignored lv hs rhs i j acc1 acc2 =
  if j % 2 = 0
  then construct_rhs_init_ignored (lv + 1) hs rhs (i / 2) (j / 2) acc1 acc2
  else ()

val mt_get_root_inv_ok:
  mt:merkle_tree{mt_wf_elts mt} -> drt:hash ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  Lemma (requires (mt_inv mt olds))
        (ensures (let nmt, rt = mt_get_root mt drt in
                 // Only `MT?.rhs` and `MT?.mroot` are changed.
                 MT?.i mt == MT?.i nmt /\
                 MT?.j mt == MT?.j nmt /\
                 MT?.hs mt == MT?.hs nmt /\
                 // A Merkle tree with new `MT?.rhs` and `MT?.mroot` is valid.
                 mt_inv nmt olds /\
                 // A returned root is indeed the Merkle root.
                 rt == MT?.mroot nmt))
let mt_get_root_inv_ok mt drt olds =
  if MT?.rhs_ok mt then ()
  else if MT?.j mt = 0 then ()
  else begin
    construct_rhs_base_inv_ok
      (MT?.i mt) (MT?.j mt) olds (MT?.hs mt) (MT?.rhs mt)
      hash_init false;
    construct_rhs_init_ignored
      0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
      hash_init drt
  end

