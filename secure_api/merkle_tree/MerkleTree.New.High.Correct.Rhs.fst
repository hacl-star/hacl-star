module MerkleTree.New.High.Correct.Rhs

open FStar.Classical
open FStar.Ghost
open FStar.Seq

module S = FStar.Seq

module MTS = MerkleTree.Spec
open MerkleTree.New.High
open MerkleTree.New.High.Correct.Base


#set-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

/// Correctness of rightmost hashes

// Another version of `construct_rhs` that recursively
// accumulates rightmost hashes.
val construct_rhs_acc:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  fhs:hashess #hsz {
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log #hsz j fhs} ->
  acc:hash #hsz ->
  actd:bool ->
  GTot (rhs:hashes #hsz {S.length rhs = log2c j} * hash #hsz) (decreases j)
let rec construct_rhs_acc #_ #f j fhs acc actd =
  if j = 0 then (S.empty, acc)
  else begin
    if j % 2 = 0
    then (let nrhsh = construct_rhs_acc #_ #f(j / 2) (S.tail fhs) acc actd in
         (S.cons hash_init (fst nrhsh), snd nrhsh))
    else (let rhd = if actd then acc else hash_init in
         let nacc = if actd
                    then f (S.last (S.head fhs)) acc
                    else S.last (S.head fhs) in
         let nrhsh = construct_rhs_acc #_ #f (j / 2) (S.tail fhs) nacc true in
         (S.cons rhd (fst nrhsh), snd nrhsh))
  end

#push-options "--initial_ifuel 1 --max_ifuel 1"
val construct_rhs_acc_odd:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  fhs:hashess #hsz {
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log #hsz j fhs} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires (j % 2 <> 0))
        (ensures (let rrf = construct_rhs_acc #_ #f j fhs acc actd in
                 let nacc = if actd
                            then f (S.last (S.head fhs)) acc
                            else S.last (S.head fhs) in
                 let nrrf = construct_rhs_acc #_ #f (j / 2) (S.tail fhs) nacc true in
                 S.equal (S.tail (fst rrf)) (fst nrrf) /\
                 snd rrf == snd nrrf))
let construct_rhs_acc_odd #_ #f j fhs acc actd = ()
#pop-options

#push-options "--initial_fuel 2 --max_fuel 2"
val construct_rhs_acc_inv_ok_0:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  fhs:hashess #hsz {
    S.length fhs = 1 /\
    mt_hashes_lth_inv_log #hsz 1 fhs /\
    mt_hashes_inv_log #_ #f 1 fhs} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_acc #_ #f 1 fhs acc actd in
                 mt_rhs_inv #_ #f 1
                   (hash_seq_spec_full #_ #f (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #_ #f #1
                   (hash_seq_spec_full #_ #f (S.head fhs) acc actd) ==
                 MTS.HRaw #hsz (snd crhs)))
let construct_rhs_acc_inv_ok_0 #_ #f fhs acc actd = ()
#pop-options

#push-options "--z3rlimit 240"
val construct_rhs_acc_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 0} ->
  fhs:hashess #hsz {
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log #hsz j fhs /\
    mt_hashes_inv_log #_ #f j fhs} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_acc #_ #f j fhs acc actd in
                 mt_rhs_inv #_ #f j
                   (hash_seq_spec_full #_ #f (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #_ #f #(log2c j)
                   (hash_seq_spec_full #_ #f (S.head fhs) acc actd) ==
                 MTS.HRaw (snd crhs)))
        (decreases j)
let rec construct_rhs_acc_inv_ok #hsz #f j fhs acc actd =
  if j = 1 then 
    construct_rhs_acc_inv_ok_0 #_ #f fhs acc actd
  else if j % 2 = 0 then begin
    construct_rhs_acc_inv_ok #_ #f (j / 2) (S.tail fhs) acc actd;
    let rcrhs = construct_rhs_acc #_ #f (j / 2) (S.tail fhs) acc actd in
    assert (mt_rhs_inv #_ #f (j / 2)
             (hash_seq_spec_full #_ #f (S.head (S.tail fhs)) acc actd)
             (fst rcrhs) actd);
    assert (MTS.mt_get_root #_ #f #(log2c j - 1)
             (hash_seq_spec_full #_ #f (S.head (S.tail fhs)) acc actd) ==
           MTS.HRaw (snd rcrhs));

    let crhs = (S.cons hash_init (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next #_ #f j fhs;
    hash_seq_spec_full_even_next #_ #f 
      j (S.head fhs) (S.head (S.tail fhs)) acc actd;
    assert (mt_rhs_inv #_ #f (j / 2)
             (MTS.mt_next_lv #_ #f #(log2c j)
               (hash_seq_spec_full #_ #f (S.head fhs) acc actd))
             (fst rcrhs) actd);

    assert (mt_rhs_inv #_ #f j
             (hash_seq_spec_full #_ #f (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #_ #f #(log2c j)
             (hash_seq_spec_full #_ #f (S.head fhs) acc actd) ==
           MTS.HRaw (snd rcrhs))
  end

  else begin
    let rhd = if actd then acc else hash_init #hsz in
    let nacc = if actd
               then f (S.last (S.head fhs)) acc
               else S.last (S.head fhs) in
    construct_rhs_acc_inv_ok #_ #f (j / 2) (S.tail fhs) nacc true;
    let rcrhs = construct_rhs_acc #_ #f (j / 2) (S.tail fhs) nacc true in
    assert (mt_rhs_inv #_ #f (j / 2)
             (hash_seq_spec_full #_ #f (S.head (S.tail fhs)) nacc true)
             (fst rcrhs) true);
    assert (MTS.mt_get_root #_ #f #(log2c j - 1)
             (hash_seq_spec_full #_ #f  (S.head (S.tail fhs)) nacc true) ==
           MTS.HRaw (snd rcrhs));

    let crhs = (S.cons rhd (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next #_ #f j fhs;
    hash_seq_spec_full_odd_next #_ #f 
      j (S.head fhs) (S.head (S.tail fhs)) acc actd nacc;
    (if actd then hash_seq_spec_full_case_true #_ #f (S.head fhs) acc);
    assert (if actd
           then (S.index (hash_seq_spec_full #_ #f (S.head fhs) acc actd) j ==
                MTS.HRaw rhd)
           else true);
    assert (mt_rhs_inv #_ #f (j / 2)
             (MTS.mt_next_lv #_ #f #(log2c j)
               (hash_seq_spec_full #_ #f (S.head fhs) acc actd))
             (fst rcrhs) true);

    assert (mt_rhs_inv #_ #f j
             (hash_seq_spec_full #_ #f (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #_ #f #(log2c j)
             (hash_seq_spec_full #_ #f (S.head fhs) acc actd) ==
           MTS.HRaw (snd crhs))
  end
#pop-options


val rhs_equiv:
  #hsz:pos ->
  j:nat ->
  rhs1:hashes #hsz {S.length rhs1 = log2c j} ->
  rhs2:hashes #hsz {S.length rhs2 = log2c j} ->
  actd:bool ->
  GTot Type0 (decreases j)
let rec rhs_equiv #hsz j rhs1 rhs2 actd =
  if j = 0 then true
  else if j % 2 = 0
  then rhs_equiv #hsz (j / 2) (S.tail rhs1) (S.tail rhs2) actd
  else ((if actd then S.head rhs1 == S.head rhs2 else true) /\
       rhs_equiv #hsz (j / 2) (S.tail rhs1) (S.tail rhs2) true)

val rhs_equiv_inv_preserved:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  smt:MTS.merkle_tree (log2c j) ->
  rhs1:hashes #hsz {S.length rhs1 = log2c j} ->
  rhs2:hashes #hsz {S.length rhs2 = log2c j} ->
  actd:bool ->
  Lemma (requires (mt_rhs_inv #_ #f j smt rhs1 actd /\
                  rhs_equiv #hsz j rhs1 rhs2 actd))
        (ensures (mt_rhs_inv #_ #f j smt rhs2 actd))
        (decreases j)
let rec rhs_equiv_inv_preserved #_ #f j smt rhs1 rhs2 actd =
  if j = 0 then ()
  else if j % 2 = 0
  then rhs_equiv_inv_preserved #_ #f (j / 2) (MTS.mt_next_lv #_ #f #(log2c j) smt)
         (S.tail rhs1) (S.tail rhs2) actd
  else begin
    (if actd
    then (assert (S.index smt j == MTS.HRaw (S.head rhs1));
         assert (S.head rhs1 == S.head rhs2))
    else ());
    rhs_equiv_inv_preserved #_ #f (j / 2) (MTS.mt_next_lv #_ #f #(log2c j) smt)
      (S.tail rhs1) (S.tail rhs2) true
  end

val construct_rhs_acc_consistent:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires True)
        (ensures
          (log2c_bound j (32 - lv);
          mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
          mt_hashes_lth_inv_log_converted_ #_ #f lv j (merge_hs #_ #f olds hs);
          (let rrf = construct_rhs_acc #_ #f j
                       (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd in
          let rr = construct_rhs #_ #f lv hs rhs i j acc actd in
          rhs_equiv #hsz j (fst rrf) (S.slice (fst rr) lv (lv + log2c j)) actd /\
          snd rrf == snd rr)))
        (decreases j)

#push-options "--z3rlimit 250 --ifuel 1"
#push-options "--quake 1/3"
let rec construct_rhs_acc_consistent #hsz #f lv i j olds hs rhs acc actd =
  assert (j < pow2 (32 - lv));
  assert (j <> 0 ==> j / 2 < pow2 (32 - (lv + 1)));
  log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ #_ #f lv j (merge_hs #_ #f olds hs);
  let rrf = construct_rhs_acc #_ #f j
              (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd in
  let rr = construct_rhs #_ #f lv hs rhs i j acc actd in
  construct_rhs_unchanged #_ #f lv hs rhs i j acc actd;
  assert (S.equal (S.slice rhs 0 lv) (S.slice (fst rr) 0 lv));

  if j = 0 then ()
  else begin
    log2c_div j; 
    assert (32 - (lv + 1) >= 0);
    log2c_bound (j / 2) (32 - (lv + 1));
    mt_olds_hs_lth_inv_ok #_ #f (lv + 1) (i / 2) (j / 2) olds hs;
    mt_hashes_lth_inv_log_converted_ #_ #f (lv + 1) (j / 2) (merge_hs #_ #f olds hs);
    
    if j % 2 = 0 then begin
      construct_rhs_acc_consistent #_ #f (lv + 1) (i / 2) (j / 2)
        olds hs rhs acc actd;
      log2c_bound (j/2) (32 - (lv + 1));
      mt_olds_hs_lth_inv_ok #hsz #f (lv+1) (i/2) (j/2) olds hs;
      mt_hashes_lth_inv_log_converted_ #_ #f lv j (merge_hs #_ #f olds hs);
      let rrf = construct_rhs_acc #_ #f j
                (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd in
      let rr = construct_rhs #_ #f lv hs rhs i j acc actd in
      assert (rhs_equiv #hsz j (fst rrf) (S.slice (fst rr) lv (lv + log2c j)) actd);
      assert (snd rrf == snd rr)
    end
    else
    begin
      let rhd = if actd then acc else hash_init in
      let nacc = if actd
                 then f (S.last (S.index hs lv)) acc
                 else S.last (S.index hs lv) in
      assert (S.equal (S.tail (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)))
                      (S.slice (merge_hs #_ #f olds hs)
                        (lv + 1) (lv + 1 + log2c (j / 2))));

      // Recursion step for `construct_rhs_acc`
      let nrrf = construct_rhs_acc #_ #f (j / 2)
                   (S.slice (merge_hs #_ #f olds hs) (lv + 1) (lv + 1 + (log2c (j / 2))))
                   nacc true in
      construct_rhs_acc_odd #_ #f j (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd;

      // Recursion step for `construct_rhs`
      assert (hs_wf_elts (lv + 1) hs (i / 2) (j / 2));
      let nrhs = if actd then S.upd rhs lv acc else rhs in
      let nrr = construct_rhs #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true in
      construct_rhs_odd #_ #f lv hs rhs i j acc actd;
      construct_rhs_unchanged #_ #f (lv + 1) hs nrhs (i / 2) (j / 2) nacc true;
      assert (S.equal (S.slice nrhs 0 (lv + 1)) (S.slice (fst nrr) 0 (lv + 1)));
      assert (S.index (fst nrr) lv == S.index nrhs lv);

      // Recursion for the proof
      construct_rhs_acc_consistent #_ #f (lv + 1) (i / 2) (j / 2)
        olds hs nrhs nacc true;
      assert (rhs_equiv #hsz (j / 2) (fst nrrf)
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
      assert (rhs_equiv #hsz (j / 2) (S.tail (fst rrf))
               (S.slice (fst rr) (lv + 1) (lv + 1 + log2c (j / 2))) true);
      assert (rhs_equiv #hsz j (fst rrf) (S.slice (fst rr) lv (lv + log2c j)) actd);
      assert (snd rrf == snd rr)
    end
  end
#pop-options

val construct_rhs_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{j > 0 /\ i <= j /\ j < pow2 (32 - lv)} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires (mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
                  mt_hashes_inv #_ #f lv j (merge_hs #_ #f olds hs)))
        (ensures (log2c_bound j (32 - lv);
                 mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
                 (let crhs = construct_rhs #_ #f lv hs rhs i j acc actd in
                 mt_rhs_inv #_ #f j
                   (hash_seq_spec_full #_ #f (S.index (merge_hs #_ #f olds hs) lv) acc actd)
                   (S.slice (fst crhs) lv (lv + log2c j)) actd /\
                 MTS.mt_get_root #_ #f #(log2c j)
                   (hash_seq_spec_full #_ #f (S.index (merge_hs #_ #f olds hs) lv) acc actd) ==
                 MTS.HRaw (snd crhs))))
let construct_rhs_inv_ok #hsz #f lv i j olds hs rhs acc actd =
  log2c_div j; log2c_bound j (32 - lv);
  mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
  mt_hashes_lth_inv_log_converted_ #_ #f lv j (merge_hs #_ #f olds hs);
  mt_hashes_inv_log_converted_ #_ #f lv j (merge_hs #_ #f olds hs);
  let crhs = construct_rhs #_ #f lv hs rhs i j acc actd in
  let crhsf = construct_rhs_acc #_ #f j
                (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd in
  construct_rhs_acc_consistent #_ #f lv i j olds hs rhs acc actd;
  construct_rhs_acc_inv_ok #_ #f j
    (S.slice (merge_hs #_ #f olds hs) lv (lv + log2c j)) acc actd;
  rhs_equiv_inv_preserved #_ #f j
    (hash_seq_spec_full #_ #f (S.index (merge_hs #_ #f olds hs) lv) acc actd)
    (fst crhsf) (S.slice (fst crhs) lv (lv + log2c j)) actd
#pop-options

val construct_rhs_base_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  i:nat -> j:nat{j > 0 /\ i <= j /\ j < pow2 32} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz 0 i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts 0 hs i j} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  acc:hash #hsz ->
  actd:bool ->
  Lemma (requires (mt_olds_hs_lth_inv_ok #_ #f 0 i j olds hs;
                  mt_hashes_inv #_ #f 0 j (merge_hs #_ #f olds hs)))
        (ensures (log2c_bound j 32;
                 mt_olds_hs_lth_inv_ok #_ #f 0 i j olds hs;
                 (let crhs = construct_rhs #_ #f 0 hs rhs i j acc actd in
                 mt_rhs_inv #_ #f j
                   (hash_seq_spec_full #_ #f (S.head (merge_hs #_ #f olds hs)) acc actd)
                   (S.slice (fst crhs) 0 (log2c j)) actd /\
                 MTS.mt_get_root #_ #f #(log2c j)
                   (hash_seq_spec_full #_ #f (S.head (merge_hs #_ #f olds hs)) acc actd) ==
                 MTS.HRaw (snd crhs))))
let construct_rhs_base_inv_ok #hsz #f i j olds hs rhs acc actd =
  construct_rhs_inv_ok #_ #f 0 i j olds hs rhs acc actd

val construct_rhs_init_ignored:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  hs:hashess #hsz {S.length hs = 32} ->
  rhs:hashes #hsz {S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc1:hash #hsz -> acc2:hash #hsz ->
  Lemma (requires (j > 0))
        (ensures (let rr1 = construct_rhs #_ #f lv hs rhs i j acc1 false in
                  let rr2 = construct_rhs #_ #f lv hs rhs i j acc2 false in
                  S.equal (fst rr1) (fst rr2) /\ snd rr1 == snd rr2))
        (decreases j)
#push-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec construct_rhs_init_ignored #hsz #f lv hs rhs i j acc1 acc2 =
  if j % 2 = 0
  then construct_rhs_init_ignored #_ #f (lv + 1) hs rhs (i / 2) (j / 2) acc1 acc2
  else ()
#pop-options

val mt_get_root_inv_ok:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} -> drt:hash ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz 0 (MT?.i mt) olds} ->
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
let mt_get_root_inv_ok #hsz mt drt olds =
  if MT?.rhs_ok mt then ()
  else if MT?.j mt = 0 then ()
  else begin
    construct_rhs_base_inv_ok #_ #(MT?.hash_fun mt)
      (MT?.i mt) (MT?.j mt) olds (MT?.hs mt) (MT?.rhs mt)
      hash_init false;
    construct_rhs_init_ignored #_ #(MT?.hash_fun mt)
      0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
      hash_init drt
  end
