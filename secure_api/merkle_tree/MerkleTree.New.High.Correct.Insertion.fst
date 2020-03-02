module MerkleTree.New.High.Correct.Insertion

open EverCrypt
open EverCrypt.Helpers

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
open MerkleTree.New.High
open MerkleTree.New.High.Correct.Base

/// Correctness of insertion

val mt_hashes_next_rel_insert_odd:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j % 2 = 1} ->
  hs:hashes #hsz {S.length hs = j} -> v:hash ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  Lemma (requires (mt_hashes_next_rel #_ #f j hs nhs))
        (ensures (mt_hashes_next_rel #_ #f (j + 1)
                   (S.snoc hs v) (S.snoc nhs (f (S.last hs) v))))
let mt_hashes_next_rel_insert_odd #_ #_ j hs v nhs = ()

val mt_hashes_next_rel_insert_even:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j % 2 <> 1} ->
  hs:hashes #hsz {S.length hs = j} -> v:hash ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  Lemma (requires (mt_hashes_next_rel #_ #f j hs nhs))
        (ensures (mt_hashes_next_rel #_ #f (j + 1) (S.snoc hs v) nhs))
let mt_hashes_next_rel_insert_even #_ #_ j hs v nhs = ()

val insert_head:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (S.equal (S.index (insert_ #_ #f lv i j hs acc) lv)
                 (S.snoc (S.index hs lv) acc))
let insert_head #_ #_ lv i j hs acc = ()

val insert_inv_preserved_even:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (j % 2 <> 1 /\ mt_olds_hs_inv #_ #f lv i j olds hs))
        (ensures (mt_olds_hs_inv #_ #f lv i (j + 1) olds (insert_ #_ #f lv i j hs acc)))
        (decreases (32 - lv))
#reset-options "--z3rlimit 120 --max_fuel 2"
let insert_inv_preserved_even #_ #f lv i j olds hs acc =
  let ihs = hashess_insert lv i j hs acc in
  mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
  assert (mt_hashes_inv #_ #f lv j (merge_hs #_ #f olds hs));
  merge_hs_slice_equal #_ #f olds hs olds ihs (lv + 1) 32;
  remainder_2_not_1_div j;
  insert_base #_ #f lv i j hs acc;

  if lv = 31 then ()
  else begin
    // Facts
    assert (S.index (merge_hs #_ #f olds hs) (lv + 1) ==
           S.index (merge_hs #_ #f olds ihs) (lv + 1));

    // Head proof of `mt_hashes_inv`
    mt_hashes_next_rel_insert_even #_ #f j 
      (S.index (merge_hs #_ #f olds hs) lv) acc
      (S.index (merge_hs #_ #f olds hs) (lv + 1));
    assert (mt_hashes_next_rel #_ #f (j + 1)
             (S.index (merge_hs #_ #f olds ihs) lv)
             (S.index (merge_hs #_ #f olds ihs) (lv + 1)));

    // Tail proof of `mt_hashes_inv`
    mt_hashes_lth_inv_equiv #_ #f (lv + 1) ((j + 1) / 2)
      (merge_hs #_ #f olds hs) (merge_hs #_ #f olds ihs);
    mt_hashes_inv_equiv #_ #f (lv + 1) ((j + 1) / 2)
      (merge_hs #_ #f olds hs) (merge_hs #_ #f olds ihs);
    assert (mt_hashes_inv #_ #f (lv + 1) ((j + 1) / 2) (merge_hs #_ #f olds ihs))
  end

val insert_inv_preserved:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (mt_olds_hs_inv #_ #f lv i j olds hs))
        (ensures (mt_olds_hs_inv #_ #f lv i (j + 1) olds (insert_ #_ #f lv i j hs acc)))
        (decreases (32 - lv))
#reset-options "--z3rlimit 240 --max_fuel 1"
let rec insert_inv_preserved #_ #f lv i j olds hs acc =
  if j % 2 = 1 
  then begin
    let ihs = hashess_insert lv i j hs acc in
    mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
    merge_hs_slice_equal #_ #f olds hs olds ihs (lv + 1) 32;
    assert (mt_hashes_inv #_ #f lv j (merge_hs #_ #f olds hs));
    
    remainder_2_1_div j;
    insert_rec #_ #f lv i j hs acc;

    // Recursion
    mt_hashes_lth_inv_equiv #_ #f (lv + 1) (j / 2)
      (merge_hs #_ #f olds hs) (merge_hs #_ #f olds ihs);
    mt_hashes_inv_equiv #_ #f (lv + 1) (j / 2)
      (merge_hs #_ #f olds hs) (merge_hs #_ #f olds ihs);
    let nacc = f (S.last (S.index hs lv)) acc in
    let rihs = insert_ #_ #f (lv + 1) (i / 2) (j / 2) ihs nacc in
    insert_inv_preserved #_ #f (lv + 1) (i / 2) (j / 2) olds ihs nacc;

    // Head proof of `mt_hashes_inv`
    mt_olds_hs_lth_inv_ok #_ #f lv i (j + 1) olds rihs;
    mt_hashes_next_rel_insert_odd #_ #f j
      (S.index (merge_hs #_ #f olds hs) lv) acc
      (S.index (merge_hs #_ #f olds hs) (lv + 1));
    assert (S.equal (S.index rihs lv) (S.index ihs lv));
    insert_head #_ #f (lv + 1) (i / 2) (j / 2) ihs nacc;
    assert (S.equal (S.index ihs (lv + 1)) (S.index hs (lv + 1)));
    assert (mt_hashes_next_rel #_ #f (j + 1)
             (S.index (merge_hs #_ #f olds rihs) lv)
             (S.index (merge_hs #_ #f olds rihs) (lv + 1)));

    // Tail proof of `mt_hashes_inv` by recursion
    assert (mt_olds_hs_inv #_ #f (lv + 1) (i / 2) ((j + 1) / 2) olds rihs);

    assert (mt_hashes_inv #_ #f lv (j + 1) (merge_hs #_ #f olds rihs));
    assert (mt_olds_hs_inv #_ #f lv i (j + 1) olds rihs);
    assert (mt_olds_hs_inv #_ #f lv i (j + 1) olds (insert_ #_ #f lv i j hs acc))
  end
  else begin
    insert_inv_preserved_even #_ #f lv i j olds hs acc;
    assert (mt_olds_hs_inv #_ #f lv i (j + 1) olds (insert_ #_ #f lv i j hs acc))
  end
#reset-options

val mt_insert_inv_preserved:
  #hsz:pos ->
  mt:merkle_tree #hsz {mt_wf_elts mt /\ mt_not_full mt} -> v:hash ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz 0 (MT?.i mt) olds} ->
  Lemma (requires (mt_inv #hsz mt olds))
        (ensures (mt_inv #hsz (mt_insert mt v) olds))
let mt_insert_inv_preserved #_ mt v olds =
  insert_inv_preserved #_ #(MT?.hash_fun mt) 0 (MT?.i mt) (MT?.j mt) olds (MT?.hs mt) v

/// Correctness of `create_mt`

val empty_olds_inv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  Lemma (requires True)
        (ensures (mt_olds_inv #hsz lv 0 (empty_hashes 32)))
        (decreases (32 - lv))
let rec empty_olds_inv #_ #f lv =
  if lv = 32 then ()
  else empty_olds_inv #_ #f (lv + 1)

val create_empty_mt_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  unit ->
  Lemma (empty_olds_inv #_ #f 0;
        mt_inv #hsz (create_empty_mt #_ #f ()) (empty_hashes 32))
let create_empty_mt_inv_ok #_ #f _ =
  merge_hs_empty #_ #f 32;
  mt_hashes_inv_empty #_ #f 0

val create_mt_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  init:hash ->
  Lemma (empty_olds_inv #_ #f 0;
        mt_inv #hsz (mt_create hsz f init) (empty_hashes 32))
let create_mt_inv_ok #hsz #f init =
  create_empty_mt_inv_ok #_ #f ();
  empty_olds_inv #_ #f 0;
  mt_insert_inv_preserved #_ (create_empty_mt #hsz #f ()) init (empty_hashes 32)

