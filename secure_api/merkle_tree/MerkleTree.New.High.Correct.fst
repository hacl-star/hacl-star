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

/// Invariants of high-level Merkle tree design

val empty_hashes: len:nat -> GTot (hs:hash_ss{S.length hs = len})
let empty_hashes len = S.create len S.empty

val empty_hashes_head:
  len:nat{len > 0} ->
  Lemma (S.head (empty_hashes len) == S.empty)
let empty_hashes_head len = ()

val empty_hashes_tail:
  len:nat{len > 0} ->
  Lemma (S.equal (S.tail (empty_hashes len))
                 (empty_hashes (len - 1)))
let empty_hashes_tail len = ()

val mt_hashes_lth_inv:
  lv:nat{lv <= 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_hashes_lth_inv lv j fhs =
  if lv = 32 then true
  else (S.length (S.index fhs lv) == j /\
       mt_hashes_lth_inv (lv + 1) (j / 2) fhs)

val mt_hashes_lth_inv_empty:
  lv:nat{lv <= 32} ->
  Lemma (requires True)
        (ensures (mt_hashes_lth_inv lv 0 (empty_hashes 32)))
        (decreases (32 - lv))
let rec mt_hashes_lth_inv_empty lv =
  if lv = 32 then ()
  else mt_hashes_lth_inv_empty (lv + 1)

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

val mt_hashes_inv_empty:
  lv:nat{lv < 32} ->
  Lemma (requires True)
        (ensures (mt_hashes_lth_inv_empty lv;
                 mt_hashes_inv lv 0 (empty_hashes 32)))
        (decreases (32 - lv))
let rec mt_hashes_inv_empty lv =
  if lv = 31 then ()
  else mt_hashes_inv_empty (lv + 1)

val mt_hashes_lth_inv_equiv:
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hash_ss{S.length fhs1 = 32} ->
  fhs2:hash_ss{S.length fhs2 = 32} ->
  Lemma (requires (mt_hashes_lth_inv lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32)))
        (ensures (mt_hashes_lth_inv lv j fhs2))
        (decreases (32 - lv))
let rec mt_hashes_lth_inv_equiv lv j fhs1 fhs2 =
  if lv = 31 then ()
  else (assert (S.index fhs1 lv == S.index fhs2 lv);
       mt_hashes_lth_inv_equiv (lv + 1) (j / 2) fhs1 fhs2)

val mt_hashes_inv_equiv:
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hash_ss{S.length fhs1 = 32 /\ mt_hashes_lth_inv lv j fhs1} ->
  fhs2:hash_ss{S.length fhs2 = 32 /\ mt_hashes_lth_inv lv j fhs2} ->
  Lemma (requires (mt_hashes_inv lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32)))
        (ensures (mt_hashes_inv lv j fhs2))
        (decreases (32 - lv))
let rec mt_hashes_inv_equiv lv j fhs1 fhs2 =
  if lv = 31 then ()
  else (assert (S.index fhs1 lv == S.index fhs2 lv);
       assert (S.index fhs1 (lv + 1) == S.index fhs2 (lv + 1));
       mt_hashes_inv_equiv (lv + 1) (j / 2) fhs1 fhs2)

val merge_hs:
  hs1:hash_ss ->
  hs2:hash_ss{S.length hs1 = S.length hs2} ->
  GTot (mhs:hash_ss{S.length mhs = S.length hs1})
       (decreases (S.length hs1))
let rec merge_hs hs1 hs2 =
  if S.length hs1 = 0 then S.empty
  else (S.cons (S.append (S.head hs1) (S.head hs2))
               (merge_hs (S.tail hs1) (S.tail hs2)))

val merge_hs_empty:
  len:nat ->
  Lemma (S.equal (merge_hs (empty_hashes len) (empty_hashes len))
                 (empty_hashes len))
let rec merge_hs_empty len =
  if len = 0 then ()
  else (empty_hashes_head len;
       empty_hashes_tail len;
       assert (S.equal (S.append #hash S.empty S.empty)
                       (S.empty #hash));
       assert (S.equal (merge_hs (empty_hashes len) (empty_hashes len))
                       (S.cons S.empty
                               (merge_hs (empty_hashes (len - 1))
                                         (empty_hashes (len - 1)))));
       merge_hs_empty (len - 1))

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

val merge_hs_slice_equal:
  ahs1:hash_ss ->
  ahs2:hash_ss{S.length ahs1 = S.length ahs2} ->
  bhs1:hash_ss ->
  bhs2:hash_ss{S.length bhs1 = S.length bhs2} ->
  i:nat -> j:nat{i <= j && j <= S.length ahs1 && j <= S.length bhs1} ->
  Lemma (requires (S.equal (S.slice ahs1 i j) (S.slice bhs1 i j) /\
                  S.equal (S.slice ahs2 i j) (S.slice bhs2 i j)))
        (ensures (S.equal (S.slice (merge_hs ahs1 ahs2) i j)
                          (S.slice (merge_hs bhs1 bhs2) i j)))
        (decreases (j - i))
let rec merge_hs_slice_equal ahs1 ahs2 bhs1 bhs2 i j =
  if i = j then ()
  else (assert (S.index ahs1 i == S.index bhs1 i);
       assert (S.index ahs2 i == S.index bhs2 i);
       merge_hs_slice_equal ahs1 ahs2 bhs1 bhs2 (i + 1) j)

val merge_hs_upd:
  hs1:hash_ss ->
  hs2:hash_ss{S.length hs1 = S.length hs2} ->
  i:nat{i < S.length hs1} ->
  v1:hash_seq -> v2:hash_seq ->
  Lemma (requires (S.equal (S.append (S.index hs1 i) (S.index hs2 i))
                           (S.append v1 v2)))
        (ensures (S.equal (merge_hs hs1 hs2)
                          (merge_hs (S.upd hs1 i v1) (S.upd hs2 i v2))))
        (decreases i)
let rec merge_hs_upd hs1 hs2 i v1 v2 =
  if S.length hs1 = 0 then ()
  else if i = 0 then ()
  else merge_hs_upd (S.tail hs1) (S.tail hs2) (i - 1) v1 v2

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

val mt_olds_inv_equiv:
  lv:nat{lv <= 32} ->
  i:nat ->
  olds1:hash_ss{S.length olds1 = 32} ->
  olds2:hash_ss{S.length olds2 = 32} ->
  Lemma (requires (mt_olds_inv lv i olds1 /\
                  S.equal (S.slice olds1 lv 32) (S.slice olds2 lv 32)))
        (ensures (mt_olds_inv lv i olds2))
        (decreases (32 - lv))
let rec mt_olds_inv_equiv lv i olds1 olds2 =
  if lv = 32 then ()
  else (assert (S.index olds1 lv == S.index olds2 lv);
       mt_olds_inv_equiv (lv + 1) (i / 2) olds1 olds2)

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

/// Correctness of construction

val empty_olds_inv:
  lv:nat{lv <= 32} ->
  Lemma (requires True)
        (ensures (mt_olds_inv lv 0 (empty_hashes 32)))
        (decreases (32 - lv))
let rec empty_olds_inv lv =
  if lv = 32 then ()
  else empty_olds_inv (lv + 1)

val create_empty_mt_inv:
  unit -> 
  Lemma (empty_olds_inv 0;
        mt_inv (create_empty_mt ()) (empty_hashes 32))
let create_empty_mt_inv _ =
  empty_olds_inv 0;
  hs_wf_elts_empty 0;
  merge_hs_empty 32;
  mt_hashes_inv_empty 0

/// Correctness of insertion

val mt_hashes_next_rel_insert_odd:
  j:nat{j % 2 = 1} ->
  hs:hash_seq{S.length hs = j} -> v:hash ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires (mt_hashes_next_rel j hs nhs))
        (ensures (mt_hashes_next_rel (j + 1)
                   (S.snoc hs v) (S.snoc nhs (hash_2 (S.last hs) v))))
let mt_hashes_next_rel_insert_odd j hs v nhs = ()

val mt_hashes_next_rel_insert_even:
  j:nat{j % 2 <> 1} ->
  hs:hash_seq{S.length hs = j} -> v:hash ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires (mt_hashes_next_rel j hs nhs))
        (ensures (mt_hashes_next_rel (j + 1) (S.snoc hs v) nhs))
let mt_hashes_next_rel_insert_even j hs v nhs = ()

val insert_head:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (S.equal (S.index (insert_ lv i j hs acc) lv)
                 (S.snoc (S.index hs lv) acc))
let insert_head lv i j hs acc = ()

val insert_inv_preserved_even:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (j % 2 <> 1 /\ mt_olds_hs_inv lv i j olds hs))
        (ensures (mt_olds_hs_inv lv i (j + 1) olds (insert_ lv i j hs acc)))
        (decreases (32 - lv))
#reset-options "--z3rlimit 20"
let insert_inv_preserved_even lv i j olds hs acc =
  let ihs = hash_ss_insert lv i j hs acc in
  mt_olds_hs_lth_inv_ok lv i j olds hs;
  assert (mt_hashes_inv lv j (merge_hs olds hs));
  merge_hs_slice_equal olds hs olds ihs (lv + 1) 32;
  remainder_2_not_1_div j;
  insert_base lv i j hs acc;

  if lv = 31 then ()
  else begin
    // Facts
    assert (S.index (merge_hs olds hs) (lv + 1) ==
           S.index (merge_hs olds ihs) (lv + 1));

    // Head proof of `mt_hashes_inv`
    mt_hashes_next_rel_insert_even j 
      (S.index (merge_hs olds hs) lv) acc
      (S.index (merge_hs olds hs) (lv + 1));
    assert (mt_hashes_next_rel (j + 1)
             (S.index (merge_hs olds ihs) lv)
             (S.index (merge_hs olds ihs) (lv + 1)));

    // Tail proof of `mt_hashes_inv`
    mt_hashes_lth_inv_equiv (lv + 1) ((j + 1) / 2)
      (merge_hs olds hs) (merge_hs olds ihs);
    mt_hashes_inv_equiv (lv + 1) ((j + 1) / 2)
      (merge_hs olds hs) (merge_hs olds ihs);
    assert (mt_hashes_inv (lv + 1) ((j + 1) / 2) (merge_hs olds ihs))
  end

val insert_inv_preserved:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv lv i olds} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  Lemma (requires (mt_olds_hs_inv lv i j olds hs))
        (ensures (mt_olds_hs_inv lv i (j + 1) olds (insert_ lv i j hs acc)))
        (decreases (32 - lv))
#reset-options "--z3rlimit 160 --max_fuel 2"
let rec insert_inv_preserved lv i j olds hs acc =
  if j % 2 = 1 
  then begin
    let ihs = hash_ss_insert lv i j hs acc in
    mt_olds_hs_lth_inv_ok lv i j olds hs;
    merge_hs_slice_equal olds hs olds ihs (lv + 1) 32;
    assert (mt_hashes_inv lv j (merge_hs olds hs));
    
    remainder_2_1_div j;
    insert_rec lv i j hs acc;

    // Recursion
    mt_hashes_lth_inv_equiv (lv + 1) (j / 2)
      (merge_hs olds hs) (merge_hs olds ihs);
    mt_hashes_inv_equiv (lv + 1) (j / 2)
      (merge_hs olds hs) (merge_hs olds ihs);
    let nacc = hash_2 (S.last (S.index hs lv)) acc in
    let rihs = insert_ (lv + 1) (i / 2) (j / 2) ihs nacc in
    insert_inv_preserved (lv + 1) (i / 2) (j / 2) olds ihs nacc;

    // Head proof of `mt_hashes_inv`
    mt_olds_hs_lth_inv_ok lv i (j + 1) olds rihs;
    mt_hashes_next_rel_insert_odd j
      (S.index (merge_hs olds hs) lv) acc
      (S.index (merge_hs olds hs) (lv + 1));
    assert (S.equal (S.index rihs lv) (S.index ihs lv));
    insert_head (lv + 1) (i / 2) (j / 2) ihs nacc;
    assert (S.equal (S.index ihs (lv + 1)) (S.index hs (lv + 1)));
    assert (mt_hashes_next_rel (j + 1)
             (S.index (merge_hs olds rihs) lv)
             (S.index (merge_hs olds rihs) (lv + 1)));

    // Tail proof of `mt_hashes_inv` by recursion
    assert (mt_olds_hs_inv (lv + 1) (i / 2) ((j + 1) / 2) olds rihs);

    assert (mt_hashes_inv lv (j + 1) (merge_hs olds rihs));
    assert (mt_olds_hs_inv lv i (j + 1) olds rihs);
    assert (mt_olds_hs_inv lv i (j + 1) olds (insert_ lv i j hs acc))
  end
  else begin
    insert_inv_preserved_even lv i j olds hs acc;
    assert (mt_olds_hs_inv lv i (j + 1) olds (insert_ lv i j hs acc))
  end
#reset-options

val mt_insert_inv_preserved:
  mt:merkle_tree{mt_wf_elts mt /\ mt_not_full mt} -> v:hash ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  Lemma (requires (mt_inv mt olds))
        (ensures (mt_inv (mt_insert mt v) olds))
let mt_insert_inv_preserved mt v olds =
  insert_inv_preserved 0 (MT?.i mt) (MT?.j mt) olds (MT?.hs mt) v

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
#reset-options "--z3rlimit 20 --max_fuel 2"
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
  mt_flush_to_inv_preserved_ 0 (MT?.i mt) idx (MT?.j mt) olds (MT?.hs mt)

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

/// Correctness of `mt_get_root` and `mt_get_path`

/// Correctness of path verification


