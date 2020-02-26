module MerkleTree.New.High.Correct.Base

open FStar.Classical
open FStar.Ghost
open FStar.Seq

module S = FStar.Seq

module MTS = MerkleTree.Spec
open MerkleTree.New.High

#set-options "--z3rlimit 40 --max_fuel 0 --max_ifuel 0"

/// Sequence helpers

val seq_prefix:
  #a:Type -> s1:S.seq a -> 
  s2:S.seq a{S.length s1 <= S.length s2} ->
  GTot Type0
let seq_prefix #a s1 s2 =
  S.equal s1 (S.slice s2 0 (S.length s1)) 

val seq_head_cons:
  #a:Type -> x:a -> s:S.seq a -> 
  Lemma (S.head (S.cons x s) == x)
        [SMTPat (S.cons x s)]
let seq_head_cons #a x s = ()

val seq_tail_cons:
  #a:Type -> x:a -> s:S.seq a -> 
  Lemma (S.equal (S.tail (S.cons x s)) s)
        [SMTPat (S.cons x s)]
let seq_tail_cons #a x s = ()

/// Invariants and simulation relation of high-level Merkle tree design

// Invariants of internal hashes

val empty_hashes: (#hsz:pos) -> (len:nat) -> GTot (hs:hashess #hsz {S.length hs = len})
let empty_hashes #hsz len = S.create len S.empty

val empty_hashes_head:
  #hsz:pos ->
  len:nat{len > 0} ->
  Lemma (S.head (empty_hashes #hsz len) == S.empty)
let empty_hashes_head #_ _ = ()

val empty_hashes_tail:
  #hsz:pos ->
  len:nat{len > 0} ->
  Lemma (S.equal (S.tail (empty_hashes len))
                 (empty_hashes #hsz (len - 1)))
let empty_hashes_tail #_ _ = ()

#push-options "--max_fuel 1"
val mt_hashes_lth_inv:
  #hsz:pos ->
  lv:nat{lv <= 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hashess #hsz {S.length fhs = 32} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_hashes_lth_inv #hsz lv j fhs =
  if lv = 32 then true
  else (S.length (S.index fhs lv) == j /\
       mt_hashes_lth_inv (lv + 1) (j / 2) fhs)

val mt_hashes_lth_inv_empty:
  #hsz:pos ->
  lv:nat{lv <= 32} ->
  Lemma (requires True)
        (ensures mt_hashes_lth_inv lv 0 (empty_hashes #hsz 32))
        (decreases (32 - lv))
let rec mt_hashes_lth_inv_empty #hsz lv =
  if lv = 32 then ()
  else mt_hashes_lth_inv_empty #hsz (lv + 1)

val mt_hashes_next_rel:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  GTot Type0
let mt_hashes_next_rel #hsz #f j hs nhs =
  forall (i:nat{i < j / 2}).
    S.index nhs i == 
    f (S.index hs (op_Multiply 2 i))
           (S.index hs (op_Multiply 2 i + 1))
#pop-options

#push-options "--max_fuel 2"
val mt_hashes_inv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hashess #hsz {S.length fhs = 32 /\ mt_hashes_lth_inv lv j fhs} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_hashes_inv #hsz #f lv j fhs =
  if lv = 31 then true
  else (mt_hashes_next_rel #_ #f j (S.index fhs lv) (S.index fhs (lv + 1)) /\
       mt_hashes_inv #_ #f (lv + 1) (j / 2) fhs)

val mt_hashes_inv_empty:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  Lemma (requires True)
        (ensures (mt_hashes_lth_inv_empty #hsz lv;
                 mt_hashes_inv #hsz #f lv 0 (empty_hashes #hsz 32)))
        (decreases (32 - lv))
let rec mt_hashes_inv_empty #hsz #f lv =
  if lv = 31 then ()
  else (mt_hashes_lth_inv_empty #hsz (lv + 1);
        mt_hashes_inv_empty #_ #f (lv + 1))

val mt_hashes_lth_inv_equiv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hashess{S.length fhs1 = 32} ->
  fhs2:hashess{S.length fhs2 = 32} ->
  Lemma (requires mt_hashes_lth_inv lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32))
        (ensures mt_hashes_lth_inv #hsz lv j fhs2)
        (decreases (32 - lv))
let rec mt_hashes_lth_inv_equiv #hsz #f lv j fhs1 fhs2 =
  if lv = 31 then ()
  else (assert (S.index fhs1 lv == S.index fhs2 lv);
       mt_hashes_lth_inv_equiv #_ #f (lv + 1) (j / 2) fhs1 fhs2)
#pop-options

#push-options "--max_fuel 1"
val mt_hashes_inv_equiv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hashess #hsz {S.length fhs1 = 32 /\ mt_hashes_lth_inv lv j fhs1} ->
  fhs2:hashess #hsz {S.length fhs2 = 32 /\ mt_hashes_lth_inv lv j fhs2} ->
  Lemma (requires mt_hashes_inv #_ #f lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32))
        (ensures mt_hashes_inv #_ #f lv j fhs2)
        (decreases (32 - lv))
let rec mt_hashes_inv_equiv #hsz #f lv j fhs1 fhs2 =
  if lv = 31 then ()
  else (assert (S.index fhs1 lv == S.index fhs2 lv);
       assert (S.index fhs1 (lv + 1) == S.index fhs2 (lv + 1));
       mt_hashes_inv_equiv #_ #f (lv + 1) (j / 2) fhs1 fhs2)

val merge_hs:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs1:hashess #hsz ->
  hs2:hashess #hsz {S.length hs1 = S.length hs2} ->
  GTot (mhs:hashess #hsz {S.length mhs = S.length hs1})
       (decreases (S.length hs1))
let rec merge_hs #hsz #f hs1 hs2 =
  if S.length hs1 = 0 then S.empty
  else (S.cons (S.append (S.head hs1) (S.head hs2))
               (merge_hs #_ #f (S.tail hs1) (S.tail hs2)))

val merge_hs_empty:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  len:nat ->
  Lemma (S.equal (merge_hs #_ #f (empty_hashes #hsz len) (empty_hashes #hsz len))
                 (empty_hashes #hsz len))
let rec merge_hs_empty #hsz #f len =
  if len = 0 then ()
  else (empty_hashes_head #hsz len;
       empty_hashes_tail #hsz len;
       assert (S.equal (S.append #(hash #hsz) S.empty S.empty)
                       (S.empty #(hash #hsz)));
       assert (S.equal (merge_hs #_ #f (empty_hashes len) (empty_hashes len))
                       (S.cons S.empty
                               (merge_hs #_ #f (empty_hashes (len - 1))
                                               (empty_hashes (len - 1)))));
       merge_hs_empty #_ #f (len - 1))

val merge_hs_index:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs1:hashess ->
  hs2:hashess{S.length hs1 = S.length hs2} ->
  i:nat{i < S.length hs1} ->
  Lemma (requires True)
        (ensures S.equal (S.index (merge_hs #_ #f hs1 hs2) i)
                         (S.append (S.index hs1 i) (S.index hs2 i)))
        (decreases (S.length hs1))
        [SMTPat (S.index (merge_hs #_ #f hs1 hs2) i)]
let rec merge_hs_index #hsz #f hs1 hs2 i =
  if S.length hs1 = 0 then ()
  else if i = 0 then ()
  else merge_hs_index #_ #f (S.tail hs1) (S.tail hs2) (i - 1)

val merge_hs_slice_equal:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  ahs1:hashess #hsz ->
  ahs2:hashess #hsz {S.length ahs1 = S.length ahs2} ->
  bhs1:hashess #hsz ->
  bhs2:hashess #hsz {S.length bhs1 = S.length bhs2} ->
  i:nat -> j:nat{i <= j && j <= S.length ahs1 && j <= S.length bhs1} ->
  Lemma (requires S.equal (S.slice ahs1 i j) (S.slice bhs1 i j) /\
                  S.equal (S.slice ahs2 i j) (S.slice bhs2 i j))
        (ensures  S.equal (S.slice (merge_hs #_ #f ahs1 ahs2) i j)
                          (S.slice (merge_hs #_ #f bhs1 bhs2) i j))
        (decreases (j - i))
let rec merge_hs_slice_equal #_ #f ahs1 ahs2 bhs1 bhs2 i j =
  if i = j then ()
  else (assert (S.index ahs1 i == S.index bhs1 i);
       assert (S.index ahs2 i == S.index bhs2 i);
       merge_hs_slice_equal #_ #f ahs1 ahs2 bhs1 bhs2 (i + 1) j)

val merge_hs_upd:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs1:hashess #hsz ->
  hs2:hashess #hsz {S.length hs1 = S.length hs2} ->
  i:nat{i < S.length hs1} ->
  v1:hashes #hsz -> v2:hashes #hsz ->
  Lemma (requires S.equal (S.append (S.index hs1 i) (S.index hs2 i))
                          (S.append v1 v2))
        (ensures S.equal (merge_hs #_ #f hs1 hs2)
                         (merge_hs #_ #f (S.upd hs1 i v1) (S.upd hs2 i v2)))
        (decreases i)
let rec merge_hs_upd #_ #f hs1 hs2 i v1 v2 =
  if S.length hs1 = 0 then ()
  else if i = 0 then ()
  else merge_hs_upd #_ #f (S.tail hs1) (S.tail hs2) (i - 1) v1 v2

val mt_olds_inv:
  #hsz:pos -> 
  lv:nat{lv <= 32} ->
  i:nat ->
  olds:hashess #hsz {S.length olds = 32} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_olds_inv #hsz lv i olds =
  if lv = 32 then true
  else (let ofs = offset_of i in
       S.length (S.index olds lv) == ofs /\
       mt_olds_inv #hsz (lv + 1) (i / 2) olds)

val mt_olds_inv_equiv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  i:nat ->
  olds1:hashess #hsz {S.length olds1 = 32} ->
  olds2:hashess #hsz {S.length olds2 = 32} ->
  Lemma (requires mt_olds_inv #hsz lv i olds1 /\
                  S.equal (S.slice olds1 lv 32) (S.slice olds2 lv 32))
        (ensures mt_olds_inv #hsz lv i olds2)
        (decreases (32 - lv))
let rec mt_olds_inv_equiv #hsz #f lv i olds1 olds2 =
  if lv = 32 then ()
  else (assert (S.index olds1 lv == S.index olds2 lv);
       mt_olds_inv_equiv #_ #f (lv + 1) (i / 2) olds1 olds2)

val mt_olds_hs_lth_inv_ok:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts #hsz lv hs i j} ->
  Lemma (requires True)
        (ensures mt_hashes_lth_inv #hsz lv j (merge_hs #_ #f olds hs))
        (decreases (32 - lv))
let rec mt_olds_hs_lth_inv_ok #hsz #f lv i j olds hs =
  if lv = 32 then ()
  else (mt_olds_hs_lth_inv_ok #_ #f (lv + 1) (i / 2) (j / 2) olds hs)

val mt_olds_hs_inv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv)} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz lv i olds} ->
  hs:hashess #hsz {S.length hs = 32 /\ hs_wf_elts #hsz lv hs i j} ->
  GTot Type0
let mt_olds_hs_inv #hsz #f lv i j olds hs =
  mt_olds_hs_lth_inv_ok #_ #f lv i j olds hs;
  mt_hashes_inv #_ #f lv j (merge_hs #_ #f olds hs)

// Relation between valid internal hashes (satisfying `mt_olds_hs_inv`) and
// the spec. While giving such relation, all rightmost hashes are recovered.
// Note that `MT?.rhs` after `construct_rhs` does NOT contain all rightmost
// hashes; it has partial rightmost hashes that are enough to calculate
// Merkle paths.

val log2: n:nat{n > 0} -> GTot (c:nat{pow2 c <= n && n < pow2 (c+1)})
let rec log2 n =
  if n = 1 then 0
  else 1 + log2 (n / 2)

val log2_bound:
  n:nat{n > 0} -> c:nat{n < pow2 c} ->
  Lemma (log2 n <= c-1)
let rec log2_bound n c =
  if n = 1 then ()
  else log2_bound (n / 2) (c - 1)

val log2_div:
  n:nat{n > 1} ->
  Lemma (log2 (n / 2) = log2 n - 1)
let log2_div n = ()

val log2c: 
  n:nat -> 
  GTot (c:nat{c = 0 || (pow2 (c-1) <= n && n < pow2 c)})
let log2c n =
  if n = 0 then 0 else (log2 n + 1)

val log2c_div:
  n:nat{n > 0} ->
  Lemma (log2c (n / 2) = log2c n - 1)
let log2c_div n = ()

val log2c_bound:
  n:nat -> c:nat{n < pow2 c} ->
  Lemma (log2c n <= c)
let rec log2c_bound n c =
  if n = 0 then ()
  else log2c_bound (n / 2) (c - 1)

val mt_hashes_lth_inv_log:
  #hsz:pos ->
  j:nat ->
  fhs:hashess #hsz {S.length fhs = log2c j} ->
  GTot Type0 (decreases j)
let rec mt_hashes_lth_inv_log #hsz j fhs =
  if j = 0 then true
  else (S.length (S.head fhs) == j /\
       mt_hashes_lth_inv_log #hsz (j / 2) (S.tail fhs))
#pop-options

#push-options "--max_fuel 2"
val mt_hashes_lth_inv_log_next:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  fhs:hashess #hsz {S.length fhs = log2c j} ->
  Lemma (requires mt_hashes_lth_inv_log #hsz j fhs)
        (ensures S.length (S.head fhs) == j /\
                 S.length (S.head (S.tail fhs)) == j / 2)
let mt_hashes_lth_inv_log_next #_ #_ _ _ = ()

val mt_hashes_inv_log:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  fhs:hashess #hsz {S.length fhs = log2c j /\ mt_hashes_lth_inv_log #hsz j fhs} ->
  GTot Type0 (decreases j)
let rec mt_hashes_inv_log #hsz #f j fhs =
  if j <= 1 then true
  else (mt_hashes_next_rel #_ #f j (S.index fhs 0) (S.index fhs 1) /\
       mt_hashes_inv_log #_ #f (j / 2) (S.tail fhs))

val mt_hashes_lth_inv_log_converted_:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hashess #hsz {S.length fhs = 32} ->
  Lemma (requires mt_hashes_lth_inv #hsz lv j fhs)
        (ensures (log2c_bound j (32 - lv);
                  mt_hashes_lth_inv_log #hsz j (S.slice fhs lv (lv + log2c j))))
        (decreases j)
let rec mt_hashes_lth_inv_log_converted_ #_ #f lv j fhs =
  if j = 0 then ()
  else (log2c_bound (j / 2) (32 - (lv + 1));
       mt_hashes_lth_inv_log_converted_ #_ #f (lv + 1) (j / 2) fhs)

val mt_hashes_lth_inv_log_converted:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j < pow2 32} ->
  fhs:hashess #hsz {S.length fhs = 32} ->
  Lemma (requires mt_hashes_lth_inv #hsz 0 j fhs)
        (ensures (log2c_bound j 32;
                  mt_hashes_lth_inv_log #hsz j (S.slice fhs 0 (log2c j))))
let mt_hashes_lth_inv_log_converted #_ #f j fhs =
  mt_hashes_lth_inv_log_converted_ #_ #f 0 j fhs

val mt_hashes_inv_log_converted_:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  lv:nat{lv <= 32} ->
  j:nat{j > 0 && j < pow2 (32 - lv)} ->
  fhs:hashess #hsz {S.length fhs = 32 /\ mt_hashes_lth_inv #hsz lv j fhs} ->
  Lemma (requires mt_hashes_inv #_ #f lv j fhs)
        (ensures (log2c_bound j (32 - lv);
                  mt_hashes_lth_inv_log_converted_ #_ #f lv j fhs;
                  mt_hashes_inv_log #_ #f j (S.slice fhs lv (lv + log2c j))))
        (decreases j)
#pop-options

#push-options "--z3rlimit 50 --initial_fuel 2 --max_fuel 2"
let rec mt_hashes_inv_log_converted_ #_ #f lv j fhs =
  if j = 1 then ()
  else (log2c_bound (j / 2) (32 - (lv + 1));
        mt_hashes_lth_inv_log_converted_ #_ #f (lv + 1) (j / 2) fhs;
        mt_hashes_inv_log_converted_ #_ #f (lv + 1) (j / 2) fhs)
#pop-options

val mt_hashes_inv_log_converted:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 0 && j < pow2 32} ->
  fhs:hashess #hsz {S.length fhs = 32 /\ mt_hashes_lth_inv #hsz 0 j fhs} ->
  Lemma (requires mt_hashes_inv #_ #f 0 j fhs)
        (ensures (log2c_bound j 32;
                  mt_hashes_lth_inv_log_converted_ #_ #f 0 j fhs;
                  mt_hashes_inv_log #_ #f j (S.slice fhs 0 (log2c j))))
let mt_hashes_inv_log_converted #_ #f j fhs =
  mt_hashes_inv_log_converted_ #_ #f 0 j fhs

val hash_seq_lift: 
  #hsz:pos -> 
  hs:hashes #hsz -> 
  GTot (shs:MTS.hashes #hsz {S.length shs = S.length hs})
       (decreases (S.length hs))
let rec hash_seq_lift #hsz hs =
  if S.length hs = 0 then S.empty
  else S.cons (MTS.HRaw (S.head hs)) (hash_seq_lift #hsz (S.tail hs))

#push-options "--z3rlimit 50 --initial_fuel 2 --max_fuel 2"
val hash_seq_lift_index:
  #hsz:pos -> 
  hs:hashes #hsz ->
  Lemma (requires True)
        (ensures  forall (i:nat{i < S.length hs}).
                    S.index (hash_seq_lift #hsz hs) i == MTS.HRaw (S.index hs i))
        (decreases (S.length hs))
let rec hash_seq_lift_index #hsz hs =
  if S.length hs = 0 then ()
  else hash_seq_lift_index #hsz (S.tail hs)
#pop-options

val create_pads: #hsz:pos -> len:nat -> GTot (pads:MTS.hashes #hsz {S.length pads = len})
let create_pads #hsz len = S.create len (MTS.HPad #hsz)

val hash_seq_spec:
  #hsz:pos -> 
  hs:hashes #hsz {S.length hs > 0} ->
  GTot (smt:MTS.merkle_tree #hsz (log2c (S.length hs)))
let hash_seq_spec #hsz hs =
  S.append (hash_seq_lift #hsz hs)
           (create_pads (pow2 (log2c (S.length hs)) - S.length hs))

val hash_seq_spec_index_raw:
  #hsz:pos -> 
  hs:hashes #hsz {S.length hs > 0} ->
  i:nat{i < S.length hs} ->
  Lemma (S.index (hash_seq_spec #hsz hs) i == MTS.HRaw #hsz (S.index hs i))
let hash_seq_spec_index_raw #hsz hs i =
  hash_seq_lift_index #hsz hs

// Now about recovering rightmost hashes

#push-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"
val mt_hashes_next_rel_lift_even:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 0 /\ mt_hashes_next_rel #_ #f j hs nhs)
        (ensures MTS.mt_next_rel #_ #f (log2c j)
                   (hash_seq_spec #hsz hs) (hash_seq_spec #hsz nhs))
let mt_hashes_next_rel_lift_even #hsz #_ j hs nhs =
  hash_seq_lift_index #hsz hs;
  hash_seq_lift_index #hsz nhs

val mt_hashes_next_rel_lift_odd:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 1 /\ mt_hashes_next_rel #_ #f j hs nhs)
        (ensures  MTS.mt_next_rel #_ #f (log2c j)
                   (hash_seq_spec #hsz hs)
                   (S.upd (hash_seq_spec #hsz nhs)
                          (S.length nhs) (MTS.HRaw (S.last hs))))
let mt_hashes_next_rel_lift_odd #hsz #_ j hs nhs =
  log2c_div j;
  hash_seq_lift_index #hsz hs;
  hash_seq_lift_index #hsz nhs

val mt_hashes_next_rel_next_even:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 0 /\ mt_hashes_next_rel #_ #f j hs nhs)
        (ensures  S.equal (hash_seq_spec #hsz nhs)
                          (MTS.mt_next_lv #_ #f #(log2c j) (hash_seq_spec #hsz hs)))
let mt_hashes_next_rel_next_even #hsz #f j hs nhs =
  log2c_div j;
  mt_hashes_next_rel_lift_even #_ #f j hs nhs;
  MTS.mt_next_rel_next_lv #_ #f (log2c j)
    (hash_seq_spec #hsz hs) (hash_seq_spec #hsz nhs)

val hash_seq_spec_full:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs:hashes #hsz {S.length hs > 0} ->
  acc:hash #hsz -> actd:bool ->
  GTot (smt:MTS.merkle_tree #hsz (log2c (S.length hs)))
let hash_seq_spec_full #hsz #f hs acc actd =
  if actd
  then (S.upd (hash_seq_spec #hsz hs) (S.length hs) (MTS.HRaw acc))
  else hash_seq_spec #hsz hs

val hash_seq_spec_full_index_raw:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs:hashes #hsz {S.length hs > 0} ->
  acc:hash #hsz -> actd:bool -> i:nat{i < S.length hs} ->
  Lemma (S.index (hash_seq_spec_full #_ #f hs acc actd) i ==
        MTS.HRaw (S.index hs i))
let hash_seq_spec_full_index_raw #hsz #_ hs acc actd i =
  hash_seq_spec_index_raw #hsz hs i

val hash_seq_spec_full_case_true:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs:hashes #hsz {S.length hs > 0} -> acc:hash #hsz ->
  Lemma (S.index (hash_seq_spec_full #_ #f hs acc true) (S.length hs) == MTS.HRaw acc)
let hash_seq_spec_full_case_true #_ #_ _ _ = ()  

val hash_seq_spec_full_even_next:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 0} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  acc:hash #hsz -> actd:bool ->
  Lemma
    (requires j % 2 = 0 /\ mt_hashes_next_rel #_ #f j hs nhs)
    (ensures  S.equal (hash_seq_spec_full #_ #f nhs acc actd)
                      (MTS.mt_next_lv #_ #f #(log2c j) (hash_seq_spec_full #_ #f hs acc actd)))

#restart-solver
#push-options "--quake 1/3 --z3rlimit 100 --fuel 2 --ifuel 1"
let hash_seq_spec_full_even_next #hsz #f j hs nhs acc actd =
  log2c_div j;
  mt_hashes_next_rel_lift_even #_ #f j hs nhs;
  if actd 
  then begin 
    MTS.mt_next_rel_upd_even_pad #_ #f (log2c j)
      (hash_seq_spec #hsz hs) (hash_seq_spec #hsz nhs) (S.length hs / 2) (MTS.HRaw acc);
    let n = log2c j in
    let mt = S.upd (hash_seq_spec #hsz hs) (S.length hs) (MTS.HRaw acc) in
    let nmt = S.upd (hash_seq_spec #hsz nhs) (S.length nhs) (MTS.HRaw acc) in
    // assume (MTS.mt_next_rel #_ #f n mt nmt);
    MTS.mt_next_rel_next_lv #_ #f n mt nmt
  end
  else MTS.mt_next_rel_next_lv #_ #f (log2c j)
         (hash_seq_spec_full #_ #f hs acc actd)
         (hash_seq_spec_full #_ #f nhs acc actd)
#pop-options

#push-options "--z3rlimit 80"
val hash_seq_spec_full_odd_next:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  acc:hash #hsz -> actd:bool -> nacc:hash #hsz ->
  Lemma
    (requires j % 2 = 1 /\
              mt_hashes_next_rel #_ #f j hs nhs /\
              nacc == (if actd then f (S.last hs) acc else S.last hs))
    (ensures  S.equal (hash_seq_spec_full #_ #f nhs nacc true)
                      (MTS.mt_next_lv #_ #f #(log2c j) (hash_seq_spec_full #_ #f hs acc actd)))
let hash_seq_spec_full_odd_next #hsz #f j hs nhs acc actd nacc =
  log2c_div j;
  mt_hashes_next_rel_lift_odd #_ #f j hs nhs;
  if actd
  then begin
    MTS.mt_next_rel_upd_odd #_ #f (log2c j)
      (hash_seq_spec #hsz hs)
      (S.upd (hash_seq_spec #hsz nhs) (S.length nhs) (MTS.HRaw (S.last hs)))
      (S.length nhs) (MTS.HRaw acc);
    MTS.mt_next_rel_next_lv #_ #f (log2c j)
      (S.upd (hash_seq_spec #hsz hs) (S.length hs) (MTS.HRaw acc))
      (S.upd (hash_seq_spec #hsz nhs) (S.length nhs) (MTS.HRaw (f (S.last hs) acc)))
  end
  else MTS.mt_next_rel_next_lv #_ #f (log2c j)
         (hash_seq_spec_full #_ #f hs acc actd)
         (hash_seq_spec_full #_ #f nhs nacc true)

#pop-options

val hash_seq_spec_full_next:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat{j > 1} ->
  hs:hashes #hsz {S.length hs = j} ->
  nhs:hashes #hsz {S.length nhs = j / 2} ->
  acc:hash #hsz -> actd:bool -> nacc:hash #hsz -> nactd:bool ->
  Lemma
    (requires mt_hashes_next_rel #_ #f j hs nhs /\
              nacc == (if j % 2 = 0 then acc
                      else if actd 
                      then f (S.last hs) acc
                      else S.last hs) /\
              nactd == (actd || j % 2 = 1))
    (ensures  S.equal (hash_seq_spec_full #_ #f nhs nacc nactd)
                      (MTS.mt_next_lv #_ #f #(log2c j) (hash_seq_spec_full #_ #f hs acc actd)))
let hash_seq_spec_full_next #_ #f j hs nhs acc actd nacc nactd =
  if j % 2 = 0 
  then hash_seq_spec_full_even_next #_ #f j hs nhs acc actd
  else hash_seq_spec_full_odd_next #_ #f j hs nhs acc actd nacc

val mt_rhs_inv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  j:nat ->
  smt:MTS.merkle_tree #hsz (log2c j) ->
  rhs:hashes #hsz {S.length rhs = log2c j} ->
  actd:bool ->
  GTot Type0 (decreases j)
let rec mt_rhs_inv #_ #f j smt rhs actd =
  if j = 0 then true
  else begin
    (if j % 2 = 1 && actd 
    then (S.index smt j == MTS.HRaw (S.head rhs))
    else true) /\
    mt_rhs_inv #_ #f (j / 2) (MTS.mt_next_lv #_ #f #(log2c j) smt) (S.tail rhs)
      (actd || (j % 2 = 1))
  end

val mt_root_inv:
  #hsz:pos -> #f:MTS.hash_fun_t #hsz ->
  hs0:hashes #hsz {S.length hs0 > 0} ->
  acc:hash #hsz -> actd:bool ->
  rt:hash #hsz ->
  GTot Type0
let mt_root_inv #_ #f hs0 acc actd rt =
  MTS.mt_get_root #_ #f #(log2c (S.length hs0))
    (hash_seq_spec_full #_ #f hs0 acc actd) == MTS.HRaw rt

val mt_base:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} ->
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz 0 (MT?.i mt) olds} ->
  GTot (bhs:hashes #hsz {S.length bhs = MT?.j mt})
let mt_base #hsz mt olds =
  S.head (merge_hs #hsz #(MT?.hash_fun mt) olds (MT?.hs mt))

#pop-options // --max_fuel 1

val mt_spec:
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt /\ MT?.j mt > 0} ->
  olds:hashess{S.length olds = 32 /\ mt_olds_inv #hsz 0 (MT?.i mt) olds} ->
  GTot (smt:MTS.merkle_tree #hsz (log2c (MT?.j mt)))
let mt_spec #hsz mt olds =
  hash_seq_spec #_ (mt_base mt olds)

val mt_inv: 
  #hsz:pos -> 
  mt:merkle_tree #hsz {mt_wf_elts mt} ->
  olds:hashess{S.length olds = 32 /\ mt_olds_inv #hsz 0 (MT?.i mt) olds} ->
  GTot Type0
let mt_inv #hsz mt olds =
  let i = MT?.i mt in
  let j = MT?.j mt in
  let hs = MT?.hs mt in
  let rhs = MT?.rhs mt in
  let f = MT?.hash_fun mt in
  let fhs = merge_hs #hsz #f olds hs in
  let rt = MT?.mroot mt in
  log2c_bound j 32;
  mt_olds_hs_inv #_ #f 0 i j olds hs /\
  (if j > 0 && MT?.rhs_ok mt
  then (mt_olds_hs_lth_inv_ok #_ #f 0 i j olds hs;
       mt_hashes_lth_inv_log_converted #_ #f j fhs;
       (mt_rhs_inv #_ #f j (mt_spec mt olds) (S.slice rhs 0 (log2c j)) false /\
       mt_root_inv #_ #f (mt_base mt olds) hash_init false rt))
  else true)

