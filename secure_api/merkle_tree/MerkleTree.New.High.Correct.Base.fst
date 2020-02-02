module MerkleTree.New.High.Correct.Base

open MerkleTree.Spec
open MerkleTree.New.High

open FStar.Classical
open FStar.Ghost
open FStar.Seq

module S = FStar.Seq

module MTS = MerkleTree.Spec

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

#push-options "--max_fuel 1"

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
        (ensures mt_hashes_lth_inv lv 0 (empty_hashes 32))
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
    hash_2 (S.index hs (op_Multiply 2 i))
           (S.index hs (op_Multiply 2 i + 1))

#push-options "--max_fuel 2"

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
  else (mt_hashes_lth_inv_empty (lv + 1);
        mt_hashes_inv_empty (lv + 1))

val mt_hashes_lth_inv_equiv:
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hash_ss{S.length fhs1 = 32} ->
  fhs2:hash_ss{S.length fhs2 = 32} ->
  Lemma (requires mt_hashes_lth_inv lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32))
        (ensures mt_hashes_lth_inv lv j fhs2)
        (decreases (32 - lv))
let rec mt_hashes_lth_inv_equiv lv j fhs1 fhs2 =
  if lv = 31 then ()
  else (assert (S.index fhs1 lv == S.index fhs2 lv);
       mt_hashes_lth_inv_equiv (lv + 1) (j / 2) fhs1 fhs2)

#pop-options // --max_fuel = 2

val mt_hashes_inv_equiv:
  lv:nat{lv < 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs1:hash_ss{S.length fhs1 = 32 /\ mt_hashes_lth_inv lv j fhs1} ->
  fhs2:hash_ss{S.length fhs2 = 32 /\ mt_hashes_lth_inv lv j fhs2} ->
  Lemma (requires mt_hashes_inv lv j fhs1 /\
                  S.equal (S.slice fhs1 lv 32) (S.slice fhs2 lv 32))
        (ensures mt_hashes_inv lv j fhs2)
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
        (ensures S.equal (S.index (merge_hs hs1 hs2) i)
                         (S.append (S.index hs1 i) (S.index hs2 i)))
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
  Lemma (requires S.equal (S.slice ahs1 i j) (S.slice bhs1 i j) /\
                  S.equal (S.slice ahs2 i j) (S.slice bhs2 i j))
        (ensures  S.equal (S.slice (merge_hs ahs1 ahs2) i j)
                          (S.slice (merge_hs bhs1 bhs2) i j))
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
  Lemma (requires S.equal (S.append (S.index hs1 i) (S.index hs2 i))
                          (S.append v1 v2))
        (ensures S.equal (merge_hs hs1 hs2)
                         (merge_hs (S.upd hs1 i v1) (S.upd hs2 i v2)))
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
  Lemma (requires mt_olds_inv lv i olds1 /\
                  S.equal (S.slice olds1 lv 32) (S.slice olds2 lv 32))
        (ensures mt_olds_inv lv i olds2)
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
        (ensures mt_hashes_lth_inv lv j (merge_hs olds hs))
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
  j:nat ->
  fhs:hash_ss{S.length fhs = log2c j} ->
  GTot Type0 (decreases j)
let rec mt_hashes_lth_inv_log j fhs =
  if j = 0 then true
  else (S.length (S.head fhs) == j /\
       mt_hashes_lth_inv_log (j / 2) (S.tail fhs))

#push-options "--max_fuel 2"

val mt_hashes_lth_inv_log_next:
  j:nat{j > 1} ->
  fhs:hash_ss{S.length fhs = log2c j} ->
  Lemma (requires mt_hashes_lth_inv_log j fhs)
        (ensures S.length (S.head fhs) == j /\
                 S.length (S.head (S.tail fhs)) == j / 2)
let mt_hashes_lth_inv_log_next j fhs = ()

val mt_hashes_inv_log:
  j:nat ->
  fhs:hash_ss{S.length fhs = log2c j /\ mt_hashes_lth_inv_log j fhs} ->
  GTot Type0 (decreases j)
let rec mt_hashes_inv_log j fhs =
  if j <= 1 then true
  else (mt_hashes_next_rel j (S.index fhs 0) (S.index fhs 1) /\
       mt_hashes_inv_log (j / 2) (S.tail fhs))

val mt_hashes_lth_inv_log_converted_:
  lv:nat{lv <= 32} ->
  j:nat{j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32} ->
  Lemma (requires mt_hashes_lth_inv lv j fhs)
        (ensures (log2c_bound j (32 - lv);
                  mt_hashes_lth_inv_log j (S.slice fhs lv (lv + log2c j))))
        (decreases j)
let rec mt_hashes_lth_inv_log_converted_ lv j fhs =
  if j = 0 then ()
  else (log2c_bound (j / 2) (32 - (lv + 1));
       mt_hashes_lth_inv_log_converted_ (lv + 1) (j / 2) fhs)

val mt_hashes_lth_inv_log_converted:
  j:nat{j < pow2 32} ->
  fhs:hash_ss{S.length fhs = 32} ->
  Lemma (requires mt_hashes_lth_inv 0 j fhs)
        (ensures (log2c_bound j 32;
                  mt_hashes_lth_inv_log j (S.slice fhs 0 (log2c j))))
let mt_hashes_lth_inv_log_converted j fhs =
  mt_hashes_lth_inv_log_converted_ 0 j fhs

val mt_hashes_inv_log_converted_:
  lv:nat{lv <= 32} ->
  j:nat{j > 0 && j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32 /\ mt_hashes_lth_inv lv j fhs} ->
  Lemma (requires mt_hashes_inv lv j fhs)
        (ensures (log2c_bound j (32 - lv);
                  mt_hashes_lth_inv_log_converted_ lv j fhs;
                  mt_hashes_inv_log j (S.slice fhs lv (lv + log2c j))))
        (decreases j)
#restart-solver
let rec mt_hashes_inv_log_converted_ lv j fhs =
  if j = 1 then ()
  else (log2c_bound (j / 2) (32 - (lv + 1));
        mt_hashes_lth_inv_log_converted_ (lv + 1) (j / 2) fhs;
        mt_hashes_inv_log_converted_ (lv + 1) (j / 2) fhs)

val mt_hashes_inv_log_converted:
  j:nat{j > 0 && j < pow2 32} ->
  fhs:hash_ss{S.length fhs = 32 /\ mt_hashes_lth_inv 0 j fhs} ->
  Lemma (requires mt_hashes_inv 0 j fhs)
        (ensures (log2c_bound j 32;
                  mt_hashes_lth_inv_log_converted_ 0 j fhs;
                  mt_hashes_inv_log j (S.slice fhs 0 (log2c j))))
let mt_hashes_inv_log_converted j fhs =
  mt_hashes_inv_log_converted_ 0 j fhs

val hash_seq_lift: 
  hs:hash_seq -> 
  GTot (shs:MTS.hash_seq{S.length shs = S.length hs})
       (decreases (S.length hs))
let rec hash_seq_lift hs =
  if S.length hs = 0 then S.empty
  else S.cons (HRaw (S.head hs)) (hash_seq_lift (S.tail hs))

val hash_seq_lift_index:
  hs:hash_seq ->
  Lemma (requires True)
        (ensures  forall (i:nat{i < S.length hs}).
                    S.index (hash_seq_lift hs) i == HRaw (S.index hs i))
        (decreases (S.length hs))
let rec hash_seq_lift_index hs =
  if S.length hs = 0 then ()
  else hash_seq_lift_index (S.tail hs)

#pop-options // --max_fuel 2

val create_pads: len:nat -> GTot (pads:MTS.hash_seq{S.length pads = len})
let create_pads len = S.create len HPad

val hash_seq_spec:
  hs:hash_seq{S.length hs > 0} ->
  GTot (smt:MTS.merkle_tree (log2c (S.length hs)))
let hash_seq_spec hs =
  S.append (hash_seq_lift hs)
           (create_pads (pow2 (log2c (S.length hs)) - S.length hs))

val hash_seq_spec_index_raw:
  hs:hash_seq{S.length hs > 0} ->
  i:nat{i < S.length hs} ->
  Lemma (S.index (hash_seq_spec hs) i == HRaw (S.index hs i))
let hash_seq_spec_index_raw hs i =
  hash_seq_lift_index hs

// Now about recovering rightmost hashes

val mt_hashes_next_rel_lift_even:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 0 /\ mt_hashes_next_rel j hs nhs)
        (ensures MTS.mt_next_rel (log2c j)
                   (hash_seq_spec hs) (hash_seq_spec nhs))
let mt_hashes_next_rel_lift_even j hs nhs =
  hash_seq_lift_index hs;
  hash_seq_lift_index nhs

val mt_hashes_next_rel_lift_odd:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 1 /\ mt_hashes_next_rel j hs nhs)
        (ensures  MTS.mt_next_rel (log2c j)
                   (hash_seq_spec hs)
                   (S.upd (hash_seq_spec nhs)
                          (S.length nhs) (HRaw (S.last hs))))
let mt_hashes_next_rel_lift_odd j hs nhs =
  log2c_div j;
  hash_seq_lift_index hs;
  hash_seq_lift_index nhs

val mt_hashes_next_rel_next_even:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires j % 2 = 0 /\ mt_hashes_next_rel j hs nhs)
        (ensures  S.equal (hash_seq_spec nhs)
                          (mt_next_lv #(log2c j) (hash_seq_spec hs)))
let mt_hashes_next_rel_next_even j hs nhs =
  log2c_div j;
  mt_hashes_next_rel_lift_even j hs nhs;
  MTS.mt_next_rel_next_lv (log2c j)
    (hash_seq_spec hs) (hash_seq_spec nhs)

val hash_seq_spec_full:
  hs:hash_seq{S.length hs > 0} ->
  acc:hash -> actd:bool ->
  GTot (smt:MTS.merkle_tree (log2c (S.length hs)))
let hash_seq_spec_full hs acc actd =
  if actd
  then (S.upd (hash_seq_spec hs) (S.length hs) (HRaw acc))
  else hash_seq_spec hs

val hash_seq_spec_full_index_raw:
  hs:hash_seq{S.length hs > 0} ->
  acc:hash -> actd:bool -> i:nat{i < S.length hs} ->
  Lemma (S.index (hash_seq_spec_full hs acc actd) i ==
        HRaw (S.index hs i))
let hash_seq_spec_full_index_raw hs acc actd i =
  hash_seq_spec_index_raw hs i

val hash_seq_spec_full_case_true:
  hs:hash_seq{S.length hs > 0} -> acc:hash ->
  Lemma (S.index (hash_seq_spec_full hs acc true) (S.length hs) == HRaw acc)
let hash_seq_spec_full_case_true hs acc = ()  

val hash_seq_spec_full_even_next:
  j:nat{j > 0} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  acc:hash -> actd:bool ->
  Lemma
    (requires j % 2 = 0 /\ mt_hashes_next_rel j hs nhs)
    (ensures  S.equal (hash_seq_spec_full nhs acc actd)
                      (mt_next_lv #(log2c j) (hash_seq_spec_full hs acc actd)))
#restart-solver
let hash_seq_spec_full_even_next j hs nhs acc actd =
  log2c_div j;
  mt_hashes_next_rel_lift_even j hs nhs;
  if actd 
  then begin 
    MTS.mt_next_rel_upd_even_pad (log2c j)
      (hash_seq_spec hs) (hash_seq_spec nhs) (S.length hs / 2) (HRaw acc);
    MTS.mt_next_rel_next_lv (log2c j)
      (S.upd (hash_seq_spec hs) (S.length hs) (HRaw acc))
      (S.upd (hash_seq_spec nhs) (S.length nhs) (HRaw acc))
  end
  else MTS.mt_next_rel_next_lv (log2c j)
         (hash_seq_spec_full hs acc actd)
         (hash_seq_spec_full nhs acc actd)

#push-options "--z3rlimit 80"

val hash_seq_spec_full_odd_next:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  acc:hash -> actd:bool -> nacc:hash ->
  Lemma
    (requires j % 2 = 1 /\
              mt_hashes_next_rel j hs nhs /\
              nacc == (if actd then hash_2 (S.last hs) acc else S.last hs))
    (ensures  S.equal (hash_seq_spec_full nhs nacc true)
                      (mt_next_lv #(log2c j) (hash_seq_spec_full hs acc actd)))
let hash_seq_spec_full_odd_next j hs nhs acc actd nacc =
  log2c_div j;
  mt_hashes_next_rel_lift_odd j hs nhs;
  if actd
  then begin
    MTS.mt_next_rel_upd_odd (log2c j)
      (hash_seq_spec hs)
      (S.upd (hash_seq_spec nhs) (S.length nhs) (HRaw (S.last hs)))
      (S.length nhs) (HRaw acc);
    MTS.mt_next_rel_next_lv (log2c j)
      (S.upd (hash_seq_spec hs) (S.length hs) (HRaw acc))
      (S.upd (hash_seq_spec nhs) (S.length nhs) (HRaw (hash_2 (S.last hs) acc)))
  end
  else MTS.mt_next_rel_next_lv (log2c j)
         (hash_seq_spec_full hs acc actd)
         (hash_seq_spec_full nhs nacc true)

#pop-options

val hash_seq_spec_full_next:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  acc:hash -> actd:bool -> nacc:hash -> nactd:bool ->
  Lemma
    (requires mt_hashes_next_rel j hs nhs /\
              nacc == (if j % 2 = 0 then acc
                      else if actd 
                      then hash_2 (S.last hs) acc
                      else S.last hs) /\
              nactd == (actd || j % 2 = 1))
    (ensures  S.equal (hash_seq_spec_full nhs nacc nactd)
                      (mt_next_lv #(log2c j) (hash_seq_spec_full hs acc actd)))
let hash_seq_spec_full_next j hs nhs acc actd nacc nactd =
  if j % 2 = 0 
  then hash_seq_spec_full_even_next j hs nhs acc actd
  else hash_seq_spec_full_odd_next j hs nhs acc actd nacc

val mt_rhs_inv:
  j:nat ->
  smt:MTS.merkle_tree (log2c j) ->
  rhs:hash_seq{S.length rhs = log2c j} ->
  actd:bool ->
  GTot Type0 (decreases j)
let rec mt_rhs_inv j smt rhs actd =
  if j = 0 then true
  else begin
    (if j % 2 = 1 && actd 
    then (S.index smt j == HRaw (S.head rhs))
    else true) /\
    mt_rhs_inv (j / 2) (mt_next_lv #(log2c j) smt) (S.tail rhs)
      (actd || (j % 2 = 1))
  end

val mt_root_inv:
  hs0:hash_seq{S.length hs0 > 0} ->
  acc:hash -> actd:bool ->
  rt:hash ->
  GTot Type0
let mt_root_inv hs0 acc actd rt =
  MTS.mt_get_root #(log2c (S.length hs0))
    (hash_seq_spec_full hs0 acc actd) == HRaw rt

val mt_base:
  mt:merkle_tree{mt_wf_elts mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  GTot (bhs:hash_seq{S.length bhs = MT?.j mt})
let mt_base mt olds =
  S.head (merge_hs olds (MT?.hs mt))

#pop-options // --max_fuel 1

val mt_spec:
  mt:merkle_tree{mt_wf_elts mt /\ MT?.j mt > 0} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  GTot (smt:MTS.merkle_tree (log2c (MT?.j mt)))
let mt_spec mt olds =
  hash_seq_spec (mt_base mt olds)

val mt_inv: 
  mt:merkle_tree{mt_wf_elts mt} ->
  olds:hash_ss{S.length olds = 32 /\ mt_olds_inv 0 (MT?.i mt) olds} ->
  GTot Type0
let mt_inv mt olds =
  let i = MT?.i mt in
  let j = MT?.j mt in
  let hs = MT?.hs mt in
  let rhs = MT?.rhs mt in
  let fhs = merge_hs olds hs in
  let rt = MT?.mroot mt in
  log2c_bound j 32;
  mt_olds_hs_inv 0 i j olds hs /\
  (if j > 0 && MT?.rhs_ok mt
  then (mt_olds_hs_lth_inv_ok 0 i j olds hs;
       mt_hashes_lth_inv_log_converted j fhs;
       (mt_rhs_inv j (mt_spec mt olds) (S.slice rhs 0 (log2c j)) false /\
       mt_root_inv (mt_base mt olds) hash_init false rt))
  else true)

