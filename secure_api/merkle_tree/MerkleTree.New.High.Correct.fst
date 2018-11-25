module MerkleTree.New.High.Correct

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec
open MerkleTree.New.High

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
#reset-options "--z3rlimit 20"

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
    hash_2 (S.index hs (op_Multiply 2 i))
           (S.index hs (op_Multiply 2 i + 1))

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

// Construction of spec from internal hashes, 
// and invariants of rightmost hashes.

val log2: n:nat{n > 0} -> GTot (c:nat{pow2 c <= n && n < pow2 (c+1)})
let rec log2 n =
  if n = 1 then 0
  else 1 + log2 (n / 2)

val log2_bound:
  n:nat{n > 0} -> c:nat{n < pow2 c} ->
  Lemma (log2 n <= c-1)
        [SMTPat (n < pow2 c)]
let rec log2_bound n c =
  if n = 1 then ()
  else log2_bound (n / 2) (c - 1)

val log2_div:
  n:nat{n > 1} ->
  Lemma (log2 (n / 2) = log2 n - 1)
let rec log2_div n = ()

val log2c: 
  n:nat -> 
  GTot (c:nat{c = 0 || (pow2 (c-1) <= n && n < pow2 c)})
let log2c n =
  if n = 0 then 0 else (log2 n + 1)

val log2c_div:
  n:nat{n > 0} ->
  Lemma (log2c (n / 2) = log2c n - 1)
        [SMTPatOr [[SMTPat (log2c (n / 2))];
                  [SMTPat (log2c n - 1)]]]
let rec log2c_div n = ()

val log2c_bound:
  n:nat -> c:nat{n < pow2 c} ->
  Lemma (log2c n <= c)
        [SMTPat (n < pow2 c)]
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

val mt_hashes_lth_inv_log_next:
  j:nat{j > 1} ->
  fhs:hash_ss{S.length fhs = log2c j} ->
  Lemma (requires (mt_hashes_lth_inv_log j fhs))
        (ensures (S.length (S.head fhs) == j /\
                 S.length (S.head (S.tail fhs)) == j / 2))
let rec mt_hashes_lth_inv_log_next j fhs = ()

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
  Lemma (requires (mt_hashes_lth_inv lv j fhs))
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
  Lemma (requires (mt_hashes_lth_inv 0 j fhs))
        (ensures (log2c_bound j 32;
                 mt_hashes_lth_inv_log j (S.slice fhs 0 (log2c j))))
let rec mt_hashes_lth_inv_log_converted j fhs =
  mt_hashes_lth_inv_log_converted_ 0 j fhs

val mt_hashes_inv_log_converted_:
  lv:nat{lv <= 32} ->
  j:nat{j > 0 && j < pow2 (32 - lv)} ->
  fhs:hash_ss{S.length fhs = 32 /\ mt_hashes_lth_inv lv j fhs} ->
  Lemma (requires (mt_hashes_inv lv j fhs))
        (ensures (mt_hashes_lth_inv_log_converted_ lv j fhs;
                 mt_hashes_inv_log j (S.slice fhs lv (lv + log2c j))))
        (decreases j)
let rec mt_hashes_inv_log_converted_ lv j fhs =
  if j = 1 then ()
  else (mt_hashes_lth_inv_log_converted_ (lv + 1) (j / 2) fhs;
       mt_hashes_inv_log_converted_ (lv + 1) (j / 2) fhs)

val mt_hashes_inv_log_converted:
  j:nat{j > 0 && j < pow2 32} ->
  fhs:hash_ss{S.length fhs = 32 /\ mt_hashes_lth_inv 0 j fhs} ->
  Lemma (requires (mt_hashes_inv 0 j fhs))
        (ensures (mt_hashes_lth_inv_log_converted_ 0 j fhs;
                 mt_hashes_inv_log j (S.slice fhs 0 (log2c j))))
let rec mt_hashes_inv_log_converted j fhs =
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
        (ensures (forall (i:nat{i < S.length hs}).
                   S.index (hash_seq_lift hs) i == HRaw (S.index hs i)))
        (decreases (S.length hs))
let rec hash_seq_lift_index hs =
  if S.length hs = 0 then ()
  else hash_seq_lift_index (S.tail hs)

val create_pads: len:nat -> GTot (pads:MTS.hash_seq{S.length pads = len})
let create_pads len = S.create len HPad

val hash_seq_spec:
  hs:hash_seq{S.length hs > 0} ->
  GTot (smt:MTS.merkle_tree (log2c (S.length hs)))
let hash_seq_spec hs =
  S.append (hash_seq_lift hs)
           (create_pads (pow2 (log2c (S.length hs)) - S.length hs))

val hs_sim:
  j:nat ->
  hs:hash_ss{
    S.length hs = log2c j /\ 
    mt_hashes_lth_inv_log j hs} ->
  smt:MTS.merkle_tree (log2c j) ->
  GTot Type0 (decreases j)
let rec hs_sim j hs smt =
  if j = 0 then true
  else (seq_prefix (hash_seq_lift (S.head hs)) smt /\
       hs_sim (j / 2) (S.tail hs) (mt_next_lv #(log2c j) smt))

val mt_hashes_next_rel_lift_even:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires (j % 2 = 0 /\ mt_hashes_next_rel j hs nhs))
        (ensures (MTS.mt_next_rel (log2c j)
                   (hash_seq_spec hs) (hash_seq_spec nhs)))
let mt_hashes_next_rel_lift_even j hs nhs =
  hash_seq_lift_index hs;
  hash_seq_lift_index nhs

val mt_hashes_next_rel_lift_odd:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires (j % 2 = 1 /\ mt_hashes_next_rel j hs nhs))
        (ensures (MTS.mt_next_rel (log2c j)
                   (hash_seq_spec hs)
                   (S.upd (hash_seq_spec nhs)
                          (S.length nhs) (HRaw (S.last hs)))))
let mt_hashes_next_rel_lift_odd j hs nhs =
  hash_seq_lift_index hs;
  hash_seq_lift_index nhs

val mt_hashes_next_rel_next_even:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  Lemma (requires (j % 2 = 0 /\ mt_hashes_next_rel j hs nhs))
        (ensures (S.equal (hash_seq_spec nhs)
                          (mt_next_lv #(log2c j) (hash_seq_spec hs))))
let mt_hashes_next_rel_next_even j hs nhs =
  mt_hashes_next_rel_lift_even j hs nhs;
  MTS.mt_next_rel_next_lv (log2c j)
    (hash_seq_spec hs) (hash_seq_spec nhs)

// TODO: use `actd` to build a valid `hs`?
val mt_hashes_inv_log_sim:
  j:nat{j > 0} ->
  hs:hash_ss{
    S.length hs = log2c j /\ 
    mt_hashes_lth_inv_log j hs /\
    mt_hashes_inv_log j hs} ->
  Lemma (requires True)
        (ensures (hs_sim j hs (hash_seq_spec (S.head hs))))
let rec mt_hashes_inv_log_sim j hs =
  admit ()

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
  rt:hash -> GTot Type0
let mt_root_inv hs0 rt =
  MTS.mt_get_root #(log2c (S.length hs0)) (hash_seq_spec hs0) == HRaw rt

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
  mt_olds_hs_inv 0 i j olds hs /\
  (if j > 0 && MT?.rhs_ok mt
  then (mt_olds_hs_lth_inv_ok 0 i j olds hs;
       mt_hashes_lth_inv_log_converted j fhs;
       (let bhs = S.append (S.head olds) (S.head hs) in
       mt_rhs_inv j (hash_seq_spec bhs) (S.slice rhs 0 (log2c j)) false /\
       mt_root_inv bhs rt))
  else true)

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

/// Correctness of rightmost hashes

// Localized version of `construct_rhs`
val construct_rhs_full:
  j:nat ->
  fhs:hash_ss{
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log j fhs} ->
  acc:hash ->
  actd:bool ->
  GTot (rhs:hash_seq{S.length rhs = log2c j} * hash) (decreases j)
let rec construct_rhs_full j fhs acc actd =
  if j = 0 then (S.empty, acc)
  else begin
    if j % 2 = 0
    then (let nrhsh = construct_rhs_full (j / 2) (S.tail fhs) acc actd in
         (S.cons hash_init (fst nrhsh), snd nrhsh))
    else (let rhd = if actd then acc else hash_init in
         let nacc = if actd 
                    then hash_2 (S.last (S.head fhs)) acc
                    else S.last (S.head fhs) in
         let nrhsh = construct_rhs_full (j / 2) (S.tail fhs) nacc true in
         (S.cons rhd (fst nrhsh), snd nrhsh))
  end

val construct_rhs_full_base:
  hs:hash_seq{S.length hs > 0} ->
  acc:hash -> actd:bool ->
  GTot (smt:MTS.merkle_tree (log2c (S.length hs)))
let construct_rhs_full_base hs acc actd =
  if actd
  then (S.upd (hash_seq_spec hs) (S.length hs) (HRaw acc))
  else hash_seq_spec hs

val construct_rhs_full_base_case_true:
  hs:hash_seq{S.length hs > 0} ->
  acc:hash ->
  Lemma (S.index (construct_rhs_full_base hs acc true) (S.length hs) == 
        HRaw acc)
let construct_rhs_full_base_case_true hs acc = ()  

val construct_rhs_full_base_even_next:
  j:nat{j > 0} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  acc:hash -> actd:bool ->
  Lemma
    (requires (j % 2 = 0 /\ mt_hashes_next_rel j hs nhs))
    (ensures (S.equal (construct_rhs_full_base nhs acc actd)
                      (mt_next_lv #(log2c j)
                        (construct_rhs_full_base hs acc actd))))
#reset-options "--z3rlimit 40"
let construct_rhs_full_base_even_next j hs nhs acc actd =
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
         (construct_rhs_full_base hs acc actd)
         (construct_rhs_full_base nhs acc actd)
#reset-options

val construct_rhs_full_base_odd_next:
  j:nat{j > 1} ->
  hs:hash_seq{S.length hs = j} ->
  nhs:hash_seq{S.length nhs = j / 2} ->
  acc:hash -> actd:bool -> nacc:hash ->
  Lemma
    (requires (j % 2 = 1 /\
              mt_hashes_next_rel j hs nhs /\
              nacc == (if actd then hash_2 (S.last hs) acc else S.last hs)))
    (ensures (S.equal (construct_rhs_full_base nhs nacc true)
                      (mt_next_lv #(log2c j)
                        (construct_rhs_full_base hs acc actd))))
#reset-options "--z3rlimit 40"
let construct_rhs_full_base_odd_next j hs nhs acc actd nacc =
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
         (hash_seq_spec hs)
         (S.upd (hash_seq_spec nhs) (S.length nhs) (HRaw (S.last hs)))
#reset-options

val construct_rhs_full_inv_ok_0:
  fhs:hash_ss{
    S.length fhs = 1 /\
    mt_hashes_lth_inv_log 1 fhs /\
    mt_hashes_inv_log 1 fhs} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_full 1 fhs acc actd in
                 mt_rhs_inv 1
                   (construct_rhs_full_base (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #1
                   (construct_rhs_full_base (S.head fhs) acc actd) ==
                 HRaw (snd crhs)))
let construct_rhs_full_inv_ok_0 fhs acc actd = ()

val construct_rhs_full_inv_ok:
  j:nat{j > 0} ->
  fhs:hash_ss{
    S.length fhs = log2c j /\
    mt_hashes_lth_inv_log j fhs /\
    mt_hashes_inv_log j fhs} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures (let crhs = construct_rhs_full j fhs acc actd in
                 mt_rhs_inv j
                   (construct_rhs_full_base (S.head fhs) acc actd)
                   (fst crhs) actd /\
                 MTS.mt_get_root #(log2c j)
                   (construct_rhs_full_base (S.head fhs) acc actd) == 
                 HRaw (snd crhs)))
        (decreases j)
#reset-options "--z3rlimit 240 --max_fuel 2"
let rec construct_rhs_full_inv_ok j fhs acc actd =
  if j = 1 then construct_rhs_full_inv_ok_0 fhs acc actd

  else if j % 2 = 0 then begin
    construct_rhs_full_inv_ok (j / 2) (S.tail fhs) acc actd;
    let rcrhs = construct_rhs_full (j / 2) (S.tail fhs) acc actd in
    assert (mt_rhs_inv (j / 2)
             (construct_rhs_full_base (S.head (S.tail fhs)) acc actd)
             (fst rcrhs) actd);
    assert (MTS.mt_get_root #(log2c j - 1)
             (construct_rhs_full_base (S.head (S.tail fhs)) acc actd) ==
           HRaw (snd rcrhs));

    let crhs = (S.cons hash_init (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next j fhs;
    construct_rhs_full_base_even_next
      j (S.head fhs) (S.head (S.tail fhs)) acc actd;
    assert (mt_rhs_inv (j / 2)
             (mt_next_lv #(log2c j)
               (construct_rhs_full_base (S.head fhs) acc actd))
             (fst rcrhs) actd);

    assert (mt_rhs_inv j
             (construct_rhs_full_base (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #(log2c j)
             (construct_rhs_full_base (S.head fhs) acc actd) ==
           HRaw (snd rcrhs))
  end

  else begin
    let rhd = if actd then acc else hash_init in
    let nacc = if actd 
               then hash_2 (S.last (S.head fhs)) acc
               else S.last (S.head fhs) in
    construct_rhs_full_inv_ok (j / 2) (S.tail fhs) nacc true;
    let rcrhs = construct_rhs_full (j / 2) (S.tail fhs) nacc true in
    assert (mt_rhs_inv (j / 2)
             (construct_rhs_full_base (S.head (S.tail fhs)) nacc true)
             (fst rcrhs) true);
    assert (MTS.mt_get_root #(log2c j - 1)
             (construct_rhs_full_base (S.head (S.tail fhs)) nacc true) ==
           HRaw (snd rcrhs));

    let crhs = (S.cons rhd (fst rcrhs), snd rcrhs) in
    mt_hashes_lth_inv_log_next j fhs;
    construct_rhs_full_base_odd_next
      j (S.head fhs) (S.head (S.tail fhs)) acc actd nacc;
    (if actd then construct_rhs_full_base_case_true (S.head fhs) acc);
    assert (if actd
           then (S.index (construct_rhs_full_base (S.head fhs) acc actd) j ==
                HRaw rhd)
           else true);
    assert (mt_rhs_inv (j / 2)
             (mt_next_lv #(log2c j)
               (construct_rhs_full_base (S.head fhs) acc actd))
             (fst rcrhs) true);

    assert (mt_rhs_inv j
             (construct_rhs_full_base (S.head fhs) acc actd)
             (fst crhs) actd);
    assert (MTS.mt_get_root #(log2c j)
             (construct_rhs_full_base (S.head fhs) acc actd) == 
           HRaw (snd crhs))
  end


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
  mt_flush_to_inv_preserved_ 0 (MT?.i mt) idx (MT?.j mt) olds (MT?.hs mt);
  // TODO: need to prove that flushing does not affect
  //       the validness of rightmost hashes
  admit ()

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


