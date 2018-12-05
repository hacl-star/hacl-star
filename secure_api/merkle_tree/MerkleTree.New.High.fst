module MerkleTree.New.High

open EverCrypt
open EverCrypt.Helpers

open MerkleTree.Spec

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

val hash: Type0
let hash = MTS.hash_raw

val hash_seq: Type0
let hash_seq = S.seq hash

val hash_ss: Type0
let hash_ss = S.seq hash_seq

noextract
let hash_init: hash =
  Seq.create hash_size 0uy

val hash_2: src1:hash -> src2:hash -> GTot hash
let hash_2 = MTS.hash2_raw

#reset-options "--z3rlimit 10" // default for this file

/// Facts about sequence

val seq_slice_equal_index:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length s1 && j <= S.length s2} ->
  k:nat{i <= k && k < j} ->
  Lemma (requires (S.equal (S.slice s1 i j) (S.slice s2 i j)))
        (ensures (S.index s1 k == S.index s2 k))
        [SMTPat (S.equal (S.slice s1 i j) (S.slice s2 i j));
        SMTPat (S.index s1 k)]
let seq_slice_equal_index #a s1 s2 i j k =
  assert (S.index (S.slice s1 i j) (k - i) == S.index (S.slice s2 i j) (k - i))

private val seq_slice_more_equal:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  n:nat -> m:nat{n <= m && m <= S.length s1 && m <= S.length s2} ->
  k:nat{n <= k} -> l:nat{k <= l && l <= m} ->
  Lemma (requires (S.equal (S.slice s1 n m) (S.slice s2 n m)))
        (ensures (S.equal (S.slice s1 k l) (S.slice s2 k l)))
        [SMTPat (S.equal (S.slice s1 n m) (S.slice s2 n m));
        SMTPat (S.equal (S.slice s1 k l) (S.slice s2 k l))]
private let seq_slice_more_equal #a s1 s2 n m k l =
  slice_slice s1 n m (k - n) (l - n);
  slice_slice s2 n m (k - n) (l - n)

/// Facts about "2"

val remainder_2_not_1_div:
  n:nat -> 
  Lemma (requires (n % 2 <> 1))
        (ensures (n / 2 = (n + 1) / 2))
let remainder_2_not_1_div n = ()

val remainder_2_1_div:
  n:nat -> 
  Lemma (requires (n % 2 = 1))
        (ensures (n / 2 + 1 = (n + 1) / 2))
let remainder_2_1_div n = ()  

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: i:nat -> j:nat{i <= j && j < pow2 32} ->
      hs:S.seq hash_seq{S.length hs = 32} ->
      rhs_ok:bool -> rhs:hash_seq{S.length rhs = 32} ->
      mroot:hash ->
      merkle_tree

val mt_not_full: merkle_tree -> GTot bool
let mt_not_full mt =
  MT?.j mt < pow2 32 - 1

val mt_empty: merkle_tree -> GTot bool
let mt_empty mt =
  MT?.j mt = 0

val mt_not_empty: merkle_tree -> GTot bool
let mt_not_empty mt =
  MT?.j mt > 0

/// Well-formedness w.r.t. indices of base hash elements

noextract
val offset_of: i:nat -> Tot nat
let offset_of i =
  if i % 2 = 0 then i else i - 1

val hs_wf_elts:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  i:nat -> j:nat{j >= i} ->
  GTot Type0 (decreases (32 - lv))
let rec hs_wf_elts lv hs i j =
  if lv = 32 then true
  else (let ofs = offset_of i in
       S.length (S.index hs lv) == j - ofs /\
       hs_wf_elts (lv + 1) hs (i / 2) (j / 2))

val hs_wf_elts_equal:
  lv:nat{lv <= 32} ->
  hs1:hash_ss{S.length hs1 = 32} ->
  hs2:hash_ss{S.length hs2 = 32} ->
  i:nat -> j:nat{j >= i} ->
  Lemma (requires (hs_wf_elts lv hs1 i j /\
		  S.equal (S.slice hs1 lv 32) (S.slice hs2 lv 32)))
	(ensures (hs_wf_elts lv hs2 i j))
	(decreases (32 - lv))
let rec hs_wf_elts_equal lv hs1 hs2 i j =
  if lv = 32 then ()
  else (S.slice_slice hs1 lv 32 1 (32 - lv);
       S.slice_slice hs2 lv 32 1 (32 - lv);
       assert (S.equal (S.slice hs1 (lv + 1) 32)
		       (S.slice hs2 (lv + 1) 32));
       S.lemma_index_slice hs1 lv 32 0; 
       S.lemma_index_slice hs2 lv 32 0;
       assert (S.index hs1 lv == S.index hs2 lv);
       hs_wf_elts_equal (lv + 1) hs1 hs2 (i / 2) (j / 2))

val mt_wf_elts: merkle_tree -> GTot Type0
let mt_wf_elts mt =
  hs_wf_elts 0 (MT?.hs mt) (MT?.i mt) (MT?.j mt)

/// Construction

val hs_wf_elts_empty:
  lv:nat{lv <= 32} ->
  Lemma (requires True)
	(ensures (hs_wf_elts lv (S.create 32 S.empty) 0 0))
	(decreases (32 - lv))
let rec hs_wf_elts_empty lv =
  if lv = 32 then ()
  else hs_wf_elts_empty (lv + 1)

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
val create_empty_mt: unit -> GTot (mt:merkle_tree{mt_wf_elts mt})
let create_empty_mt _ =
  hs_wf_elts_empty 0;
  MT 0 0 (S.create 32 S.empty) false (S.create 32 hash_init) hash_init

/// Insertion

val hash_ss_insert:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  v:hash ->
  GTot (ihs:hash_ss{S.length ihs = 32 /\ hs_wf_elts (lv + 1) ihs (i / 2) (j / 2)})
let hash_ss_insert lv i j hs v =
  let ihs = S.upd hs lv (S.snoc (S.index hs lv) v) in
  hs_wf_elts_equal (lv + 1) hs ihs (i / 2) (j / 2);
  ihs

val insert_:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ hs_wf_elts lv hs i j} ->
  acc:hash ->
  GTot (ihs:hash_ss{
         S.length ihs = 32 /\
         hs_wf_elts lv ihs i (j + 1) /\
         S.equal (S.slice hs 0 lv) (S.slice ihs 0 lv)})
       (decreases j)
let rec insert_ lv i j hs acc =
  let ihs = hash_ss_insert lv i j hs acc in
  assert (S.equal (S.slice hs 0 lv) (S.slice ihs 0 lv));
  if j % 2 = 1 // S.length (S.index hs lv) > 0 
  then begin
    remainder_2_1_div j;
    let nacc = hash_2 (S.last (S.index hs lv)) acc in
    let rihs = insert_ (lv + 1) (i / 2) (j / 2) ihs nacc in
    assert (hs_wf_elts (lv + 1) rihs (i / 2) (j / 2 + 1));
    assert (S.equal (S.slice ihs 0 (lv + 1)) (S.slice rihs 0 (lv + 1)));
    assert (S.index ihs lv == S.index rihs lv);
    assert (S.length (S.index rihs lv) = (j + 1) - offset_of i);
    assert (S.equal (S.slice ihs 0 (lv + 1)) (S.slice rihs 0 (lv + 1)));
    assert (S.equal (S.slice ihs 0 lv) (S.slice rihs 0 lv));
    rihs
  end
  else ihs

val insert_base:
  lv:nat -> i:nat -> j:nat -> hs:hash_ss -> acc:hash ->
  Lemma (requires (
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ hs_wf_elts lv hs i j /\
	  j % 2 <> 1))
	(ensures (S.equal (insert_ lv i j hs acc)
			  (hash_ss_insert lv i j hs acc)))
let insert_base lv i j hs acc = ()

val insert_rec:
  lv:nat -> i:nat -> j:nat -> hs:hash_ss -> acc:hash ->
  Lemma (requires (
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ hs_wf_elts lv hs i j /\
	  j % 2 == 1))
	(ensures (
	  (hs_wf_elts_equal (lv + 1) hs
	    (hash_ss_insert lv i j hs acc) (i / 2) (j / 2);
	  S.equal (insert_ lv i j hs acc)
		  (insert_ (lv + 1) (i / 2) (j / 2)
			   (hash_ss_insert lv i j hs acc)
			   (hash_2 (S.last (S.index hs lv)) acc)))))
let insert_rec lv i j hs acc = ()

val mt_insert:
  mt:merkle_tree{mt_wf_elts mt /\ mt_not_full mt} -> v:hash -> 
  GTot (imt:merkle_tree{mt_wf_elts imt})
let mt_insert mt v =
  MT (MT?.i mt)
     (MT?.j mt + 1)
     (insert_ 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v)
     false
     (MT?.rhs mt)
     (MT?.mroot mt)

val create_mt: init:hash -> GTot (mt:merkle_tree{mt_wf_elts mt})
let create_mt init =
  mt_insert (create_empty_mt ()) init

/// Getting the Merkle root and path

type path = S.seq hash

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
val construct_rhs:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  GTot (crhs:hash_seq{S.length crhs = 32} * hash)
       (decreases j)
let rec construct_rhs lv hs rhs i j acc actd =
  let ofs = offset_of i in
  if j = 0 then (rhs, acc)
  else
    (if j % 2 = 0
    then (construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) acc actd)
    else (let nrhs = if actd then S.upd rhs lv acc else rhs in
         let nacc = if actd 
                    then hash_2 (S.index (S.index hs lv) (j - 1 - ofs)) acc
                    else S.index (S.index hs lv) (j - 1 - ofs) in
         construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true))

val construct_rhs_unchanged:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires True)
        (ensures (S.equal (S.slice rhs 0 lv)
                          (S.slice (fst (construct_rhs lv hs rhs i j acc actd)) 0 lv)))
        (decreases j)
let rec construct_rhs_unchanged lv hs rhs i j acc actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else if j % 2 = 0
  then (construct_rhs_unchanged (lv + 1) hs rhs (i / 2) (j / 2) acc actd;
       let rrhs = fst (construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) acc actd) in
       assert (S.equal (S.slice rhs 0 lv) (S.slice rrhs 0 lv)))
  else (let nrhs = if actd then S.upd rhs lv acc else rhs in
       let nacc = if actd 
                  then hash_2 (S.index (S.index hs lv) (j - 1 - ofs)) acc
                  else S.index (S.index hs lv) (j - 1 - ofs) in
       construct_rhs_unchanged (lv + 1) hs nrhs (i / 2) (j / 2) nacc true;
       let rrhs = fst (construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true) in
       assert (S.equal (S.slice nrhs 0 lv) (S.slice rrhs 0 lv));
       assert (S.equal (S.slice rhs 0 lv) (S.slice nrhs 0 lv)))

val construct_rhs_even:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (j <> 0 /\ j % 2 = 0))
        (ensures (construct_rhs lv hs rhs i j acc actd ==
                 construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) acc actd))
let construct_rhs_even lv hs rhs i j acc actd = ()

val construct_rhs_odd:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  Lemma (requires (j % 2 = 1))
        (ensures (construct_rhs lv hs rhs i j acc actd ==
                 (let ofs = offset_of i in
                 let nrhs = if actd then S.upd rhs lv acc else rhs in
                 let nacc = if actd 
                            then hash_2 (S.index (S.index hs lv) (j - 1 - ofs)) acc
                            else S.index (S.index hs lv) (j - 1 - ofs) in
                 construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true)))
let construct_rhs_odd lv hs rhs i j acc actd = ()

val mt_get_root: 
  mt:merkle_tree{mt_wf_elts mt} -> drt:hash ->
  GTot (merkle_tree * hash)
let mt_get_root mt drt =
  if MT?.rhs_ok mt then (mt, MT?.mroot mt)
  else begin
    let (nrhs, rt) = 
        construct_rhs
          0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
	  drt false in
    (MT (MT?.i mt) (MT?.j mt) (MT?.hs mt) true nrhs rt, rt)
  end

val mt_get_root_rhs_ok_true:
  mt:merkle_tree{mt_wf_elts mt} -> drt:hash ->
  Lemma (requires (MT?.rhs_ok mt == true))
        (ensures (mt_get_root mt drt == (mt, MT?.mroot mt)))
let mt_get_root_rhs_ok_true mt drt = ()

val mt_get_root_rhs_ok_false:
  mt:merkle_tree{mt_wf_elts mt} -> drt:hash ->
  Lemma (requires (MT?.rhs_ok mt == false))
        (ensures (mt_get_root mt drt ==
                 (let (nrhs, rt) = 
                   construct_rhs
                     0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
	             drt false in
                   (MT (MT?.i mt) (MT?.j mt) (MT?.hs mt) true nrhs rt, rt))))
let mt_get_root_rhs_ok_false mt drt = ()

val path_insert: p:path -> hp:hash -> GTot path
let path_insert p hp = S.snoc p hp

val mt_path_length_step:
  k:nat -> j:nat{k <= j} -> actd:bool -> GTot nat
let mt_path_length_step k j actd =
  if j = 0 then 0
  else (if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd) then 0 else 1)
       else 1)

val mt_path_length:
  k:nat -> j:nat{k <= j} -> actd:bool -> GTot nat
let rec mt_path_length k j actd =
  if j = 0 then 0
  else (let nactd = actd || (j % 2 = 1) in
       mt_path_length_step k j actd +
       mt_path_length (k / 2) (j / 2) nactd)

val mt_get_path_step:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    j <> 0 /\ i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  GTot path
let mt_get_path_step lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if k % 2 = 1
  then path_insert p (S.index (S.index hs lv) (k - 1 - ofs))
  else (if k = j then p
       else if k + 1 = j
	    then (if actd
		 then path_insert p (S.index rhs lv)
		 else p)
	    else path_insert p (S.index (S.index hs lv) (k + 1 - ofs)))

// Construct a Merkle path for a given index `k`, hashes `hs`, 
// and rightmost hashes `rhs`.
val mt_get_path_:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat -> 
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  GTot (np:path{S.length np = S.length p + mt_path_length k j actd})
       (decreases (32 - lv))
let rec mt_get_path_ lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then p
  else
    (let np = mt_get_path_step lv hs rhs i j k p actd in
    mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
    		 (if j % 2 = 0 then actd else true))

val mt_get_path_unchanged:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat -> 
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  Lemma (requires True)
        (ensures (S.equal p (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                                     0 (S.length p))))
        (decreases (32 - lv))
let rec mt_get_path_unchanged lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else
    (let np = mt_get_path_step lv hs rhs i j k p actd in
    assert (S.equal p (S.slice np 0 (S.length p)));
    mt_get_path_unchanged (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
      (if j % 2 = 0 then actd else true))

val mt_get_path_pull:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat -> 
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  Lemma (requires True)
        (ensures (S.equal (mt_get_path_ lv hs rhs i j k p actd)
                          (S.append p (mt_get_path_ lv hs rhs i j k S.empty actd))))
        (decreases (32 - lv))
#reset-options "--z3rlimit 20 --max_fuel 1"
let rec mt_get_path_pull lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then ()
  else 
    (let np = mt_get_path_step lv hs rhs i j k p actd in
    let nactd = if j % 2 = 0 then actd else true in
    mt_get_path_pull (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np nactd;
    mt_get_path_pull (lv + 1) hs rhs (i / 2) (j / 2) (k / 2)
      (mt_get_path_step lv hs rhs i j k S.empty actd) nactd)
#reset-options "--z3rlimit 10"

val mt_get_path_slice:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat -> 
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  Lemma (requires True)
        (ensures (S.equal (S.slice (mt_get_path_ lv hs rhs i j k p actd)
                            (S.length p) (S.length p + mt_path_length k j actd))
                          (mt_get_path_ lv hs rhs i j k S.empty actd)))
        (decreases (32 - lv))
let rec mt_get_path_slice lv hs rhs i j k p actd =
  mt_get_path_pull lv hs rhs i j k p actd

val mt_get_path: 
  mt:merkle_tree{mt_wf_elts mt} ->
  idx:nat{MT?.i mt <= idx /\ idx < MT?.j mt} ->
  drt:hash ->
  GTot (nat * 
       (np:path{S.length np = 1 + mt_path_length idx (MT?.j mt) false}) * 
       hash)
let mt_get_path mt idx drt =
  let (umt, root) = mt_get_root mt drt in
  let ofs = offset_of (MT?.i umt) in
  let np = path_insert S.empty (S.index (S.index (MT?.hs umt) 0) (idx - ofs)) in
  (MT?.j umt,
  mt_get_path_ 0 (MT?.hs umt) (MT?.rhs umt)
    (MT?.i umt) (MT?.j umt) idx np false,
  root)

/// Flushing

val mt_flush_to_:
  lv:nat{lv < 32} ->
  hs:hash_ss{S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs pi j} ->
  GTot (fhs:hash_ss{
         S.length fhs = 32 /\ 
         S.equal (S.slice hs 0 lv) (S.slice fhs 0 lv) /\
         hs_wf_elts lv fhs i j}) (decreases i)
let rec mt_flush_to_ lv hs pi i j =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then hs
  else (let ofs = oi - opi in
       let hvec = S.index hs lv in
       let flushed = S.slice hvec ofs (S.length hvec) in
       let nhs = S.upd hs lv flushed in
       hs_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
       mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))

val mt_flush_to_rec:
  lv:nat{lv < 32} ->
  hs:hash_ss{S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    hs_wf_elts lv hs pi j} ->
  Lemma (requires (offset_of i <> offset_of pi))
        (ensures (mt_flush_to_ lv hs pi i j ==
                 (let ofs = offset_of i - offset_of pi in
                 let hvec = S.index hs lv in
                 let flushed = S.slice hvec ofs (S.length hvec) in
                 let nhs = S.upd hs lv flushed in
                 hs_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
                 mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))))
let mt_flush_to_rec lv hs pi i j = ()                 

val mt_flush_to: 
  mt:merkle_tree{mt_wf_elts mt} -> 
  idx:nat{idx >= MT?.i mt /\ idx < MT?.j mt} ->
  GTot (fmt:merkle_tree{mt_wf_elts fmt})
let mt_flush_to mt idx =
  let fhs = mt_flush_to_ 0 (MT?.hs mt) (MT?.i mt) idx (MT?.j mt) in
  MT idx (MT?.j mt) fhs (MT?.rhs_ok mt) (MT?.rhs mt) (MT?.mroot mt)

val mt_flush: 
  mt:merkle_tree{mt_wf_elts mt /\ MT?.j mt > MT?.i mt} -> 
  GTot (fmt:merkle_tree{mt_wf_elts fmt})
let mt_flush mt = 
  mt_flush_to mt (MT?.j mt - 1)


/// Retraction

val mt_retract_to_:
  hs:hash_ss{S.length hs = 32} ->
  lv:nat{lv < S.length hs} ->
  i:nat ->
  s:nat -> // s is the first index excluded from nhs
  j:nat{ i <= s /\ s <= j /\ 
         j < pow2 (S.length hs - lv) /\
         hs_wf_elts lv hs i j} ->
  GTot (nhs:hash_ss{
         S.length nhs = S.length hs /\
         S.equal (S.slice hs 0 lv) (S.slice nhs 0 lv) /\
         hs_wf_elts lv nhs i s})
  (decreases (S.length hs - lv))  
let rec mt_retract_to_ hs lv i s j =
  if lv >= S.length hs then hs
  else begin
    let hvec = S.index hs lv in
    let old_len = j - offset_of i in
    let new_len = s - offset_of i in
    assert (S.length hvec = old_len);
    assert (new_len <= old_len);
    assert (new_len <= S.length hvec);
    let retracted = S.slice hvec 0 new_len in
    let nhs = S.upd hs lv retracted in
    if lv >= S.length hs - 1 then nhs else
    begin
      hs_wf_elts_equal (lv + 1) hs nhs (i / 2) (j / 2);
      mt_retract_to_ nhs (lv + 1) (i / 2) (s / 2) (j / 2)
    end
  end

val mt_retract_to: 
  mt:merkle_tree{mt_wf_elts mt} -> 
  r:nat{MT?.i mt <= r /\ r < MT?.j mt} ->
  GTot (rmt:merkle_tree{mt_wf_elts rmt /\ MT?.i rmt = MT?.i mt /\ MT?.j rmt = r + 1})
let mt_retract_to mt r =
  let nhs = mt_retract_to_ (MT?.hs mt) 0 (MT?.i mt) (r+1) (MT?.j mt) in  
  MT (MT?.i mt) (r+1) nhs false (MT?.rhs mt) (MT?.mroot mt)
  

/// Verification

val mt_verify_:
  k:nat ->
  j:nat{k <= j} ->
  p:path ->
  ppos:nat ->
  acc:hash ->
  actd:bool{ppos + mt_path_length k j actd <= S.length p} ->
  GTot hash
let rec mt_verify_ k j p ppos acc actd =
  if j = 0 then acc
  else (let nactd = actd || (j % 2 = 1) in
       if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd)
	    then mt_verify_ (k / 2) (j / 2) p ppos acc nactd
	    else (let nacc = hash_2 acc (S.index p ppos) in
		 mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd))
       else (let nacc = hash_2 (S.index p ppos) acc in
	    mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd))

val mt_verify:
  k:nat ->
  j:nat{k < j} ->
  p:path{S.length p = 1 + mt_path_length k j false} ->
  rt:hash ->
  GTot bool
let mt_verify k j p rt =
  let crt = mt_verify_ k j p 1 (S.index p 0) false in
  crt = rt

