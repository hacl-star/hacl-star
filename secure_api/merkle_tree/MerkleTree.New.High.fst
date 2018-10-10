module MerkleTree.New.High

open EverCrypt
open EverCrypt.Helpers

open FStar.All
open FStar.Ghost
open FStar.Seq

module List = FStar.List.Tot
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

val hash_size: uint32_t
let hash_size = 32ul

type hash = b:EHS.bytes{S.length b = U32.v hash_size}
type hash_seq = S.seq hash
type hash_ss = S.seq hash_seq

let hash_init: hash = S.create (U32.v hash_size) 0uy

val hash_2: src1:hash -> src2:hash -> GTot hash
let hash_2 src1 src2 =
  EHS.extract (EHS.hash0 #(Ghost.hide EHS.SHA256) (S.append src1 src2))

/// High-level Merkle tree data structure

let merkle_tree_size_lg = 32

noeq type merkle_tree =
| MT: i:nat -> j:nat{j >= i && j < pow2 merkle_tree_size_lg} ->
      hs:S.seq hash_seq{S.length hs = 32} ->
      rhs_ok:bool -> rhs:hash_seq{S.length rhs = 32} ->
      merkle_tree

val mt_not_full: merkle_tree -> GTot bool
let mt_not_full mt =
  MT?.j mt < pow2 merkle_tree_size_lg - 1

/// Well-formedness

val offset_of: i:nat -> Tot nat
let offset_of i =
  if i % 2 = 0 then i else i - 1

val mt_wf_elts:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  i:nat -> j:nat{j >= i} ->
  GTot Type0 (decreases (32 - lv))
let rec mt_wf_elts lv hs i j =
  if lv = 32 then true
  else (let ofs = offset_of i in
       S.length (S.index hs lv) == j - ofs /\
       mt_wf_elts (lv + 1) hs (i / 2) (j / 2))

val mt_wf_elts_equal:
  lv:nat{lv <= 32} ->
  hs1:hash_ss{S.length hs1 = 32} ->
  hs2:hash_ss{S.length hs2 = 32} ->
  i:nat -> j:nat{j >= i} ->
  Lemma (requires (mt_wf_elts lv hs1 i j /\
		  S.equal (S.slice hs1 lv 32) (S.slice hs2 lv 32)))
	(ensures (mt_wf_elts lv hs2 i j))
	(decreases (32 - lv))
let rec mt_wf_elts_equal lv hs1 hs2 i j =
  if lv = 32 then ()
  else (S.slice_slice hs1 lv 32 1 (32 - lv);
       S.slice_slice hs2 lv 32 1 (32 - lv);
       assert (S.equal (S.slice hs1 (lv + 1) 32)
		       (S.slice hs2 (lv + 1) 32));
       S.lemma_index_slice hs1 lv 32 0; 
       S.lemma_index_slice hs2 lv 32 0;
       assert (S.index hs1 lv == S.index hs2 lv);
       mt_wf_elts_equal (lv + 1) hs1 hs2 (i / 2) (j / 2))

val mt_wf: merkle_tree -> GTot Type0
let mt_wf mt =
  mt_wf_elts 0 (MT?.hs mt) (MT?.i mt) (MT?.j mt)

type wf_mt = mt:merkle_tree{mt_wf mt}

/// Construction

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
val create_empty_mt: unit -> GTot merkle_tree
let create_empty_mt _ =
  MT 0 0 (S.create 32 S.empty) false (S.create 32 hash_init)

/// Insertion

val insert_:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ mt_wf_elts lv hs i j} ->
  acc:hash ->
  GTot (ihs:hash_ss{S.length ihs = 32})
       (decreases j)
let rec insert_ lv i j hs acc =
  let ihs = S.upd hs lv (S.snoc (S.index hs lv) acc) in
  if j % 2 = 1 && S.length (S.index hs lv) > 0 
  then (let nacc = hash_2 (S.last (S.index hs lv)) acc in
       mt_wf_elts_equal (lv + 1) hs ihs (i / 2) (j / 2);
       insert_ (lv + 1) (i / 2) (j / 2) ihs nacc)
  else ihs

val mt_insert:
  mt:wf_mt{mt_not_full mt} -> v:hash -> GTot merkle_tree
let mt_insert mt v =
  MT (MT?.i mt)
     (MT?.j mt + 1)
     (insert_ 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v)
     false
     (MT?.rhs mt)

val create_mt: init:hash -> GTot merkle_tree
let create_mt init =
  admit ();
  mt_insert (create_empty_mt ()) init

/// Getting the Merkle root and path

type path = S.seq hash

// Construct the rightmost hashes for a given (incomplete) Merkle tree.
// This function calculates the Merkle root as well, which is the final
// accumulator value.
private val construct_rhs:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j && j < pow2 (32 - lv) /\
    mt_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  GTot (crhs:hash_seq{S.length crhs = 32} * hash) (decreases j)
private let rec construct_rhs lv hs rhs i j acc actd =
  admit ();
  let ofs = offset_of i in
  if j = 0 then (rhs, acc)
  else
    (if j % 2 = 0
    then construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) acc actd
    else (if actd
    	 then (let nrhs = S.upd rhs lv acc in
	      let nacc = hash_2 (S.index (S.index hs lv) (j - 1 - ofs)) acc in
	      construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true)
	 else (let nacc = S.index (S.index hs lv) (j - 1 - ofs) in
	      construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) nacc true)))

val mt_get_root: mt:wf_mt -> GTot hash
let mt_get_root mt =
  let (_, root) = construct_rhs
		    0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
		    hash_init false in
  root

val path_insert: p:path -> hp:hash -> GTot path
let path_insert p hp = S.snoc p hp

// Construct a Merkle path for a given index `k`, hashes `hs`, 
// and rightmost hashes `rhs`.
val mt_get_path_:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat -> j:nat{i <= j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  GTot path (decreases (32 - lv))
let rec mt_get_path_ lv hs rhs i j k p actd =
  admit ();
  let ofs = offset_of i in
  if j = 0 then p
  else
    (let np = 
      (if k % 2 = 1
      then path_insert p (S.index (S.index hs lv) (k - 1 - ofs))
      else (if k = j then p
	   else if k + 1 = j
	   then (if actd
		then path_insert p (S.index rhs lv)
		else p)
	   else path_insert p (S.index (S.index hs lv) (k + 1 - ofs)))) in
    mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
    		 (if j % 2 = 0 then actd else true))

val mt_get_path: mt:wf_mt -> idx:nat -> GTot (path * hash)
let mt_get_path mt idx =
  admit ();
  let (rhs, root) =
    construct_rhs 0 (MT?.hs mt) (MT?.rhs mt) (MT?.i mt) (MT?.j mt)
		  hash_init false in
  let ofs = offset_of (MT?.i mt) in
  let ip = path_insert S.empty (S.index (S.index (MT?.hs mt) 0) (idx - ofs)) in
  (mt_get_path_ 0 (MT?.hs mt) rhs (MT?.i mt) (MT?.j mt) idx ip false,
  root)

val mt_flush_to_:
  lv:nat{lv < 32} ->
  hs:hash_ss{S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{j > i} ->
  GTot hash_ss
let rec mt_flush_to_ lv hs pi i j =
  admit ();
  if i = 0 then hs
  else (let ofs = offset_of i - offset_of pi in
       let hvec = S.index hs lv in
       let flushed = S.slice hvec ofs (S.length hvec) in
       let nhs = S.upd hs lv flushed in
       mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))

val mt_flush_to: 
  mt:wf_mt -> idx:nat -> GTot wf_mt
let mt_flush_to mt idx =
  admit ();
  let fhs = mt_flush_to_ 0 (MT?.hs mt) (MT?.i mt) idx (MT?.j mt) in
  MT idx (MT?.j mt) fhs (MT?.rhs_ok mt) (MT?.rhs mt)

val mt_flush: mt:wf_mt{MT?.j mt > MT?.i mt} -> GTot wf_mt
let mt_flush mt = 
  mt_flush_to mt (MT?.j mt - 1)

val mt_verify_:
  k:nat ->
  j:nat{k <= j} ->
  p:path ->
  ppos:nat ->
  acc:hash ->
  actd:bool ->
  GTot hash
let rec mt_verify_ k j p ppos acc actd =
  admit ();
  if j = 0 then acc
  else (let nactd = actd || (j % 2 = 1) in
       let phash = S.index p ppos in
       if k % 2 = 0
       then (if j = k || (j = k + 1 && not actd)
	    then mt_verify_ (k / 2) (j / 2) p ppos acc nactd
	    else (let nacc = hash_2 acc phash in
		 mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd))
       else (let nacc = hash_2 phash acc in
	    mt_verify_ (k / 2) (j / 2) p (ppos + 1) nacc nactd))

val mt_verify:
  k:nat ->
  j:nat{k < j} ->
  p:path ->
  rt:hash ->
  GTot bool
let mt_verify k j p rt =
  admit ();
  let crt = mt_verify_ k j p 1 (S.index p 0) false in
  crt = rt


