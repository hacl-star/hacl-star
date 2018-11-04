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

val hash_size: nat
let hash_size = U32.v (EHS.tagLen EHS.SHA256)

val hash: Type0
let hash = b:EHS.bytes{S.length b = hash_size}

val hash_seq: Type0
let hash_seq = S.seq hash

val hash_ss: Type0
let hash_ss = S.seq hash_seq

let hash_init: hash = S.create hash_size 0uy

val hash_2: src1:hash -> src2:hash -> GTot hash
let hash_2 src1 src2 =
  EHS.extract (EHS.hash0 #EHS.SHA256 (S.append src1 src2))

/// High-level Merkle tree data structure

let merkle_tree_size_lg = 32

noeq type merkle_tree =
| MT: i:nat -> j:nat{j >= i && j < pow2 merkle_tree_size_lg} ->
      hs:S.seq hash_seq{S.length hs = 32} ->
      rhs_ok:bool -> rhs:hash_seq{S.length rhs = 32} ->
      mroot:hash ->
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

val mt_wf_elts_empty:
  lv:nat{lv <= 32} ->
  Lemma (requires True)
	(ensures (mt_wf_elts lv (S.create 32 S.empty) 0 0))
	(decreases (32 - lv))
let rec mt_wf_elts_empty lv =
  if lv = 32 then ()
  else mt_wf_elts_empty (lv + 1)

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
val create_empty_mt: unit -> GTot wf_mt
let create_empty_mt _ =
  mt_wf_elts_empty 0;
  MT 0 0 (S.create 32 S.empty) false (S.create 32 hash_init) hash_init

/// Insertion

val hash_ss_insert:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ mt_wf_elts lv hs i j} ->
  v:hash ->
  GTot (ihs:hash_ss{S.length ihs = 32 /\ mt_wf_elts (lv + 1) ihs (i / 2) (j / 2)})
let hash_ss_insert lv i j hs v =
  let ihs = S.upd hs lv (S.snoc (S.index hs lv) v) in
  mt_wf_elts_equal (lv + 1) hs ihs (i / 2) (j / 2);
  ihs

val insert_:
  lv:nat{lv < 32} ->
  i:nat ->
  j:nat{i <= j /\ j < pow2 (32 - lv) - 1} ->
  hs:hash_ss{S.length hs = 32 /\ mt_wf_elts lv hs i j} ->
  acc:hash ->
  GTot (ihs:hash_ss{S.length ihs = 32})
       (decreases j)
let rec insert_ lv i j hs acc =
  let ihs = hash_ss_insert lv i j hs acc in
  if j % 2 = 1 // S.length (S.index hs lv) > 0 
  then (let nacc = hash_2 (S.last (S.index hs lv)) acc in
       insert_ (lv + 1) (i / 2) (j / 2) ihs nacc)
  else ihs

val insert_base:
  lv:nat -> i:nat -> j:nat -> hs:hash_ss -> acc:hash ->
  Lemma (requires (
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ mt_wf_elts lv hs i j /\
	  j % 2 <> 1))
	(ensures (S.equal (insert_ lv i j hs acc)
			  (hash_ss_insert lv i j hs acc)))
let insert_base lv i j hs acc = ()

val insert_rec:
  lv:nat -> i:nat -> j:nat -> hs:hash_ss -> acc:hash ->
  Lemma (requires (
	  lv < 32 /\ i <= j /\ j < pow2 (32 - lv) - 1 /\
	  S.length hs = 32 /\ mt_wf_elts lv hs i j /\
	  j % 2 == 1))
	(ensures (
	  (mt_wf_elts_equal (lv + 1) hs
	    (hash_ss_insert lv i j hs acc) (i / 2) (j / 2);
	  S.equal (insert_ lv i j hs acc)
		  (insert_ (lv + 1) (i / 2) (j / 2)
			   (hash_ss_insert lv i j hs acc)
			   (hash_2 (S.last (S.index hs lv)) acc)))))
let insert_rec lv i j hs acc = ()

val mt_insert:
  mt:wf_mt{mt_not_full mt} -> v:hash -> GTot merkle_tree
let mt_insert mt v =
  MT (MT?.i mt)
     (MT?.j mt + 1)
     (insert_ 0 (MT?.i mt) (MT?.j mt) (MT?.hs mt) v)
     false
     (MT?.rhs mt)
     (MT?.mroot mt)

val create_mt: init:hash -> GTot merkle_tree
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
    mt_wf_elts lv hs i j} ->
  acc:hash ->
  actd:bool ->
  GTot (crhs:hash_seq{S.length crhs = 32} * hash) (decreases j)
let rec construct_rhs lv hs rhs i j acc actd =
  let ofs = offset_of i in
  if j = 0 then (rhs, acc)
  else
    (if j % 2 = 0
    then construct_rhs (lv + 1) hs rhs (i / 2) (j / 2) acc actd
    else (let nrhs = if actd then S.upd rhs lv acc else rhs in
         let nacc = if actd 
                    then hash_2 (S.index (S.index hs lv) (j - 1 - ofs)) acc
                    else S.index (S.index hs lv) (j - 1 - ofs) in
         construct_rhs (lv + 1) hs nrhs (i / 2) (j / 2) nacc true))

val construct_rhs_even:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    i <= j /\ j < pow2 (32 - lv) /\
    mt_wf_elts lv hs i j} ->
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
    mt_wf_elts lv hs i j} ->
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
  mt:wf_mt -> drt:hash ->
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
  mt:wf_mt -> drt:hash ->
  Lemma (requires (MT?.rhs_ok mt == true))
        (ensures (mt_get_root mt drt == (mt, MT?.mroot mt)))
let mt_get_root_rhs_ok_true mt drt = ()

val mt_get_root_rhs_ok_false:
  mt:wf_mt -> drt:hash ->
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

val mt_get_path_step:
  lv:nat{lv <= 32} ->
  hs:hash_ss{S.length hs = 32} ->
  rhs:hash_seq{S.length rhs = 32} ->
  i:nat ->
  j:nat{
    j <> 0 /\ i <= j /\ j < pow2 (32 - lv) /\
    mt_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  GTot path (decreases (32 - lv))
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
    mt_wf_elts lv hs i j} ->
  k:nat{i <= k && k <= j} ->
  p:path ->
  actd:bool ->
  GTot path (decreases (32 - lv))
let rec mt_get_path_ lv hs rhs i j k p actd =
  let ofs = offset_of i in
  if j = 0 then p
  else
    (let np = mt_get_path_step lv hs rhs i j k p actd in
    mt_get_path_ (lv + 1) hs rhs (i / 2) (j / 2) (k / 2) np
    		 (if j % 2 = 0 then actd else true))

val mt_get_path: 
  mt:wf_mt ->
  idx:nat{MT?.i mt <= idx /\ idx < MT?.j mt} ->
  drt:hash ->
  GTot (nat * path * hash)
let mt_get_path mt idx drt =
  let (umt, root) = mt_get_root mt drt in
  let ofs = offset_of (MT?.i umt) in
  let np = path_insert S.empty (S.index (S.index (MT?.hs umt) 0) (idx - ofs)) in
  (MT?.j umt,
  mt_get_path_ 0 (MT?.hs umt) (MT?.rhs umt)
    (MT?.i umt) (MT?.j umt) idx np false,
  root)

val mt_flush_to_:
  lv:nat{lv < 32} ->
  hs:hash_ss{S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    mt_wf_elts lv hs pi j} ->
  GTot (fhs:hash_ss{S.length fhs = 32}) (decreases i)
let rec mt_flush_to_ lv hs pi i j =
  let oi = offset_of i in
  let opi = offset_of pi in
  if oi = opi then hs
  else (let ofs = oi - opi in
       let hvec = S.index hs lv in
       let flushed = S.slice hvec ofs (S.length hvec) in
       let nhs = S.upd hs lv flushed in
       mt_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
       mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))

val mt_flush_to_rec:
  lv:nat{lv < 32} ->
  hs:hash_ss{S.length hs = 32} ->
  pi:nat ->
  i:nat{i >= pi} ->
  j:nat{
    j >= i /\ j < pow2 (32 - lv) /\
    mt_wf_elts lv hs pi j} ->
  Lemma (requires (offset_of i <> offset_of pi))
        (ensures (mt_flush_to_ lv hs pi i j ==
                 (let ofs = offset_of i - offset_of pi in
                 let hvec = S.index hs lv in
                 let flushed = S.slice hvec ofs (S.length hvec) in
                 let nhs = S.upd hs lv flushed in
                 mt_wf_elts_equal (lv + 1) hs nhs (pi / 2) (j / 2);
                 mt_flush_to_ (lv + 1) nhs (pi / 2) (i / 2) (j / 2))))
let mt_flush_to_rec lv hs pi i j = ()                 

val mt_flush_to: 
  mt:wf_mt -> 
  idx:nat{idx >= MT?.i mt /\ idx < MT?.j mt} ->
  GTot merkle_tree
let mt_flush_to mt idx =
  let fhs = mt_flush_to_ 0 (MT?.hs mt) (MT?.i mt) idx (MT?.j mt) in
  MT idx (MT?.j mt) fhs (MT?.rhs_ok mt) (MT?.rhs mt) (MT?.mroot mt)

val mt_flush: mt:wf_mt{MT?.j mt > MT?.i mt} -> GTot merkle_tree
let mt_flush mt = 
  mt_flush_to mt (MT?.j mt - 1)

val mt_verify_:
  k:nat ->
  j:nat{k <= j} ->
  p:path ->
  ppos:nat{ppos <= S.length p /\ j < pow2 (S.length p - ppos)} ->
  acc:hash ->
  actd:bool ->
  GTot hash
let rec mt_verify_ k j p ppos acc actd =
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
  p:path{1 <= S.length p /\ j < pow2 (S.length p - 1)} ->
  rt:hash ->
  GTot bool
let mt_verify k j p rt =
  let crt = mt_verify_ k j p 1 (S.index p 0) false in
  crt = rt

