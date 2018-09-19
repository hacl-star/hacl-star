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

val mt_wf: merkle_tree -> GTot Type0
let mt_wf mt =
  mt_wf_elts 0 (MT?.hs mt) (MT?.i mt) (MT?.j mt)

type wf_mt = mt:merkle_tree{mt_wf mt}

/// Construction

// NOTE: the public function is `create_mt` defined below, which
// builds a tree with an initial hash.
private val create_empty_mt: unit -> GTot wf_mt
private let create_empty_mt _ =
  admit ();
  MT 0 0 (S.create 32 S.empty) false (S.create 32 hash_init)

/// Insertion

private val insert_:
  lv:nat{lv < 32} ->
  i:Ghost.erased nat ->
  j:nat{Ghost.reveal i <= j} ->
  hs:hash_ss{
    S.length hs = 32 /\ 
    mt_wf_elts lv hs (Ghost.reveal i) j} ->
  acc:hash ->
  GTot (ihs:hash_ss{
    S.length ihs = 32 /\
    mt_wf_elts lv ihs (Ghost.reveal i) (j + 1)})
  (decreases j)
private let rec insert_ lv i j hs acc =
  admit ();
  let ihs = S.upd hs lv (S.snoc (S.index hs lv) acc) in
  if j % 2 = 1 && S.length (S.index hs lv) > 0 
  then (let nacc = hash_2 (S.last (S.index hs lv)) acc in
       insert_ (lv + 1) 
	       (Ghost.hide (Ghost.reveal i / 2)) (j / 2)
	       ihs nacc)
  else ihs

val mt_insert:
  mt:wf_mt{mt_not_full mt} -> v:hash -> GTot wf_mt
let mt_insert mt v =
  MT (MT?.i mt)
     (MT?.j mt + 1)
     (insert_ 0 (Ghost.hide (MT?.i mt)) (MT?.j mt) (MT?.hs mt) v)
     false
     (MT?.rhs mt)

val create_mt: init:hash -> GTot wf_mt
let create_mt init =
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

// TODOs:
// path_insert
// mt_get_path
// mt_flush_to
// mt_flush
// mt_verify


