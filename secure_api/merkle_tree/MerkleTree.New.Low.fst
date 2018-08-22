module MerkleTree.New.Low

open EverCrypt.Hash
open EverCrypt.Helpers

open FStar.All
open FStar.Integers
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open LowStar.Vector
open LowStar.BufVector

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = LowStar.Vector
module BV = LowStar.BufVector
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8

module EHS = EverCrypt.Hash
module EHL = EverCrypt.Helpers

type hash = uint8_p
type hash_vec = BV.buf_vector uint8_t

val hash_size: uint32_t
let hash_size = EHS.tagLen EHS.SHA256

/// Compression of two hashes

val hash_2: 
  src1:hash -> src2:hash -> dst:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_live hash_size h0 src1 /\
	   BV.buffer_inv_live hash_size h0 src2 /\
	   BV.buffer_inv_live hash_size h0 dst))
	 (ensures (fun h0 _ h1 -> true))
let hash_2 src1 src2 dst =
  admit ();
  HST.push_frame ();
  let st = EHS.create EHS.SHA256 in
  EHS.init st;

  let sb1 = B.alloca 0uy (EHS.blockLen EHS.SHA256) in
  let sb2 = B.alloca 0uy (EHS.blockLen EHS.SHA256) in
  B.blit src1 0ul sb1 0ul hash_size;
  B.blit src2 0ul sb2 0ul hash_size;

  EHS.update (Ghost.hide S.empty) st sb1;
  let hh1 = HST.get () in
  EHS.update (Ghost.hide (B.as_seq hh1 sb1)) st sb2;
  EHS.finish st dst;
  HST.pop_frame ()

/// Low-level Merkle tree data structure

// A Merkle tree `MT i j hs` stores all necessary hashes to generate
// a Merkle path for each element from the index `i` to `j-1`. 
// `hs` is a 2-dim store for hashes, where `hs[0]` contains leaf hash values.
// `ths` is a store for "rightmost" hashes, manipulated only when required to
// calculate some merkle paths that need the rightmost hashes as a part of them.
noeq type merkle_tree = 
| MT: i:uint32_t -> j:uint32_t{j > i} ->
      hs:B.buffer hash_vec{B.length hs = 32} ->
      ths:hash_vec{V.size_of ths = 32ul} ->
      merkle_tree

/// Construction

val create_mt_: 
  hs:B.buffer hash_vec{B.length hs = 32} ->
  depth:uint32_t{depth <= 32ul} ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 hs /\
	   HST.is_eternal_region (B.frameOf hs)))
	 (ensures (fun h0 mt h1 -> true))
	 (decreases (U32.v depth))
let rec create_mt_ hs depth =
  if depth = 0ul then ()
  else (let dr = BV.new_region_ (B.frameOf hs) in
       let hv = BV.create_reserve hash_size 1ul dr in
       B.upd hs (depth - 1ul) hv;
       create_mt_ hs (depth - 1ul))

val create_mt: unit ->
  HST.ST merkle_tree
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> true))
let create_mt _ =
  let mt_region = BV.new_region_ HH.root in
  let hs = B.malloc mt_region (BV.create_empty uint8_t) 32ul in
  create_mt_ hs 32ul;
  let ths = BV.create 0uy hash_size 32ul in
  MT 0ul 1ul hs ths

/// Destruction (free)

val free_mt_:
  lv:uint32_t{lv <= 32ul} ->
  hs:B.buffer hash_vec{B.length hs = 32} ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec free_mt_ lv hs =
  admit ();
  if lv = 0ul then ()
  else (BV.free hash_size (B.index hs (lv - 1ul));
       free_mt_ (lv - 1ul) hs)

val free_mt: merkle_tree ->
  HST.ST unit
	 (requires (fun _ -> true))
	 (ensures (fun h0 _ h1 -> true))
let free_mt mt =
  admit ();
  free_mt_ 32ul (MT?.hs mt);
  BV.free hash_size (MT?.ths mt);
  B.free (MT?.hs mt)

/// Insertion

val insert_:
  lv:uint32_t{lv < 32ul} ->
  j:uint32_t ->
  hs:B.buffer hash_vec{B.length hs = 32} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert_ lv j hs acc =
  admit ();
  if j % 2ul = 0ul then 
    B.upd hs lv (V.insert (B.index hs lv) acc)
  else
    (B.upd hs lv (V.insert (B.index hs lv) acc);
    hash_2 (V.back (B.index hs lv)) acc acc;
    insert_ (lv + 1ul) (j / 2ul) hs acc)

// Caution: current impl. manipulates the content in `v`
//          as an accumulator.
val insert:
  mt:merkle_tree -> v:hash ->
  HST.ST merkle_tree
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec insert mt v =
  admit ();
  insert_ 0ul (MT?.j mt) (MT?.hs mt) v;
  MT (MT?.i mt)
     (MT?.j mt + 1ul)
     (MT?.hs mt)
     (MT?.ths mt)

/// Getting the Merkle root and path

val fill_rightmost:
  lv:uint32_t{lv < 32ul} ->
  hs:B.buffer hash_vec{B.length hs = 32} ->
  ths:hash_vec{V.size_of ths = 32ul} ->
  j:uint32_t ->
  acc:hash -> actd:bool ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec fill_rightmost lv hs ths j acc actd =
  admit ();
  if j = 0ul then ()
  else if j % 2ul = 0ul
  then fill_rightmost (lv + 1ul) hs ths (j / 2ul) acc actd
  else (
    (if actd
    then (hash_2 (V.index (B.index hs lv) (j - 1ul)) acc acc;
	 BV.assign_copy hash_size ths (lv + 1ul) acc)
    else B.blit (V.index (B.index hs lv) (j - 1ul)) 0ul acc 0ul hash_size);
    fill_rightmost (lv + 1ul) hs ths (j / 2ul) acc true)

// Assuming the rightmost hashes (`ths`) are already calculated
val mt_get_path_:
  lv:uint32_t{lv < 32ul} ->
  hs:B.buffer hash_vec{B.length hs = 32} ->
  ths:hash_vec{V.size_of ths = 32ul} ->
  j:uint32_t -> k:uint32_t{j = 0ul || k < j} ->
  path:B.buffer hash{B.length path = 32} ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_get_path_ lv hs ths j k path =
  admit ();
  if j = 0ul then ()
  else if k % 2ul = 0ul 
  then (if k + 1ul < j
       then (B.upd path lv (V.index (B.index hs lv) (k + 1ul));
	    mt_get_path_ (lv + 1ul) hs ths (j / 2ul) (k / 2ul) path)
       else (B.upd path lv (V.index ths lv);
	    mt_get_path_ (lv + 1ul) hs ths (j / 2ul) (k / 2ul) path))
  else (B.upd path lv (V.index (B.index hs lv) (k - 1ul));
       mt_get_path_ (lv + 1ul) hs ths (j / 2ul) (k / 2ul) path)

val mt_get_path:
  mt:merkle_tree -> 
  idx:uint32_t{MT?.i mt <= idx && idx < MT?.j mt} ->
  root:hash ->
  path:B.buffer hash{B.length path = 32} ->
  HST.ST uint32_t
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_get_path mt idx root path =
  fill_rightmost 0ul (MT?.hs mt) (MT?.ths mt) (MT?.j mt) root false;
  mt_get_path_ 0ul (MT?.hs mt) (MT?.ths mt) (MT?.j mt) idx path;
  MT?.j mt

/// Flushing

// TODO: need to think about flushing after deciding a proper 
//       data structure for `MT?.hs`.
// NOTE: flush "until" `idx`
val mt_flush_to:
  mt:merkle_tree ->
  idx:uint32_t{idx <= MT?.j mt} ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush_to mt idx = ()

val mt_flush:
  mt:merkle_tree ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_flush mt =
  mt_flush_to mt (MT?.j mt)

/// Client-side verification

val mt_verify_:
  lv:uint32_t{lv < 32ul} ->
  k:uint32_t ->
  j:uint32_t{j = 0ul || k < j} ->
  path:B.buffer hash{B.length path = 32} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let rec mt_verify_ lv k j path acc =
  admit ();
  if j = 0ul then ()
  else
    (if k % 2ul = 1ul
    then (if k + 1ul < j
	 then hash_2 acc (B.index path lv) acc
	 else ())
    else hash_2 (B.index path lv) acc acc;
    mt_verify_ (lv + 1ul) (k / 2ul) (j / 2ul) path acc)

val buf_eq:
  #a:eqtype -> b1:B.buffer a -> b2:B.buffer a ->
  len:uint32_t ->
  HST.ST bool
	 (requires (fun h0 -> 
	   B.live h0 b1 /\ B.live h0 b2 /\
	   len <= B.len b1 /\ len <= B.len b2))
	 (ensures (fun h0 _ h1 -> true))
let rec buf_eq #a b1 b2 len =
  if len = 0ul then true
  else (let a1 = B.index b1 (len - 1ul) in
       let a2 = B.index b2 (len - 1ul) in
       let teq = buf_eq b1 b2 (len - 1ul) in
       a1 = a2 && teq)

val mt_verify:
  k:uint32_t ->
  j:uint32_t{k < j} ->
  path:B.buffer hash{B.length path = 32} ->
  root:hash ->
  HST.ST bool
	 (requires (fun h0 -> true))
	 (ensures (fun h0 _ h1 -> true))
let mt_verify k j path root =
  admit ();
  let acc = B.malloc HH.root 0uy hash_size in
  mt_verify_ 0ul k j path acc;
  buf_eq acc root hash_size

