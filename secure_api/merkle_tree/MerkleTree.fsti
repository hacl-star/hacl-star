module MerkleTree

module HST = FStar.HyperStack.ST
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer

module U32 = FStar.UInt32
module U64 = FStar.UInt64

module MTS = MerkleTree.Spec
module MTNL = MerkleTree.New.Low
module MTNLH = MerkleTree.New.Low.Hashes
module MTNLHF = MerkleTree.New.Low.Hashfunctions
module MTNLS = MerkleTree.New.Low.Serialization


let hash_size_t = MTNLH.hash_size_t
let offset_t = MTNL.offset_t
let index_t = MTNL.index_t
let hash #hsz = MTNLH.hash #hsz
let uint64_t = UInt64.t

let path #hsz = MTNL.path #hsz
let path_p #hsz = MTNL.path_p #hsz 
let const_path_p #hsz = MTNL.const_path_p #hsz

let merkle_tree = MTNL.merkle_tree
let mt_p = MTNL.mt_p
let const_mt_p = MTNL.const_mt_p


[@ (Comment "Constructors and destructors for hashes and paths")]
val init_hash (hash_size:hash_size_t) (r:HST.erid): HST.St (hash #hash_size) 
val free_hash (hash_size:hash_size_t) (h:hash #hash_size): HST.St unit

val init_path (#hash_size:hash_size_t) (mtr:HH.rid) (r:HST.erid): HST.St (path_p #hash_size)
val clear_path (hash_size:hash_size_t) (mtr:HH.rid) (p:path_p #hash_size): HST.St unit  
val free_path (hash_size:hash_size_t) (p:path_p #hash_size): HST.St unit

[@ (Comment "Construction

  @param[in]  i   The initial hash")]
val mt_create: r:HST.erid -> init:hash #32ul -> HST.St mt_p

val mt_create_custom:
  hsz:hash_size_t ->
  hash_spec:Ghost.erased (MTS.hash_fun_t #(U32.v hsz)) ->
  r:HST.erid -> init:hash #hsz -> hash_fun:MTNLHF.hash_fun_t #hsz #hash_spec -> HST.St mt_p


[@ (Comment "  Destruction

    @param[in]  mt  The Merkle tree")]
val mt_free: mt:mt_p -> HST.St unit


[@ (Comment "Insertion

  param[in]  mt  The Merkle tree
  param[in]  v   The tree does not take ownership of the hash, it makes a copy of its content.

 Note: The content of the hash will be overwritten with an arbitrary value.")] 
val mt_insert: hsz:Ghost.erased hash_size_t -> mt:mt_p -> v:hash #hsz -> HST.St unit

[@ (Comment "Precondition predicate for mt_insert")]
val mt_insert_pre: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> v:hash #hsz -> HST.St bool


[@ (Comment "Getting the Merkle root

  param[in]  mt   The Merkle tree
  param[out] root The Merkle root returned as a hash pointer")]
val mt_get_root: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> rt:hash #hsz -> HST.St unit
  
[@ (Comment "Precondition predicate for mt_get_root")]
val mt_get_root_pre: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> rt:hash #hsz -> HST.St bool
  

[@ (Comment "Getting a Merkle path

  param[in]  mt   The Merkle tree
  param[in]  idx  The index of the target hash
  param[out] root The Merkle root
  param[out] path A resulting Merkle path that contains the leaf hash.

  return The number of elements in the tree

  Notes:
  - The resulting path contains pointers to hashes in the tree, not copies of
    the hash values.
  - idx must be within the currently held indices in the tree (past the
    last flush index).")]
val mt_get_path: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> idx:offset_t -> p:path_p #hsz -> root:hash #hsz -> HST.St index_t

[@ (Comment "Precondition predicate for mt_get_path")]
val mt_get_path_pre: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> idx:offset_t -> p:const_path_p #hsz -> root:hash #hsz -> HST.St bool



[@ (Comment "Flush the Merkle tree

  param[in]  mt   The Merkle tree")]
val mt_flush: mt:mt_p -> HST.St unit

[@ (Comment "Precondition predicate for mt_flush")]
val mt_flush_pre: mt:const_mt_p -> HST.St bool


[@ (Comment "Flush the Merkle tree up to a given index
 
  param[in]  mt   The Merkle tree
  param[in]  idx  The index up to which to flush the tree")]
val mt_flush_to: mt:mt_p -> idx:offset_t -> HST.St unit
  
[@ (Comment "Precondition predicate for mt_flush_to")]
val mt_flush_to_pre: mt:const_mt_p -> idx:offset_t -> HST.St bool


[@ (Comment "Retract the Merkle tree down to a given index

  param[in]  mt   The Merkle tree
  param[in]  idx  The index to retract the tree to

 Note: The element and idx will remain in the tree.")]
val mt_retract_to: mt:mt_p -> r:offset_t -> HST.St unit

[@ (Comment "Precondition predicate for mt_retract_to")]
val mt_retract_to_pre: mt:const_mt_p -> r:offset_t -> HST.St bool


[@ (Comment "Client-side verification

  param[in]  mt   The Merkle tree
  param[in]  tgt  The index of the target hash
  param[in]  max  The maximum index + 1 of the tree when the path was generated
  param[in]  path The Merkle path to verify
  param[in]  root

  return true if the verification succeeded, false otherwise
  
  Note: max - tgt must be less than 2^32.")]
val mt_verify: #hsz:Ghost.erased hash_size_t -> #hash_spec:MTS.hash_fun_t #(U32.v hsz) -> mt:const_mt_p -> k:uint64_t -> j:uint64_t -> mtr:HH.rid -> p:const_path_p #hsz ->
  rt:hash #hsz -> HST.St bool


[@ (Comment "Precondition predicate for mt_verify")]
val mt_verify_pre: #hsz:Ghost.erased hash_size_t -> mt:const_mt_p -> k:uint64_t -> j:uint64_t -> mtr:HH.rid -> p:const_path_p #hsz -> rt:hash #hsz -> HST.St bool


[@ (Comment "Serialization size

  param[in]  mt   The Merkle tree

  return the number of bytes required to serialize the tree")]
val mt_serialize_size: mt:const_mt_p -> HST.St uint64_t
  

[@ (Comment "Merkle tree serialization

  param[in]  mt   The Merkle tree
  param[out] buf  The buffer to serialize the tree into
  param[in]  len  Length of buf

  return the number of bytes written

  Note: buf must be a buffer of size mt_serialize_size(mt) or larger, but
  smaller than 2^32 (larger buffers are currently not supported).")]
val mt_serialize: mt:const_mt_p -> output:MTNLS.uint8_p -> sz:uint64_t -> HST.St uint64_t


[@ (Comment "Merkle tree deserialization

  param[in]  buf  The buffer to deserialize the tree from
  param[in]  len  Length of buf

  return pointer to the new tree if successful, NULL otherwise

  Note: buf must point to an allocated buffer.")]
val mt_deserialize: #hash_size:hash_size_t -> rid:HST.erid -> input:MTNLS.const_uint8_p -> sz:uint64_t{CB.length input = U64.v sz} -> hash_spec:Ghost.erased(MTS.hash_fun_t #(U32.v hash_size)) -> hash_fun:MTNLHF.hash_fun_t #hash_size #hash_spec -> HST.St (B.pointer_or_null merkle_tree)


[@ (Comment "Path serialization

  param[in]  path The path
  param[in]  mt   The Merkle tree the path belongs to
  param[out] buf  The buffer to serialize the path into
  param[in]  len  Length of buf

  return the number of bytes written")]
val mt_serialize_path: #hsz:Ghost.erased hash_size_t -> p:const_path_p #hsz -> mt:const_mt_p -> output:MTNLS.uint8_p -> sz:uint64_t -> HST.St uint64_t



[@ (Comment "Path deserialization

  param[in]  buf  The buffer to deserialize the path from
  param[in]  len  Length of buf

  return pointer to the new path if successful, NULL otherwise
  
 Note: buf must point to an allocated buffer.")]
val mt_deserialize_path: #hsz:hash_size_t -> rid:HST.erid -> input:MTNLS.const_uint8_p -> sz:uint64_t{CB.length input = U64.v sz} -> HST.St (B.pointer_or_null (path #hsz))
