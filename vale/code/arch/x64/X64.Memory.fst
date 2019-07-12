module X64.Memory

module M = X64.Memory_s

let heap = M.heap
let mem = M.mem

let coerce (#a:Type0) (b:Type0{a == b}) (x:a) : b = x

let m_of_typ (t:typ) : M.typ =
  match t with
  | TBase TUInt8 -> M.TBase M.TUInt8
  | TBase TUInt16 -> M.TBase M.TUInt16
  | TBase TUInt32 -> M.TBase M.TUInt32
  | TBase TUInt64 -> M.TBase M.TUInt64
  | TBase TUInt128 -> M.TBase M.TUInt128

let buffer t = M.buffer (m_of_typ t)

let buffer_as_seq #t h b = M.buffer_as_seq h b
let buffer_readable #t h b = M.buffer_readable h b
let buffer_length #t b = M.buffer_length b
let loc = M.loc
let loc_none = M.loc_none
let loc_union = M.loc_union
let loc_buffer #t b = M.loc_buffer b
let loc_disjoint = M.loc_disjoint
let loc_includes = M.loc_includes
let modifies = M.modifies

let buffer_addr #t b m = M.buffer_addr b m

let modifies_goal_directed s h1 h2 = modifies s h1 h2
let lemma_modifies_goal_directed s h1 h2 = ()

let buffer_length_buffer_as_seq #t h b = M.buffer_length_buffer_as_seq h b

let modifies_buffer_elim #t1 b p h h' = M.modifies_buffer_elim b p h h'

let modifies_buffer_addr #t b p h h' = M.modifies_buffer_addr b p h h'

let modifies_buffer_readable #t b p h h' = M.modifies_buffer_readable b p h h'

let loc_disjoint_none_r s = M.loc_disjoint_none_r s
let loc_disjoint_union_r s s1 s2 = M.loc_disjoint_union_r s s1 s2
let loc_includes_refl s = M.loc_includes_refl s
let loc_includes_trans s1 s2 s3 = M.loc_includes_trans s1 s2 s3
let loc_includes_union_r s s1 s2 = M.loc_includes_union_r s s1 s2
let loc_includes_union_l s1 s2 s = M.loc_includes_union_l s1 s2 s
let loc_includes_union_l_buffer #t s1 s2 b = M.loc_includes_union_l s1 s2 (loc_buffer b)
let loc_includes_none s = M.loc_includes_none s
let modifies_refl s h = M.modifies_refl s h
let modifies_goal_directed_refl s h = M.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = M.modifies_loc_includes s1 h h' s2
let modifies_trans s12 h1 h2 s23 h3 = M.modifies_trans s12 h1 h2 s23 h3

let modifies_goal_directed_trans s12 h1 h2 s13 h3 =
  modifies_trans s12 h1 h2 s13 h3;
  modifies_loc_includes s13 h1 h3 (loc_union s12 s13);
  ()

let modifies_goal_directed_trans2 s12 h1 h2 s13 h3 = modifies_goal_directed_trans s12 h1 h2 s13 h3

let buffer_read #t b i h = M.buffer_read b i h
let buffer_write #t b i v h = M.buffer_write b i v h

let valid_mem64 = M.valid_mem64
let load_mem64 = M.load_mem64
let store_mem64 = M.store_mem64

let valid_mem128 = M.valid_mem128
let load_mem128 = M.load_mem128
let store_mem128 = M.store_mem128

let lemma_valid_mem64 = M.lemma_valid_mem64
let lemma_load_mem64 = M.lemma_load_mem64
let lemma_store_mem64 = M.lemma_store_mem64

let lemma_valid_mem128 = M.lemma_valid_mem128
let lemma_load_mem128 = M.lemma_load_mem128
let lemma_store_mem128 = M.lemma_store_mem128

let lemma_store_load_mem64 = M.lemma_store_load_mem64
let lemma_frame_store_mem64 = M.lemma_frame_store_mem64
let lemma_valid_store_mem64 = M.lemma_valid_store_mem64

let lemma_store_load_mem128 = M.lemma_store_load_mem128
let lemma_frame_store_mem128 = M.lemma_frame_store_mem128
let lemma_valid_store_mem128 = M.lemma_valid_store_mem128

let memtaint = M.memtaint

let valid_taint_buf64 = M.valid_taint_buf64
let valid_taint_buf128 = M.valid_taint_buf128

let modifies_valid_taint64 = M.modifies_valid_taint64
let modifies_valid_taint128 = M.modifies_valid_taint128
