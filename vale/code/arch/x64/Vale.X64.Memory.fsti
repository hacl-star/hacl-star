module Vale.X64.Memory
include Vale.Arch.HeapTypes_s
open FStar.Mul
open Vale.Def.Prop_s
open Vale.X64.Machine_s
open Vale.Arch.HeapImpl

unfold let vale_heap = vale_heap
unfold let vale_heap_impl = vale_heap_impl

let get_vale_heap (vhi:vale_heap_impl) : vale_heap = vhi
let set_vale_heap (vhi:vale_heap_impl) (vh:vale_heap) : vale_heap_impl = vh
let vale_heap_impl_equal (h1 h2:vale_heap_impl) = h1 == h2

unfold let nat8 = Vale.Def.Words_s.nat8
unfold let nat16 = Vale.Def.Words_s.nat16
unfold let nat32 = Vale.Def.Words_s.nat32
unfold let nat64 = Vale.Def.Words_s.nat64
unfold let quad32 = Vale.Def.Types_s.quad32

let base_typ_as_vale_type (t:base_typ) : Tot eqtype =
  match t with
  | TUInt8 -> nat8
  | TUInt16 -> nat16
  | TUInt32 -> nat32
  | TUInt64 -> nat64
  | TUInt128 -> quad32

val buffer (t:base_typ) : Type u#1
val buffer_as_seq (#t:base_typ) (h:vale_heap) (b:buffer t) : GTot (Seq.seq (base_typ_as_vale_type t))
val buffer_readable (#t:base_typ) (h:vale_heap) (b:buffer t) : GTot prop0
val buffer_writeable (#t:base_typ) (b:buffer t) : GTot prop0
val buffer_length (#t:base_typ) (b:buffer t) : GTot nat
val loc : Type u#0
val loc_none : loc
val loc_union (s1 s2:loc) : GTot loc
val loc_buffer (#t:base_typ) (b:buffer t) : GTot loc
val loc_disjoint (s1 s2:loc) : GTot prop0
val loc_includes (s1 s2:loc) : GTot prop0
val modifies (s:loc) (h1 h2:vale_heap) : GTot prop0

let valid_buffer_read (#t:base_typ) (h:vale_heap) (b:buffer t) (i:int) : prop0 =
  0 <= i /\ i < buffer_length b /\ buffer_readable h b

let valid_buffer_write (#t:base_typ) (h:vale_heap) (b:buffer t) (i:int) : prop0 =
  valid_buffer_read h b i /\ buffer_writeable b

// Named abbreviations for Vale type system:
unfold let vuint8 = TUInt8
unfold let vuint16 = TUInt16
unfold let vuint32 = TUInt32
unfold let vuint64 = TUInt64
unfold let vuint128 = TUInt128

let buffer8 = buffer vuint8
let buffer16 = buffer vuint16
let buffer32 = buffer vuint32
let buffer64 = buffer vuint64
let buffer128 = buffer vuint128

val buffer_addr (#t:base_typ) (b:buffer t) (h:vale_heap) : GTot int

unfold
let locs_disjoint (ls:list loc) : prop0 =
  BigOps.normal (BigOps.pairwise_and' (fun x y -> loc_disjoint x y /\ loc_disjoint y x) ls)

// equivalent to modifies; used to prove modifies clauses via modifies_goal_directed_trans
val modifies_goal_directed (s:loc) (h1 h2:vale_heap) : GTot prop0
val lemma_modifies_goal_directed (s:loc) (h1 h2:vale_heap) : Lemma
  (modifies s h1 h2 == modifies_goal_directed s h1 h2)

val buffer_length_buffer_as_seq (#t:base_typ) (h:vale_heap) (b:buffer t) : Lemma
  (requires True)
  (ensures (Seq.length (buffer_as_seq h b) == buffer_length b))
  [SMTPat (Seq.length (buffer_as_seq h b))]

val modifies_buffer_elim (#t1:base_typ) (b:buffer t1) (p:loc) (h h':vale_heap) : Lemma
  (requires
    loc_disjoint (loc_buffer b) p /\
    buffer_readable h b /\
    modifies p h h'
  )
  (ensures
    buffer_readable h b /\
    buffer_readable h' b /\
    buffer_as_seq h b == buffer_as_seq h' b
  )
  [SMTPatOr [
    [SMTPat (modifies p h h'); SMTPat (buffer_readable h' b)];
    [SMTPat (modifies p h h'); SMTPat (buffer_as_seq h' b)];
  ]]

val modifies_buffer_addr (#t:base_typ) (b:buffer t) (p:loc) (h h':vale_heap) : Lemma
  (requires
    modifies p h h'
  )
  (ensures buffer_addr b h == buffer_addr b h')
  [SMTPat (modifies p h h'); SMTPat (buffer_addr b h')]


val modifies_buffer_readable (#t:base_typ) (b:buffer t) (p:loc) (h h':vale_heap) : Lemma
  (requires
    modifies p h h' /\
    buffer_readable h b
  )
  (ensures buffer_readable h' b)
  [SMTPat (modifies p h h'); SMTPat (buffer_readable h' b)]

val loc_disjoint_none_r (s:loc) : Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r (s s1 s2:loc) : Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_includes_refl (s:loc) : Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans (s1 s2 s3:loc) : Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r (s s1 s2:loc) : Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_union_l (s1 s2 s:loc) : Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  // for efficiency, no SMT pattern

val loc_includes_union_l_buffer (#t:base_typ) (s1 s2:loc) (b:buffer t) : Lemma
  (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
  (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]

val loc_includes_none (s:loc) : Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val modifies_refl (s:loc) (h:vale_heap) : Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_goal_directed_refl (s:loc) (h:vale_heap) : Lemma
  (modifies_goal_directed s h h)
  [SMTPat (modifies_goal_directed s h h)]

val modifies_loc_includes (s1:loc) (h h':vale_heap) (s2:loc) : Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  // for efficiency, no SMT pattern

val modifies_trans (s12:loc) (h1 h2:vale_heap) (s23:loc) (h3:vale_heap) : Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  // for efficiency, no SMT pattern

// Prove (modifies s13 h1 h3).
// To avoid unnecessary matches, don't introduce any other modifies terms.
// Introduce modifies_goal_directed instead.
val modifies_goal_directed_trans (s12:loc) (h1 h2:vale_heap) (s13:loc) (h3:vale_heap) : Lemma
  (requires
    modifies s12 h1 h2 /\
    modifies_goal_directed s13 h2 h3 /\
    loc_includes s13 s12
  )
  (ensures (modifies s13 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s13 h1 h3)]

val modifies_goal_directed_trans2 (s12:loc) (h1 h2:vale_heap) (s13:loc) (h3:vale_heap) : Lemma
  (requires
    modifies s12 h1 h2 /\
    modifies_goal_directed s13 h2 h3 /\
    loc_includes s13 s12
  )
  (ensures (modifies_goal_directed s13 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies_goal_directed s13 h1 h3)]

val buffer_read (#t:base_typ) (b:buffer t) (i:int) (h:vale_heap) : Ghost (base_typ_as_vale_type t)
  (requires True)
  (ensures (fun v ->
    0 <= i /\ i < buffer_length b /\ buffer_readable h b ==>
    v == Seq.index (buffer_as_seq h b) i
  ))

val buffer_write (#t:base_typ) (b:buffer t) (i:int) (v:base_typ_as_vale_type t) (h:vale_heap) : Ghost vale_heap
  (requires buffer_readable h b /\ buffer_writeable b)
  (ensures (fun h' ->
    0 <= i /\ i < buffer_length b /\ buffer_readable h b ==>
    modifies (loc_buffer b) h h' /\
    buffer_readable h' b /\
    buffer_as_seq h' b == Seq.upd (buffer_as_seq h b) i v
  ))

val valid_mem64 (ptr:int) (h:vale_heap) : GTot bool // is there a 64-bit word at address ptr?
val writeable_mem64 (ptr:int) (h:vale_heap) : GTot bool // can we write a 64-bit word at address ptr?
val load_mem64 (ptr:int) (h:vale_heap) : GTot nat64 // the 64-bit word at ptr (if valid_mem64 holds)
val store_mem64 (ptr:int) (v:nat64) (h:vale_heap) : GTot vale_heap

val valid_mem128 (ptr:int) (h:vale_heap) : GTot bool
val writeable_mem128 (ptr:int) (h:vale_heap) : GTot bool
val load_mem128  (ptr:int) (h:vale_heap) : GTot quad32
val store_mem128 (ptr:int) (v:quad32) (h:vale_heap) : GTot vale_heap

val lemma_valid_mem64 (b:buffer64) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    valid_mem64 (buffer_addr b h + 8 * i) h
  )

val lemma_writeable_mem64 (b:buffer64) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures
    writeable_mem64 (buffer_addr b h + 8 * i) h
  )

val lemma_load_mem64 (b:buffer64) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    load_mem64 (buffer_addr b h + 8 * i) h == buffer_read b i h
  )

val lemma_store_mem64 (b:buffer64) (i:nat) (v:nat64) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures
    store_mem64 (buffer_addr b h + 8 * i) v h == buffer_write b i v h
  )

val lemma_valid_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    valid_mem128 (buffer_addr b h + 16 * i) h
  )

val lemma_writeable_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures
    writeable_mem128 (buffer_addr b h + 16 * i) h
  )

val lemma_load_mem128 (b:buffer128) (i:nat) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b
  )
  (ensures
    load_mem128 (buffer_addr b h + 16 * i) h == buffer_read b i h
  )

val lemma_store_mem128 (b:buffer128) (i:nat) (v:quad32) (h:vale_heap) : Lemma
  (requires
    i < Seq.length (buffer_as_seq h b) /\
    buffer_readable h b /\
    buffer_writeable b
  )
  (ensures
    store_mem128 (buffer_addr b h + 16 * i) v h == buffer_write b i v h
  )

//Memtaint related functions

type memtaint = memTaint_t

val valid_taint_buf64 (b:buffer64) (vale_heap:vale_heap) (memTaint:memtaint) (t:taint) : GTot prop0
val valid_taint_buf128 (b:buffer128) (vale_heap:vale_heap) (memTaint:memtaint) (t:taint) : GTot prop0

val lemma_valid_taint64
    (b:buffer64)
    (memTaint:memtaint)
    (vale_heap:vale_heap)
    (i:nat{i < buffer_length b})
    (t:taint)
  : Lemma
  (requires valid_taint_buf64 b vale_heap memTaint t /\ buffer_readable vale_heap b)
  (ensures (
    let ptr = buffer_addr b vale_heap + 8 * i in
    forall i'.{:pattern Map.sel memTaint i'} i' >= ptr /\ i' < ptr + 8 ==> Map.sel memTaint i' == t))

val lemma_valid_taint128
    (b:buffer128)
    (memTaint:memtaint)
    (vale_heap:vale_heap)
    (i:nat{i < buffer_length b})
    (t:taint)
  : Lemma
  (requires valid_taint_buf128 b vale_heap memTaint t /\ buffer_readable vale_heap b)
  (ensures (
    let ptr = buffer_addr b vale_heap + 16 * i in
    forall i'.{:pattern Map.sel memTaint i'} i' >= ptr /\ i' < ptr + 16 ==> Map.sel memTaint i' == t))

val same_memTaint64
    (b:buffer64)
    (mem0:vale_heap)
    (mem1:vale_heap)
    (memtaint0:memtaint)
    (memtaint1:memtaint)
  : Lemma
  (requires (modifies (loc_buffer b) mem0 mem1 /\
    (forall p.{:pattern Map.sel memtaint0 p \/ Map.sel memtaint1 p} Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

val same_memTaint128
    (b:buffer128)
    (mem0:vale_heap)
    (mem1:vale_heap)
    (memtaint0:memtaint)
    (memtaint1:memtaint)
  : Lemma
  (requires (modifies (loc_buffer b) mem0 mem1 /\
    (forall p.{:pattern Map.sel memtaint0 p \/ Map.sel memtaint1 p} Map.sel memtaint0 p == Map.sel memtaint1 p)))
  (ensures memtaint0 == memtaint1)

val modifies_valid_taint64 (b:buffer64) (p:loc) (h h':vale_heap) (memTaint:memtaint) (t:taint) : Lemma
  (requires modifies p h h')
  (ensures valid_taint_buf64 b h memTaint t <==> valid_taint_buf64 b h' memTaint t)
  [SMTPat (modifies p h h'); SMTPat (valid_taint_buf64 b h' memTaint t)]

val modifies_valid_taint128 (b:buffer128) (p:loc) (h h':vale_heap) (memTaint:memtaint) (t:taint) : Lemma
  (requires modifies p h h')
  (ensures valid_taint_buf128 b h memTaint t <==> valid_taint_buf128 b h' memTaint t)
  [SMTPat (modifies p h h'); SMTPat (valid_taint_buf128 b h' memTaint t)]
