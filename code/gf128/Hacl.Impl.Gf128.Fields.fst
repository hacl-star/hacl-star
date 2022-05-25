module Hacl.Impl.Gf128.Fields

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.IntVector
open Lib.Buffer

open Hacl.Spec.GF128.Vec

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.GF128
module GF = Spec.GaloisField


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

noextract
type field_spec = gf128_spec

inline_for_extraction noextract
let elem_t (s:field_spec) =
  match s with
  | PreComp -> uint64
  | NI -> vec_t U128 1

inline_for_extraction noextract
let elem_zero (s:field_spec) : elem_t s =
  match s with
  | PreComp -> u64 0
  | NI -> vec_zero U128 1

inline_for_extraction noextract
let felem_len (s:field_spec) =
  match s with
  | PreComp -> 2ul
  | NI -> 1ul

inline_for_extraction noextract
let felem4_len (s:field_spec) =
  match s with
  | PreComp -> 8ul
  | NI -> 4ul

inline_for_extraction noextract
let precomp_len (s:field_spec) =
  match s with
  | PreComp -> 264ul
  | NI -> 4ul

inline_for_extraction noextract
let felem (s:field_spec) = lbuffer (elem_t s) (felem_len s)

inline_for_extraction noextract
let felem4 (s:field_spec) = lbuffer (elem_t s) (felem4_len s)

inline_for_extraction noextract
let precomp (s:field_spec) = lbuffer (elem_t s) (precomp_len s)

inline_for_extraction noextract
type block = lbuffer uint8 16ul

inline_for_extraction noextract
type block4 = lbuffer uint8 64ul

noextract
val feval: #s:field_spec -> h:mem -> e:felem s -> GTot elem
let feval #s h e =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.feval h e
  | NI -> Hacl.Impl.Gf128.FieldNI.feval h e

noextract
val feval4: #s:field_spec -> h:mem -> e:felem4 s -> GTot elem4
let feval4 #s h e =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.feval4 h e
  | NI -> Hacl.Impl.Gf128.FieldNI.feval4 h e

noextract
let zero = GF.zero #S.gf128


noextract
val get_r1: #s:field_spec -> h:mem -> p:precomp s -> GTot S.elem
let get_r1 #s h pre =
  match s with
  | PreComp -> feval h (gsub pre 6ul 2ul)
  | NI -> feval h (gsub pre 3ul 1ul)


noextract
val get_r4: #s:field_spec -> h:mem -> p:precomp s -> GTot S.elem
let get_r4 #s h pre =
  match s with
  | PreComp -> feval h (gsub pre 0ul 2ul)
  | NI -> feval h (gsub pre 0ul 1ul)


noextract
val get_r4321: #s:field_spec -> h:mem -> p:precomp s -> GTot elem4
let get_r4321 #s h pre =
  match s with
  | PreComp -> feval4 h (gsub pre 0ul 8ul)
  | NI -> feval4 h pre


noextract
val precomp_inv_t: #s:field_spec -> h:mem -> pre:precomp s -> Type0
let precomp_inv_t #s h pre =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.load_precomp_r_inv h pre
  | NI -> get_r4321 h pre == load_precompute_r (get_r1 h pre)


inline_for_extraction noextract
val create_felem: s:field_spec ->
  StackInline (felem s)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v (felem_len s)) (elem_zero s)) /\
    feval h1 f == zero)

let create_felem s =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.create_felem ()
  | NI -> Hacl.Impl.Gf128.FieldNI.create_felem ()


inline_for_extraction noextract
val copy_felem:
    #s:field_spec
  -> f1:felem s
  -> f2:felem s ->
  Stack unit
  (requires fun h -> live h f1 /\ live h f2 /\ disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies1 f1 h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)

let copy_felem #s f1 f2 =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.copy_felem f1 f2
  | NI -> Hacl.Impl.Gf128.FieldNI.copy_felem f1 f2


inline_for_extraction noextract
val felem_set_zero:
    #s:field_spec
  -> f:felem s ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies1 f h0 h1 /\
    feval h1 f == zero)

let felem_set_zero #s f =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.felem_set_zero f
  | NI -> Hacl.Impl.Gf128.FieldNI.felem_set_zero f


inline_for_extraction noextract
val create_felem4: s:field_spec ->
  StackInline (felem4 s)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (v (felem4_len s)) (elem_zero s)) /\
    feval4 h1 f == LSeq.create 4 zero)

let create_felem4 s =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.create_felem4 ()
  | NI -> Hacl.Impl.Gf128.FieldNI.create_felem4 ()


inline_for_extraction noextract
val load_felem:
    #s:field_spec
  -> x:felem s
  -> y:block ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let load_felem #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.load_felem x y
  | NI -> Hacl.Impl.Gf128.FieldNI.load_felem x y


inline_for_extraction noextract
val load_felem4:
    #s:field_spec
  -> x:felem4 s
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == encode4 (as_seq h0 y))

let load_felem4 #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.load_felem4 x y
  | NI -> Hacl.Impl.Gf128.FieldNI.load_felem4 x y


inline_for_extraction noextract
val store_felem:
    #s:field_spec
  -> x:block
  -> y:felem s ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    as_seq h1 x == S.store_elem (feval h0 y))

let store_felem #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.store_felem x y
  | NI -> Hacl.Impl.Gf128.FieldNI.store_felem x y


inline_for_extraction noextract
val load_precompute_r:
    #s:field_spec
  -> pre:precomp s
  -> key:block ->
  Stack unit
  (requires fun h -> live h pre /\ live h key /\ disjoint pre key)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    get_r1 h1 pre == S.load_elem (as_seq h0 key) /\
    precomp_inv_t h1 pre)

let load_precompute_r #s pre key =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.load_precompute_r pre key
  | NI -> Hacl.Impl.Gf128.FieldNI.load_precompute_r pre key


inline_for_extraction noextract
val fadd:
    #s:field_spec
  -> x:felem s
  -> y:felem s ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fadd #S.gf128 (feval h0 x) (feval h0 y))

let fadd #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fadd x y
  | NI -> Hacl.Impl.Gf128.FieldNI.fadd x y


inline_for_extraction noextract
val fadd4:
    #s:field_spec
  -> x:felem4 s
  -> y:felem4 s ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == fadd4 (feval4 h0 x) (feval4 h0 y))

let fadd4 #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fadd4 x y
  | NI -> Hacl.Impl.Gf128.FieldNI.fadd4 x y


inline_for_extraction noextract
val fmul:
    #s:field_spec
  -> x:felem s
  -> y:felem s ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 y))

let fmul #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fmul x y
  | NI -> Hacl.Impl.Gf128.FieldNI.fmul x y


inline_for_extraction noextract
val fmul_pre:
    #s:field_spec
  -> x:felem s
  -> y:precomp s ->
  Stack unit
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\
    precomp_inv_t h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (get_r4 h0 y))

let fmul_pre #s x y =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fmul_pre x y
  | NI -> Hacl.Impl.Gf128.FieldNI.fmul_pre x y


inline_for_extraction noextract
val fmul_r4:
    #s:field_spec
  -> x:felem4 s
  -> y:precomp s ->
  Stack unit
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\
    precomp_inv_t h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == fmul4 (feval4 h0 x) (LSeq.create 4 (get_r4 h0 y)))

let fmul_r4 #s x pre =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fmul_r4 x pre
  | NI -> Hacl.Impl.Gf128.FieldNI.fmul_r4 x pre


inline_for_extraction noextract
val fadd_acc4:
    #s:field_spec
  -> x:felem4 s
  -> acc:felem s ->
  Stack unit
  (requires fun h ->
    live h x /\ live h acc /\ disjoint x acc)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Hacl.Spec.GF128.Vec.fadd4 (LSeq.create4 (feval h0 acc) zero zero zero) (feval4 h0 x))

let fadd_acc4 #s x acc =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.fadd_acc4 x acc
  | NI -> Hacl.Impl.Gf128.FieldNI.fadd_acc4 x acc


inline_for_extraction noextract
val normalize4:
    #s:field_spec
  -> acc:felem s
  -> x:felem4 s
  -> y:precomp s ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h x /\ live h y /\
    disjoint acc x /\ disjoint acc y /\ disjoint x y /\
    precomp_inv_t h y)
  (ensures  fun h0 _ h1 -> modifies2 x acc h0 h1 /\
    feval h1 acc == normalize4 (get_r4321 h0 y) (feval4 h0 x))

let normalize4 #s acc x pre =
  match s with
  | PreComp -> Hacl.Impl.Gf128.FieldPreComp.normalize4 acc x pre
  | NI -> Hacl.Impl.Gf128.FieldNI.normalize4 acc x pre
