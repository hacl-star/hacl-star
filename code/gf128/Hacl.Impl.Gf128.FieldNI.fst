module Hacl.Impl.Gf128.FieldNI

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec
module Lemmas = Hacl.Spec.GF128.Lemmas

include Hacl.Spec.Gf128.FieldNI

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let vec128_zero = vec_zero U128 1
noextract
let zero = GF.zero #S.gf128

let felem = lbuffer vec128 1ul
let felem4 = lbuffer vec128 4ul
let precomp = lbuffer vec128 4ul

let block = lbuffer uint8 16ul
let block4 = lbuffer uint8 64ul

unfold noextract
let op_String_Access #a #len = LSeq.index #a #len


noextract
let feval (h:mem) (f:felem) : GTot Vec.elem =
  let f = as_seq h f in
  (vec_v f.[0]).[0]


noextract
let feval4 (h:mem) (f:felem4) : GTot Vec.elem4 =
  let f = as_seq h f in
  let f0 = (vec_v f.[0]).[0] in
  let f1 = (vec_v f.[1]).[0] in
  let f2 = (vec_v f.[2]).[0] in
  let f3 = (vec_v f.[3]).[0] in
  create4 f0 f1 f2 f3


inline_for_extraction
val create_felem: unit ->
  StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 1 vec128_zero) /\
    feval h1 f == zero)

let create_felem () = create 1ul vec128_zero


inline_for_extraction
val copy_felem: f1:felem -> f2:felem ->
  Stack unit
  (requires fun h -> live h f1 /\ live h f2 /\ disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies1 f1 h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)

let copy_felem f1 f2 =
  let h0 = ST.get () in
  f1.(0ul) <- f2.(0ul);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 f1) (as_seq h0 f2)


inline_for_extraction
val felem_set_zero: f:felem ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies1 f h0 h1 /\
    feval h1 f == zero)

let felem_set_zero f = f.(0ul) <- vec128_zero


inline_for_extraction
val create_felem4: unit ->
  StackInline felem4
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 4 vec128_zero) /\
    feval4 h1 f == LSeq.create 4 zero)

let create_felem4 () =
  let f = create 4ul vec128_zero in
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 f) (LSeq.create 4 (u128 0));
  f


inline_for_extraction
val load_felem:
    x:felem
  -> y:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let load_felem x y =
  let h0 = ST.get () in
  x.(size 0) <- vec_load_be U128 1 y;
  BSeq.index_uints_from_bytes_be #U128 #SEC #1 (as_seq h0 y) 0


inline_for_extraction
val load_felem4:
    x:felem4
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.encode4 (as_seq h0 y))

let load_felem4 x y =
  let h0 = ST.get () in
  x.(size 0) <- vec_load_be U128 1 (sub y (size 0) (size 16));
  BSeq.index_uints_from_bytes_be #U128 #SEC #1 (LSeq.sub (as_seq h0 y) 0 16) 0;
  x.(size 1) <- vec_load_be U128 1 (sub y (size 16) (size 16));
  BSeq.index_uints_from_bytes_be #U128 #SEC #1 (LSeq.sub (as_seq h0 y) 16 16) 0;
  x.(size 2) <- vec_load_be U128 1 (sub y (size 32) (size 16));
  BSeq.index_uints_from_bytes_be #U128 #SEC #1 (LSeq.sub (as_seq h0 y) 32 16) 0;
  x.(size 3) <- vec_load_be U128 1 (sub y (size 48) (size 16));
  BSeq.index_uints_from_bytes_be #U128 #SEC #1 (LSeq.sub (as_seq h0 y) 48 16) 0


inline_for_extraction
val store_felem:
    x:lbuffer uint8 16ul
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    as_seq h1 x == S.store_elem (feval h0 y))

let store_felem x y =
  let h0 = ST.get () in
  vec_store_be x y.(size 0);
  let ul = vec_v (as_seq h0 y).[0] in
  FStar.Classical.forall_intro (BSeq.index_uints_to_bytes_be #U128 #SEC #1 ul);
  LSeq.eq_intro (BSeq.uints_to_bytes_be #U128 #SEC #1 ul) (BSeq.uint_to_bytes_be ul.[0])


val fadd:
    x: felem
  -> y: felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fadd #S.gf128 (feval h0 x) (feval h0 y))

[@CInline]
let fadd x y =
  x.(size 0) <- cl_add x.(size 0) y.(size 0)


val fadd4:
    x:felem4
  -> y:felem4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (feval4 h0 x) (feval4 h0 y))

[@CInline]
let fadd4 x y =
  let (x0, x1, x2, x3) = (x.(0ul), x.(1ul), x.(2ul), x.(3ul)) in
  let (y0, y1, y2, y3) = (y.(0ul), y.(1ul), y.(2ul), y.(3ul)) in
  let h0 = ST.get () in
  x.(size 0) <- cl_add x0 y0;
  x.(size 1) <- cl_add x1 y1;
  x.(size 2) <- cl_add x2 y2;
  x.(size 3) <- cl_add x3 y3;
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (feval4 h0 x) (feval4 h0 y))


val fmul:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 y))

[@ CInline]
let fmul x y =
  let xe = x.(size 0) in
  let ye = y.(size 0) in
  let (hi,lo) = clmul_wide xe ye in
  let lo = gf128_reduce hi lo in
  x.(size 0) <- lo;
  gf128_clmul_wide_reduce_lemma xe ye


val load_precompute_r:
    pre:precomp
  -> key:block ->
  Stack unit
  (requires fun h -> live h pre /\ live h key /\ disjoint pre key)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    (let r = S.load_elem (as_seq h0 key) in
    feval h1 (gsub pre 3ul 1ul) == r /\
    feval4 h1 pre == Vec.load_precompute_r r))

[@CInline]
let load_precompute_r pre key =
  let r4 = sub pre (size 0) (size 1) in
  let r3 = sub pre (size 1) (size 1) in
  let r2 = sub pre (size 2) (size 1) in
  let r1 = sub pre (size 3) (size 1) in

  load_felem r1 key;
  copy_felem r4 r1;
  copy_felem r3 r1;
  copy_felem r2 r1;
  fmul r2 r1;
  fmul r3 r2;
  fmul r4 r3


val fmul_pre:
    x:felem
  -> y:precomp ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 (gsub y 0ul 1ul)))

[@CInline]
let fmul_pre x pre =
  let r = sub pre (size 0) (size 1) in
  fmul x r


val fmul_r4:
    x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h -> live h x /\ live h pre /\ disjoint x pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    (let r4 = feval h0 (gsub pre 0ul 1ul) in
    feval4 h1 x == Vec.fmul4 (feval4 h0 x) (LSeq.create 4 r4)))

[@CInline]
let fmul_r4 x pre =
  let h0 = ST.get () in
  fmul (sub x (size 0) (size 1)) (sub pre (size 0) (size 1));
  fmul (sub x (size 1) (size 1)) (sub pre (size 0) (size 1));
  fmul (sub x (size 2) (size 1)) (sub pre (size 0) (size 1));
  fmul (sub x (size 3) (size 1)) (sub pre (size 0) (size 1));
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x)
    (Vec.fmul4 (feval4 h0 x) (LSeq.create 4 (feval h0 (gsub pre 0ul 1ul))))


inline_for_extraction noextract
val fadd_acc4:
    x:felem4
  -> acc:felem ->
  Stack unit
  (requires fun h ->
    live h x /\ live h acc /\ disjoint x acc)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (create4 (feval h0 acc) zero zero zero) (feval4 h0 x))

let fadd_acc4 x acc =
  let h0 = ST.get () in
  x.(0ul) <- cl_add acc.(0ul) x.(0ul);
  let h1 = ST.get () in
  Lemmas.add_identity (feval h0 (gsub x 1ul 1ul));
  Lemmas.add_identity (feval h0 (gsub x 2ul 1ul));
  Lemmas.add_identity (feval h0 (gsub x 3ul 1ul));
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (create4 (feval h0 acc) zero zero zero) (feval4 h0 x))


val normalize4:
    acc:felem
  -> x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h -> live h acc /\ live h x /\ live h pre)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    feval h1 acc == Vec.normalize4 (feval4 h0 pre) (feval4 h0 x))

[@CInline]
let normalize4 acc x pre =
  let x1 = x.(size 0) in
  let x2 = x.(size 1) in
  let x3 = x.(size 2) in
  let x4 = x.(size 3) in
  let y1 = pre.(size 0) in
  let y2 = pre.(size 1) in
  let y3 = pre.(size 2) in
  let y4 = pre.(size 3) in

  let (hi,lo) = clmul_wide4 x1 x2 x3 x4 y1 y2 y3 y4 in
  let lo = gf128_reduce hi lo in
  acc.(size 0) <- lo;
  gf128_clmul_wide4_reduce_lemma x1 x2 x3 x4 y1 y2 y3 y4
