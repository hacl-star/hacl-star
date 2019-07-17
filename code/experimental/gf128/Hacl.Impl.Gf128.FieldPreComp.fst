module Hacl.Impl.Gf128.FieldPreComp

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec


#set-options "--z3rlimit 25"

noextract
let zero = GF.zero #S.gf128

inline_for_extraction noextract
let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)

type felem = lbuffer uint64 2ul
type felem4 = lbuffer uint64 8ul
type table = lbuffer uint64 256ul // r4(8) + table(256)
type precomp = lbuffer uint64 264ul // r4(8) + table(256)

type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul


unfold noextract
let op_String_Access #a #len = LSeq.index #a #len

noextract
let feval (h:mem) (f:felem) : GTot Vec.elem =
  let f = as_seq h f in
  nat_to_uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0])


noextract
let feval4 (h:mem) (f:felem4) : GTot Vec.elem4 =
  let f = as_seq h f in
  let f0 = nat_to_uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0]) in
  let f1 = nat_to_uint #U128 #SEC (v f.[3] * pow2 64 + v f.[2]) in
  let f2 = nat_to_uint #U128 #SEC (v f.[5] * pow2 64 + v f.[4]) in
  let f3 = nat_to_uint #U128 #SEC (v f.[7] * pow2 64 + v f.[6]) in
  Lib.IntVector.create4 f0 f1 f2 f3


inline_for_extraction
val create_felem: unit ->
  StackInline felem
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 2 (u64 0)) /\
    feval h1 f == zero)

let create_felem () = create 2ul (u64 0)


inline_for_extraction
val copy_felem: f1:felem -> f2:felem ->
  Stack unit
  (requires fun h -> live h f1 /\ live h f2 /\ disjoint f1 f2)
  (ensures  fun h0 _ h1 -> modifies1 f1 h0 h1 /\
    as_seq h1 f1 == as_seq h0 f2)

let copy_felem f1 f2 =
  let h0 = ST.get () in
  f1.(0ul) <- f2.(0ul);
  f1.(1ul) <- f2.(1ul);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 f1) (as_seq h0 f2)


inline_for_extraction
val felem_set_zero: f:felem ->
  Stack unit
  (requires fun h -> live h f)
  (ensures  fun h0 _ h1 -> modifies1 f h0 h1 /\
    feval h1 f == zero)

let felem_set_zero f =
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0


inline_for_extraction
val create_felem4: unit ->
  StackInline felem4
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 8 (u64 0)) /\
    feval4 h1 f == LSeq.create 4 zero)

let create_felem4 () =
  let f = create 8ul (u64 0) in
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 f) (LSeq.create 4 (u128 0));
  f


inline_for_extraction
val load_felem:
    x:felem
  -> y:block ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let load_felem x y =
  x.(size 1) <- uint_from_bytes_be #U64 (sub y (size 0) (size 8));
  x.(size 0) <- uint_from_bytes_be #U64 (sub y (size 8) (size 8));
  admit()


inline_for_extraction
val load_felem4:
    x:felem4
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.encode4 (as_seq h0 y))

let load_felem4 x y =
  let x0 = sub x (size 0) (size 2) in
  let y0 = sub y (size 0) (size 16) in
  let x1 = sub x (size 2) (size 2) in
  let y1 = sub y (size 16) (size 16) in
  let x2 = sub x (size 4) (size 2) in
  let y2 = sub y (size 32) (size 16) in
  let x3 = sub x (size 6) (size 2) in
  let y3 = sub y (size 48) (size 16) in
  load_felem x0 y0;
  load_felem x1 y1;
  load_felem x2 y2;
  load_felem x3 y3; admit()


inline_for_extraction
val store_felem:
    x:lbuffer uint8 16ul
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    as_seq h1 x == S.store_elem (feval h0 y))

let store_felem x y =
  uint_to_bytes_be #U64 (sub x (size 0) (size 8)) y.(size 1);
  uint_to_bytes_be #U64 (sub x (size 8) (size 8)) y.(size 0); admit()


inline_for_extraction
val fadd:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fadd #S.gf128 (feval h0 x) (feval h0 y))

let fadd x y =
  x.(size 0) <- x.(size 0) ^. y.(size 0);
  x.(size 1) <- x.(size 1) ^. y.(size 1); admit()


inline_for_extraction
val fadd4:
    x:felem4
  -> y:felem4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (feval4 h0 x) (feval4 h0 y))

let fadd4 x y =
  let x0 = sub x (size 0) (size 2) in
  let y0 = sub y (size 0) (size 2) in
  let x1 = sub x (size 2) (size 2) in
  let y1 = sub y (size 2) (size 2) in
  let x2 = sub x (size 4) (size 2) in
  let y2 = sub y (size 4) (size 2) in
  let x3 = sub x (size 6) (size 2) in
  let y3 = sub y (size 6) (size 2) in

  fadd x0 y0;
  fadd x1 y1;
  fadd x2 y2;
  fadd x3 y3; admit()


[@CInline]
val fmul:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 y))

let fmul x y =
  push_frame();
  let tmp = create 2ul (u64 0) in
  let sh = create 2ul (u64 0) in
  sh.(size 0) <- y.(size 0);
  sh.(size 1) <- y.(size 1);
  let h0 = ST.get() in
  loop_nospec2 #h0 (size 64) tmp sh
    (fun i ->
      let s0 = sh.(size 0) in
      let s1 = sh.(size 1) in
      let m = bit_mask64 (x.(size 1) >>. (size 63 -. i)) in
      tmp.(size 0) <- tmp.(size 0) ^. (m &. s0);
      tmp.(size 1) <- tmp.(size 1) ^. (m &. s1);
      let s = bit_mask64 s0 in
      sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
      sh.(size 1) <- (s1 >>. size 1) ^. (s &. u64 0xE100000000000000));
  let h1 = ST.get () in
  loop_nospec2 #h1 (size 64) tmp sh
    (fun i ->
	   let s0 = sh.(size 0) in
      let s1 = sh.(size 1) in
      let m = bit_mask64 (x.(size 0) >>. (size 63 -. i)) in
      tmp.(size 0) <- tmp.(size 0) ^. (m &. s0);
      tmp.(size 1) <- tmp.(size 1) ^. (m &. s1);
      let s = bit_mask64 s0 in
      sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
      sh.(size 1) <- (s1 >>. size 1) ^. (s &. u64 0xE100000000000000));
  x.(size 0) <- tmp.(size 0);
  x.(size 1) <- tmp.(size 1);
  pop_frame(); admit()


[@CInline]
val prepare:
    pre:table
  -> r:felem ->
  Stack unit
  (requires fun h -> live h pre /\ live h r)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1)

let prepare pre r =
  push_frame();
  let sh = create 2ul (u64 0) in
  sh.(size 0) <- r.(size 0);
  sh.(size 1) <- r.(size 1);
  let h0 = ST.get () in
  loop_nospec2 #h0 (size 128) pre sh (fun i ->
	 let s0 = sh.(size 0) in
	 let s1 = sh.(size 1) in
	 pre.(i *. size 2) <- s0;
	 pre.(size 1 +. i *. size 2) <- s1;
	 let m = bit_mask64 s0 in
    sh.(size 0) <- (s0 >>. size 1) |. (s1 <<. size 63);
    sh.(size 1) <- (s1 >>. size 1) ^. (m &. u64 0xE100000000000000));
  pop_frame()


[@CInline]
val load_precompute_r:
    pre:precomp
  -> key:block ->
  Stack unit
  (requires fun h -> live h pre /\ live h key)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    (let r = S.load_elem (as_seq h0 key) in
    feval h1 (gsub pre 6ul 2ul) == r /\
    feval4 h1 (gsub pre 0ul 8ul) == Vec.load_precompute_r r))

let load_precompute_r pre key =
  let r4321 = sub pre (size 0) (size 8) in
  let r1 = sub r4321 (size 6) (size 2) in
  let r2 = sub r4321 (size 4) (size 2) in
  let r3 = sub r4321 (size 2) (size 2) in
  let r4 = sub r4321 (size 0) (size 2) in

  let table = sub pre (size 8) (size 256) in
  load_felem r1 key;
  copy_felem r4 r1;
  copy_felem r3 r1;
  copy_felem r2 r1;

  fmul r2 r1;
  fmul r3 r2;
  fmul r4 r3;
  prepare table r4


[@CInline]
val fmul_pre:
    x:felem
  -> pre:precomp ->
  Stack unit
  (requires fun h -> live h x /\ live h pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 (gsub pre 0ul 2ul)))

let fmul_pre x pre =
  push_frame();
  let tab = sub pre (size 8) (size 256) in
  let tmp = create 2ul (u64 0) in
  let h0 = ST.get() in
  loop_nospec #h0 (size 64) tmp
    (fun i ->
	   let m = bit_mask64 (x.(size 1) >>. (size 63 -. i)) in
	   tmp.(size 0) <- tmp.(size 0) ^. (m &. tab.(i *. size 2));
	   tmp.(size 1) <- tmp.(size 1) ^. (m &. tab.(size 1 +. i *. size 2)));
  let h1 = ST.get () in
  loop_nospec #h1 (size 64) tmp
    (fun i ->
	   let m = bit_mask64 (x.(size 0) >>. (size 63 -. i)) in
	   tmp.(size 0) <- tmp.(size 0) ^. (m &. tab.(size 128 +. i *. size 2));
	   tmp.(size 1) <- tmp.(size 1) ^. (m &. tab.(size 129 +. i *. size 2)));
  x.(size 0) <- tmp.(size 0);
  x.(size 1) <- tmp.(size 1);
  pop_frame(); admit()


[@CInline]
val fmul_r4:
    x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h -> live h x /\ live h pre /\ disjoint x pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    (let r4 = feval h0 (gsub pre 0ul 2ul) in
    feval4 h1 x == Vec.fmul4 (feval4 h0 x) (LSeq.create 4 r4)))

let fmul_r4 x pre =
  fmul_pre (sub x (size 0) (size 2)) pre;
  fmul_pre (sub x (size 2) (size 2)) pre;
  fmul_pre (sub x (size 4) (size 2)) pre;
  fmul_pre (sub x (size 6) (size 2)) pre; admit()

[@CInline]
val normalize4:
    acc:felem
  -> x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h -> live h acc /\ live h x /\ live h pre)
  (ensures  fun h0 _ h1 -> modifies1 acc h0 h1 /\
    (let x = Vec.fadd4 (Lib.IntVector.create4 (feval h0 acc) GF.zero GF.zero GF.zero) (feval4 h0 x) in
    feval h1 acc == Vec.normalize4 x (feval4 h0 (gsub pre 0ul 8ul))))

let normalize4 acc x pre =
  let x1 = sub x (size 0) (size 2) in
  let x2 = sub x (size 2) (size 2) in
  let x3 = sub x (size 4) (size 2) in
  let x4 = sub x (size 6) (size 2) in

  let r4 = sub pre (size 0) (size 2) in
  let r3 = sub pre (size 2) (size 2) in
  let r2 = sub pre (size 4) (size 2) in
  let r1 = sub pre (size 6) (size 2) in

  fadd acc x1;
  fmul_pre acc pre;
  fmul x2 r3;
  fmul x3 r2;
  fmul x4 r1;
  fadd acc x2;
  fadd acc x3;
  fadd acc x4; admit()
