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
module SPreComp = Hacl.Spec.Gf128.FieldPreComp
module Lemmas = Hacl.Spec.GF128.Lemmas


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

noextract
let zero = GF.zero #S.gf128

inline_for_extraction noextract
let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)

type felem = lbuffer uint64 2ul
type felem4 = lbuffer uint64 8ul
type table = lbuffer uint64 256ul
type precomp = lbuffer uint64 264ul // r4(8) + table(256)

type block = lbuffer uint8 16ul
type block4 = lbuffer uint8 64ul


unfold noextract
let op_String_Access #a #len = LSeq.index #a #len


noextract
let feval (h:mem) (f:felem) : GTot Vec.elem =
  let f = as_seq h f in
  uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0])


noextract
let feval4 (h:mem) (f:felem4) : GTot Vec.elem4 =
  let f = as_seq h f in
  let f0 = uint #U128 #SEC (v f.[1] * pow2 64 + v f.[0]) in
  let f1 = uint #U128 #SEC (v f.[3] * pow2 64 + v f.[2]) in
  let f2 = uint #U128 #SEC (v f.[5] * pow2 64 + v f.[4]) in
  let f3 = uint #U128 #SEC (v f.[7] * pow2 64 + v f.[6]) in
  Lib.IntVector.create4 f0 f1 f2 f3


noextract
let load_precomp_r_inv (h:mem) (pre:precomp) : Type0 =
  feval4 h (gsub pre 0ul 8ul) == Vec.load_precompute_r (feval h (gsub pre 6ul 2ul)) /\
  (let (y1, tab1) = SPreComp.precomp_s0 (as_seq h (gsub pre 0ul 2ul)) in
   let (y2, tab2) = SPreComp.precomp_s0 y1 in
   as_seq h (gsub pre 8ul 128ul) == tab1 /\ as_seq h (gsub pre 136ul 128ul) == tab2)


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
  (requires fun h -> live h f1 /\ live h f2 /\ eq_or_disjoint f1 f2)
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
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == S.encode (as_seq h0 y))

let load_felem x y =
  let h0 = ST.get () in
  assert (S.encode (as_seq h0 y) == BSeq.uint_from_bytes_be #U128 #SEC (as_seq h0 y));
  x.(size 1) <- uint_from_bytes_be #U64 (sub y (size 0) (size 8));
  x.(size 0) <- uint_from_bytes_be #U64 (sub y (size 8) (size 8));
  let h1 = ST.get () in
  assert (feval h1 x == uint #U128 #SEC (v (as_seq h1 x).[1] * pow2 64 + v (as_seq h1 x).[0]));
  BSeq.lemma_reveal_uint_to_bytes_be #U64 (LSeq.sub (as_seq h0 y) 0 8);
  BSeq.lemma_reveal_uint_to_bytes_be #U64 (LSeq.sub (as_seq h0 y) 8 8);
  assert (v (feval h1 x) == BSeq.nat_from_bytes_be (LSeq.sub (as_seq h0 y) 8 8) + pow2 64 * BSeq.nat_from_bytes_be (LSeq.sub (as_seq h0 y) 0 8));
  BSeq.nat_from_intseq_be_slice_lemma (as_seq h0 y) 8;
  assert (v (feval h1 x) == BSeq.nat_from_bytes_be (as_seq h0 y));
  BSeq.lemma_reveal_uint_to_bytes_be #U128 (as_seq h0 y);
  assert (v (feval h1 x) == v (S.encode (as_seq h0 y)))


inline_for_extraction
val load_felem4:
    x:felem4
  -> y:block4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ disjoint x y)
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
  load_felem x3 y3


val uints64_to_bytes_be_lemma: lo:uint64 -> hi:uint64 -> Lemma
  (LSeq.concat (BSeq.uint_to_bytes_be lo) (BSeq.uint_to_bytes_be hi) == BSeq.nat_to_bytes_be 16 (v lo * pow2 64 + v hi))
let uints64_to_bytes_be_lemma lo hi =
  let open Lib.ByteSequence in
  let lp = nat_to_bytes_be #SEC 16 (v lo * pow2 64 + v hi) in
  let rp = LSeq.concat (uint_to_bytes_be lo) (uint_to_bytes_be hi) in
  assert (nat_from_bytes_be lp == v lo * pow2 64 + v hi);
  Seq.append_slices (uint_to_bytes_be lo) (uint_to_bytes_be hi);
  nat_from_intseq_be_slice_lemma #U8 #SEC #16 rp 8;
  assert (nat_from_bytes_be rp == nat_from_bytes_be (LSeq.sub rp 8 8) + pow2 (8 * 8) * nat_from_bytes_be (LSeq.sub rp 0 8));
  assert (nat_from_bytes_be rp == nat_from_bytes_be (uint_to_bytes_be hi) + pow2 64 * nat_from_bytes_be (uint_to_bytes_be lo));
  lemma_uint_to_bytes_be_preserves_value lo;
  lemma_uint_to_bytes_be_preserves_value hi;
  nat_from_intseq_be_inj lp rp


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
  assert (S.store_elem (feval h0 y) == BSeq.uint_to_bytes_be #U128 #SEC (feval h0 y));
  let h0 = ST.get () in
  let r0 = y.(1ul) in
  let r1 = y.(0ul) in
  update_sub_f h0 x 0ul 8ul
    (fun h -> BSeq.uint_to_bytes_be #U64 r0)
    (fun _ -> uint_to_bytes_be (sub x 0ul 8ul) r0);
  let h1 = ST.get () in
  update_sub_f h1 x 8ul 8ul
    (fun h -> BSeq.uint_to_bytes_be #U64 r1)
    (fun _ -> uint_to_bytes_be (sub x 8ul 8ul) r1);
  let h2 = ST.get () in
  LSeq.eq_intro (LSeq.sub (as_seq h2 x) 0 8) (BSeq.uint_to_bytes_be #U64 r0);
  LSeq.lemma_concat2 8 (BSeq.uint_to_bytes_be #U64 r0) 8 (BSeq.uint_to_bytes_be #U64 r1) (as_seq h2 x);
  uints64_to_bytes_be_lemma r0 r1;
  assert (as_seq h2 x == BSeq.nat_to_bytes_be 16 (v (feval h0 y)));
  BSeq.lemma_nat_to_from_bytes_be_preserves_value (as_seq h2 x) 16 (v (feval h0 y));
  BSeq.lemma_uint_to_bytes_be_preserves_value (feval h0 y);
  BSeq.nat_from_intseq_be_inj (as_seq h2 x) (BSeq.uint_to_bytes_be #U128 #SEC (feval h0 y))


inline_for_extraction
val fadd:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fadd #S.gf128 (feval h0 x) (feval h0 y))

let fadd x y =
  let h0 = ST.get () in
  x.(size 0) <- x.(size 0) ^. y.(size 0);
  x.(size 1) <- x.(size 1) ^. y.(size 1);
  SPreComp.fadd_lemma (as_seq h0 x) (as_seq h0 y)


inline_for_extraction
val fadd4:
    x:felem4
  -> y:felem4 ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
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

  let h0 = ST.get () in
  fadd x0 y0;
  fadd x1 y1;
  fadd x2 y2;
  fadd x3 y3;
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (feval4 h0 x) (feval4 h0 y))


inline_for_extraction noextract
val mask_add0:
    x:uint64
  -> y:felem
  -> res:felem
  -> i:size_t{v i < 64} ->
  Stack unit
  (requires fun h -> live h y /\ live h res /\ disjoint y res)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == SPreComp.mask_add0 x (as_seq h0 y) (as_seq h0 res) (v i))

let mask_add0 x y res i =
  let h0 = ST.get () in
  let m = bit_mask64 (x >>. (63ul -. i)) in
  res.(0ul) <- res.(0ul) ^. (y.(0ul) &. m);
  res.(1ul) <- res.(1ul) ^. (y.(1ul) &. m);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 res) (SPreComp.mask_add0 x (as_seq h0 y) (as_seq h0 res) (v i))


inline_for_extraction noextract
val mask_shift_right_mod: y:felem ->
  Stack unit
  (requires fun h -> live h y)
  (ensures  fun h0 _ h1 -> modifies (loc y) h0 h1 /\
    as_seq h1 y == SPreComp.mask_shift_right_mod (as_seq h0 y))

let mask_shift_right_mod y =
  let h0 = ST.get () in
  let m = bit_mask64 y.(0ul) in
  y.(0ul) <- (y.(0ul) >>. 1ul) |. (y.(1ul) <<. 63ul);
  y.(1ul) <- (y.(1ul) >>. 1ul) ^. (u64 0xE100000000000000 &. m);
  let h1 = ST.get () in
  LSeq.eq_intro (as_seq h1 y) (SPreComp.mask_shift_right_mod_optimized (as_seq h0 y));
  SPreComp.mask_shift_right_mod_optimized_lemma (as_seq h0 y)


inline_for_extraction noextract
val fmul_f0:
    x:uint64
  -> i:size_t{v i < 64}
  -> res:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h res /\ live h y /\ disjoint y res)
  (ensures  fun h0 _ h1 -> modifies2 res y h0 h1 /\
    (as_seq h1 res, as_seq h1 y) == SPreComp.fmul_be_s_f0 x (v i) (as_seq h0 res, as_seq h0 y))

let fmul_f0 x i res y =
  mask_add0 x y res i;
  mask_shift_right_mod y


val fmul:
    x:felem
  -> y:felem ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ eq_or_disjoint x y)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 y))

[@CInline]
let fmul x y =
  push_frame();
  let res = create 2ul (u64 0) in
  let y_ = create 2ul (u64 0) in
  copy_felem y_ y;

  let h0 = ST.get () in
  [@inline_let]
  let spec1 h = SPreComp.fmul_be_s_f0 (LSeq.index (as_seq h x) 1) in
  loop2 h0 64ul res y_ spec1
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec1 h0) (as_seq h0 res, as_seq h0 y_) (v i);
    fmul_f0 x.(1ul) i res y_);

  let h1 = ST.get () in
  [@inline_let]
  let spec0 h = SPreComp.fmul_be_s_f0 (LSeq.index (as_seq h x) 0) in
  loop2 h1 64ul res y_ spec0
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec0 h0) (as_seq h1 res, as_seq h1 y_) (v i);
    fmul_f0 x.(0ul) i res y_);
  let h2 = ST.get () in
  assert (as_seq h2 res == SPreComp.fmul_be_s (as_seq h0 x) (as_seq h0 y));
  copy_felem x res;
  SPreComp.fmul_be_lemma (as_seq h0 x) (as_seq h0 y);
  SPreComp.fmul_be_one_loop_lemma (as_seq h0 x) (as_seq h0 y);
  pop_frame()


inline_for_extraction noextract
let table1 = lbuffer uint64 128ul

inline_for_extraction
val precomp_f:
    i:size_t{v i < 64}
  -> sh:felem
  -> pre:table1 ->
  Stack unit
  (requires fun h -> live h pre /\ live h sh /\ disjoint pre sh)
  (ensures  fun h0 _ h1 -> modifies2 pre sh h0 h1 /\
    (as_seq h1 sh, as_seq h1 pre) == SPreComp.precomp_s_f0 (v i) (as_seq h0 sh, as_seq h0 pre))

let precomp_f i sh pre =
  update_sub pre (2ul *! i) 2ul sh;
  mask_shift_right_mod sh


val prepare:
    pre:table
  -> r:felem ->
  Stack unit
  (requires fun h -> live h pre /\ live h r /\ disjoint pre r)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    (let (y1, tab1) = SPreComp.precomp_s0 (as_seq h0 r) in
     let (y2, tab2) = SPreComp.precomp_s0 y1 in
     as_seq h1 (gsub pre 0ul 128ul) == tab1 /\
     as_seq h1 (gsub pre 128ul 128ul) == tab2))

[@CInline]
let prepare pre r =
  push_frame();
  memset pre (u64 0) 256ul; //FIX: this shouldn't be needed
  let sh = create 2ul (u64 0) in
  copy_felem sh r;

  let pre1 = sub pre 0ul 128ul in
  let pre2 = sub pre 128ul 128ul in

  let h0 = ST.get() in
  LSeq.eq_intro (as_seq h0 pre1) (LSeq.create 128 (u64 0));
  LSeq.eq_intro (as_seq h0 pre2) (LSeq.create 128 (u64 0));

  [@inline_let]
  let spec h = SPreComp.precomp_s_f0 in
  loop2 h0 64ul sh pre1 spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec h0) (as_seq h0 sh, as_seq h0 pre1) (v i);
    precomp_f i sh pre1);

  let h1 = ST.get() in
  Seq.lemma_split (as_seq h1 pre) 128;

  loop2 h1 64ul sh pre2 spec
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec h1) (as_seq h1 sh, as_seq h1 pre2) (v i);
    precomp_f i sh pre2);
  let h2 = ST.get () in
  Seq.lemma_split (as_seq h2 pre) 128;
  pop_frame()


val load_precompute_r:
    pre:precomp
  -> key:block ->
  Stack unit
  (requires fun h -> live h pre /\ live h key /\ disjoint pre key)
  (ensures  fun h0 _ h1 -> modifies1 pre h0 h1 /\
    feval h1 (gsub pre 6ul 2ul) == S.load_elem (as_seq h0 key) /\
    load_precomp_r_inv h1 pre)

[@CInline]
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


inline_for_extraction
val fmul_pre_f:
    x:uint64
  -> tab:table1
  -> i:size_t{v i < 64}
  -> tmp:felem ->
  Stack unit
  (requires fun h -> live h tmp /\ live h tab /\ disjoint tmp tab)
  (ensures  fun h0 _ h1 -> modifies1 tmp h0 h1 /\
    as_seq h1 tmp == SPreComp.fmul_pre_s_f0 x (as_seq h0 tab) (v i) (as_seq h0 tmp))

let fmul_pre_f x tab i tmp =
  mask_add0 x (sub tab (2ul *! i) 2ul) tmp i


val fmul_pre:
    x:felem
  -> pre:precomp ->
  Stack unit
  (requires fun h ->
    live h x /\ live h pre /\ disjoint x pre /\
    load_precomp_r_inv h pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval h1 x == GF.fmul_be #S.gf128 (feval h0 x) (feval h0 (gsub pre 0ul 2ul)))

[@CInline]
let fmul_pre x pre =
  push_frame();
  let tab = sub pre (size 8) (size 256) in
  let tmp = create 2ul (u64 0) in

  let h0 = ST.get() in
  [@inline_let]
  let spec1 h = SPreComp.fmul_pre_s_f0 (LSeq.index (as_seq h x) 1) (LSeq.sub (as_seq h tab) 0 128) in
  loop1 h0 64ul tmp spec1
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec1 h0) (as_seq h0 tmp) (v i);
    fmul_pre_f x.(1ul) (sub tab 0ul 128ul) i tmp);

  let h1 = ST.get () in
  [@inline_let]
  let spec0 h = SPreComp.fmul_pre_s_f0 (LSeq.index (as_seq h x) 0) (LSeq.sub (as_seq h tab) 128 128) in
  loop1 h1 64ul tmp spec0
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 64 (spec0 h1) (as_seq h1 tmp) (v i);
    fmul_pre_f x.(0ul) (sub tab 128ul 128ul) i tmp);
  copy_felem x tmp;
  SPreComp.fmul_pre_lemma (as_seq h0 x) (as_seq h0 (gsub pre 0ul 2ul));
  SPreComp.fmul_be_one_loop_lemma (as_seq h0 x) (as_seq h0 (gsub pre 0ul 2ul));
  pop_frame()


val fmul_r4:
    x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h ->
    live h x /\ live h pre /\ disjoint x pre /\
    load_precomp_r_inv h pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    (let r4 = feval h0 (gsub pre 0ul 2ul) in
    feval4 h1 x == Vec.fmul4 (feval4 h0 x) (LSeq.create 4 r4)))

[@CInline]
let fmul_r4 x pre =
  let h0 = ST.get () in
  fmul_pre (sub x (size 0) (size 2)) pre;
  fmul_pre (sub x (size 2) (size 2)) pre;
  fmul_pre (sub x (size 4) (size 2)) pre;
  fmul_pre (sub x (size 6) (size 2)) pre;
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x)
    (Vec.fmul4 (feval4 h0 x) (LSeq.create 4 (feval h0 (gsub pre 0ul 2ul))))


inline_for_extraction noextract
val fmul4:
    x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h ->
    live h x /\ live h pre /\ disjoint x pre /\
    load_precomp_r_inv h pre)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fmul4 (feval4 h0 x) (feval4 h0 (gsub pre 0ul 8ul)))

let fmul4 x pre =
  let h0 = ST.get () in
  fmul_pre (sub x 0ul 2ul) pre;
  fmul (sub x 2ul 2ul) (sub pre 2ul 2ul);
  fmul (sub x 4ul 2ul) (sub pre 4ul 2ul);
  fmul (sub x 6ul 2ul) (sub pre 6ul 2ul);
  let h1 = ST.get () in
  LSeq.eq_intro (feval4 h1 x)
    (Vec.fmul4 (feval4 h0 x) (feval4 h0 (gsub pre 0ul 8ul)))


inline_for_extraction noextract
val fadd_acc4:
    x:felem4
  -> acc:felem ->
  Stack unit
  (requires fun h ->
    live h x /\ live h acc /\ disjoint x acc)
  (ensures  fun h0 _ h1 -> modifies1 x h0 h1 /\
    feval4 h1 x == Vec.fadd4 (Lib.IntVector.create4 (feval h0 acc) zero zero zero) (feval4 h0 x))

let fadd_acc4 x acc =
  let h0 = ST.get () in
  fadd (sub x 0ul 2ul) acc;
  let h1 = ST.get () in
  assert (feval h1 (gsub x 0ul 2ul) == GF.fadd #S.gf128 (feval h0 (gsub x 0ul 2ul)) (feval h0 acc));
  Lemmas.add_commutativity (feval h0 (gsub x 0ul 2ul)) (feval h0 acc);
  Lemmas.add_identity (feval h0 (gsub x 2ul 2ul));
  Lemmas.add_identity (feval h0 (gsub x 4ul 2ul));
  Lemmas.add_identity (feval h0 (gsub x 6ul 2ul));
  LSeq.eq_intro (feval4 h1 x) (Vec.fadd4 (Lib.IntVector.create4 (feval h0 acc) zero zero zero) (feval4 h0 x))


#set-options "--z3rlimit 100"

val normalize4:
    acc:felem
  -> x:felem4
  -> pre:precomp ->
  Stack unit
  (requires fun h ->
    live h acc /\ live h x /\ live h pre /\
    disjoint acc pre /\ disjoint acc x /\ disjoint x pre /\
    load_precomp_r_inv h pre)
  (ensures  fun h0 _ h1 -> modifies2 x acc h0 h1 /\
    feval h1 acc == Vec.normalize4 (feval4 h0 (gsub pre 0ul 8ul)) (feval4 h0 x))

[@CInline]
let normalize4 acc x pre =
  let x1 = sub x (size 0) (size 2) in
  let x2 = sub x (size 2) (size 2) in
  let x3 = sub x (size 4) (size 2) in
  let x4 = sub x (size 6) (size 2) in

  fmul4 x pre;

  copy_felem acc x1;
  fadd acc x2;
  fadd acc x3;
  fadd acc x4
