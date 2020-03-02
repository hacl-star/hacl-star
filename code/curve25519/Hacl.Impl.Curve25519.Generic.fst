module Hacl.Impl.Curve25519.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields

include Hacl.Impl.Curve25519.Finv
include Hacl.Impl.Curve25519.AddAndDouble

module ST = FStar.HyperStack.ST
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

module C = Hacl.Impl.Curve25519.Fields.Core

module S = Spec.Curve25519
module M = Hacl.Spec.Curve25519.AddAndDouble
module Lemmas = Hacl.Spec.Curve25519.Field64.Lemmas

friend Lib.LoopCombinators

#reset-options "--z3rlimit 200 --max_fuel 2 --using_facts_from '* -FStar.Seq -Hacl.Spec.*' --record_options"
//#set-options "--debug Hacl.Impl.Curve25519.Generic --debug_level ExtractNorm"

inline_for_extraction noextract
let scalar = lbuffer uint8 32ul

inline_for_extraction noextract
val scalar_bit:
    s:scalar
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == S.ith_bit (as_seq h0 s) (v n) /\ v r <= 1)
let scalar_bit s n =
  let h0 = ST.get () in
  mod_mask_lemma ((LSeq.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)

inline_for_extraction noextract
val decode_point:
    #s:field_spec
  -> o:point s
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      state_inv_t h1 (get_x o) /\ state_inv_t h1 (get_z o) /\
      fget_x h1 o == S.decodePoint (as_seq h0 i) /\ fget_z h1 o == 1)
[@ Meta.Attribute.specialize ]
let decode_point #s o i =
  push_frame();
  let tmp = create 4ul (u64 0) in
  let h0 = ST.get () in
  uints_from_bytes_le #U64 tmp i;
  let h1 = ST.get () in
  BSeq.uints_from_bytes_le_nat_lemma #U64 #SEC #4 (as_seq h0 i);
  assert (BSeq.nat_from_intseq_le (as_seq h1 tmp) == BSeq.nat_from_bytes_le (as_seq h0 i));
  let tmp3 = tmp.(3ul) in
  tmp.(3ul) <- tmp3 &. u64 0x7fffffffffffffff;
  mod_mask_lemma tmp3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  assert (v (mod_mask #U64 #SEC 63ul) == v (u64 0x7fffffffffffffff));
  let h2 = ST.get () in
  assert (v (LSeq.index (as_seq h2 tmp) 3) < pow2 63);
  Lemmas.lemma_felem64_mod255 (as_seq h1 tmp);
  assert (BSeq.nat_from_intseq_le (as_seq h2 tmp) == BSeq.nat_from_bytes_le (as_seq h0 i) % pow2 255);
  let x : felem s = sub o 0ul (nlimb s) in
  let z : felem s = sub o (nlimb s) (nlimb s) in
  set_one z;
  load_felem x tmp;
  pop_frame()



val encode_point:
    #s:field_spec
  -> o:lbuffer uint8 32ul
  -> i:point s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ disjoint o i /\
      state_inv_t h0 (get_x i) /\ state_inv_t h0 (get_z i))
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.encodePoint (fget_x h0 i, fget_z h0 i))
[@ Meta.Attribute.specialize ]
let encode_point #s o i =
  push_frame();
  let x : felem s = sub i 0ul (nlimb s) in
  let z : felem s = sub i (nlimb s) (nlimb s) in
  let tmp = create_felem s in
  let u64s = create 4ul (u64 0) in
  let tmp_w = create (2ul `FStar.UInt32.mul` ((nwide s) <: FStar.UInt32.t)) (wide_zero s) in
  let h0 = ST.get () in
  finv tmp z tmp_w;
  fmul tmp tmp x tmp_w;
  let h1 = ST.get () in
  assert (feval h1 tmp == S.fmul (S.fpow (feval h0 z) (pow2 255 - 21)) (feval h0 x));
  assert (feval h1 tmp == S.fmul (feval h0 x) (S.fpow (feval h0 z) (pow2 255 - 21)));
  store_felem u64s tmp;
  let h2 = ST.get () in
  assert (as_seq h2 u64s == BSeq.nat_to_intseq_le 4 (feval h1 tmp));
  uints_to_bytes_le #U64 4ul o u64s;
  let h3 = ST.get () in
  BSeq.uints_to_bytes_le_nat_lemma #U64 #SEC 4 (feval h1 tmp);
  assert (as_seq h3 o == BSeq.nat_to_bytes_le 32 (feval h1 tmp));
  pop_frame()

// TODO: why re-define the signature here?
val cswap2:
    #s:field_spec
  -> bit:uint64{v bit <= 1}
  -> p1:felem2 s
  -> p2:felem2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 p1 /\ live h0 p2 /\ disjoint p1 p2)
    (ensures  fun h0 _ h1 ->
      modifies (loc p1 |+| loc p2) h0 h1 /\
      (v bit == 1 ==> as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1) /\
      (v bit == 0 ==> as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2) /\
      (fget_xz h1 p1, fget_xz h1 p2) == S.cswap2 bit (fget_xz h0 p1) (fget_xz h0 p2))
[@ Meta.Attribute.inline_ ]
let cswap2 #s bit p0 p1 =
  C.cswap2 #s bit p0 p1

#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 3"

val ladder_step:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> i:size_t{v i < 251}
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
      v (LSeq.index (as_seq h0 bit) 0) <= 1 /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
      let (p0, p1, b) = S.ladder_step (as_seq h0 k) (fget_xz h0 q) (v i)
	(fget_xz h0 nq, fget_xz h0 nq_p1, LSeq.index (as_seq h0 bit) 0) in
      p0 == fget_xz h1 nq /\ p1 == fget_xz h1 nq_p1 /\
      b == LSeq.index (as_seq h1 bit) 0 /\
      v (LSeq.index (as_seq h1 bit) 0) <= 1 /\
      state_inv_t h1 (get_x q) /\ state_inv_t h1 (get_z q) /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1)))
[@ Meta.Attribute.inline_ ]
let ladder_step #s k q i p01_tmp1_swap tmp2 =
  let p01_tmp1 = sub p01_tmp1_swap 0ul (8ul *! nlimb s) in
  let swap : lbuffer uint64 1ul = sub p01_tmp1_swap (8ul *! nlimb s) 1ul in
  let nq = sub p01_tmp1 0ul (2ul *! nlimb s) in
  let nq_p1 = sub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) in

  assert (gsub p01_tmp1_swap 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  assert (gsub p01_tmp1 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  assert (gsub p01_tmp1_swap 0ul (8ul *! nlimb s) == p01_tmp1);
  assert (gsub p01_tmp1_swap (8ul *! nlimb s) 1ul == swap);

  let h0 = ST.get () in
  let bit = scalar_bit k (253ul -. i) in
  assert (v bit == v (S.ith_bit (as_seq h0 k) (253 - v i)));
  let sw = swap.(0ul) ^. bit in
  logxor_lemma1 (LSeq.index (as_seq h0 swap) 0) bit;
  cswap2 #s sw nq nq_p1;
  point_add_and_double #s q p01_tmp1 tmp2;
  swap.(0ul) <- bit

#set-options "--max_fuel 2"

val ladder_step_loop:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
      v (LSeq.index (as_seq h0 bit) 0) <= 1 /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
      let (p0, p1, b) =
	Lib.LoopCombinators.repeati 251
	(S.ladder_step (as_seq h0 k) (fget_xz h0 q))
	(fget_xz h0 nq, fget_xz h0 nq_p1, LSeq.index (as_seq h0 bit) 0) in
      p0 == fget_xz h1 nq /\ p1 == fget_xz h1 nq_p1 /\ b == LSeq.index (as_seq h1 bit) 0 /\
      v (LSeq.index (as_seq h1 bit) 0) <= 1 /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1)))
[@ Meta.Attribute.inline_ ]
let ladder_step_loop #s k q p01_tmp1_swap tmp2 =
  let h0 = ST.get () in

  [@ inline_let]
  let spec_fh h0 =
    S.ladder_step (as_seq h0 k) (fget_x h0 q, fget_z h0 q) in

  [@ inline_let]
  let acc h : GTot (tuple3 S.proj_point S.proj_point uint64) =
    let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
    let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
    let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
    (fget_xz h nq, fget_xz h nq_p1, LSeq.index (as_seq h bit) 0) in

  [@ inline_let]
  let inv h (i:nat{i <= 251}) =
    let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
    let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
    let bit : lbuffer uint64 1ul = gsub p01_tmp1_swap (8ul *! nlimb s) 1ul in
    modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h /\
    v (LSeq.index (as_seq h bit) 0) <= 1 /\
    state_inv_t h (get_x q) /\ state_inv_t h (get_z q) /\
    state_inv_t h (get_x nq) /\ state_inv_t h (get_z nq) /\
    state_inv_t h (get_x nq_p1) /\ state_inv_t h (get_z nq_p1) /\
    acc h == Lib.LoopCombinators.repeati i (spec_fh h0) (acc h0) in

  Lib.Loops.for 0ul 251ul inv
    (fun i ->
      Lib.LoopCombinators.unfold_repeati 251 (spec_fh h0) (acc h0) (v i);
      ladder_step #s k q i p01_tmp1_swap tmp2)

#set-options "--max_fuel 0 --z3rlimit 150"

val ladder0_:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      fget_xz h1 nq ==
      M.montgomery_ladder1_0 (as_seq h0 k) (fget_xz h0 q) (fget_xz h0 nq) (fget_xz h0 nq_p1)))
[@ Meta.Attribute.inline_ ]
let ladder0_ #s k q p01_tmp1_swap tmp2 =
  let p01_tmp1 = sub p01_tmp1_swap 0ul (8ul *! nlimb s) in
  let nq : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  let nq_p1 : point s = sub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
  let swap:lbuffer uint64 1ul = sub p01_tmp1_swap (8ul *! nlimb s) 1ul in

  assert (gsub p01_tmp1_swap 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  assert (gsub p01_tmp1 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  assert (gsub p01_tmp1_swap 0ul (8ul *! nlimb s) == p01_tmp1);
  assert (gsub p01_tmp1_swap (8ul *! nlimb s) 1ul == swap);

  // bit 255 is 0 and bit 254 is 1
  cswap2 #s (u64 1) nq nq_p1;
  point_add_and_double #s q p01_tmp1 tmp2;
  swap.(0ul) <- u64 1;

  //Got about 1K speedup by removing 4 iterations here.
  //First iteration can be skipped because top bit of scalar is 0
  ladder_step_loop #s k q p01_tmp1_swap tmp2;
  let sw = swap.(0ul) in
  cswap2 #s sw nq nq_p1

val ladder1_:
    #s:field_spec
  -> p01_tmp1:lbuffer (limb s) (8ul *! nlimb s)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 p01_tmp1 /\ live h0 tmp2 /\ disjoint p01_tmp1 tmp2 /\
     (let nq = gsub p01_tmp1 0ul (2ul *! nlimb s) in
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq)))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1 |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1 0ul (2ul *! nlimb s) in
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      fget_xz h1 nq == M.montgomery_ladder1_1 (fget_xz h0 nq)))
[@ Meta.Attribute.inline_ ]
let ladder1_ #s p01_tmp1 tmp2 =
  let nq : point s = sub p01_tmp1 0ul (2ul *! nlimb s) in
  let tmp1 = sub p01_tmp1 (4ul *! nlimb s) (4ul *! nlimb s) in

  assert (gsub p01_tmp1 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1 (4ul *! nlimb s) (4ul *! nlimb s) == tmp1);

  point_double nq tmp1 tmp2;
  point_double nq tmp1 tmp2;
  point_double nq tmp1 tmp2

val ladder2_:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
     (let nq' = M.montgomery_ladder1_0 (as_seq h0 k) (fget_xz h0 q) (fget_xz h0 nq) (fget_xz h0 nq_p1) in
      fget_xz h1 nq == M.montgomery_ladder1_1 nq')))
[@ Meta.Attribute.inline_ ]
let ladder2_ #s k q p01_tmp1_swap tmp2 =
  let p01_tmp1 = sub p01_tmp1_swap 0ul (8ul *! nlimb s) in
  let nq : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  let nq_p1 : point s = sub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
  assert (gsub p01_tmp1_swap 0ul (8ul *! nlimb s) == p01_tmp1);
  assert (gsub p01_tmp1_swap 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1 0ul (2ul *! nlimb s) == nq);
  assert (gsub p01_tmp1 (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  assert (gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) == nq_p1);
  ladder0_ #s k q p01_tmp1_swap tmp2;
  ladder1_ #s p01_tmp1 tmp2

inline_for_extraction noextract
val ladder3_:
    #s:field_spec
  -> q:point s
  -> p01:lbuffer (limb s) (4ul *! nlimb s)
  -> Stack unit
    (requires fun h0 ->
      live h0 q /\ live h0 p01 /\ disjoint q p01 /\
      fget_z h0 q == 1 /\ state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01) h0 h1 /\
     (let nq = gsub p01 0ul (2ul *! nlimb s) in
      let nq_p1 = gsub p01 (2ul *! nlimb s) (2ul *! nlimb s) in
      state_inv_t h1 (get_x q) /\ state_inv_t h1 (get_z q) /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1) /\
      (fget_xz h1 q, fget_xz h1 nq, fget_xz h1 nq_p1) == M.montgomery_ladder1_2 (fget_x h0 q)))
let ladder3_ #s q p01 =
  let p0 : point s = sub p01 0ul (2ul *! nlimb s) in
  let p1 : point s = sub p01 (2ul *! nlimb s) (2ul *! nlimb s) in
  copy p1 q;
  let x0 : felem s = sub p0 0ul (nlimb s) in
  let z0 : felem s = sub p0 (nlimb s) (nlimb s) in
  set_one x0;
  set_zero z0;
  let h0 = ST.get () in
  assert (gsub p01 0ul (2ul *! nlimb s) == p0);
  assert (gsub p01 (2ul *! nlimb s) (2ul *! nlimb s) == p1);
  assert (gsub p0 0ul (nlimb s) == x0);
  assert (gsub p0 (nlimb s) (nlimb s) == z0);

  assert (fget_x h0 p1 == fget_x h0 q);
  assert (fget_z h0 p1 == 1);
  assert (fget_x h0 p0 == 1);
  assert (fget_z h0 p0 == 0);

  assert (
    state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
    state_inv_t h0 (get_x p0) /\ state_inv_t h0 (get_z p0) /\
    state_inv_t h0 (get_x p1) /\ state_inv_t h0 (get_z p1))

val ladder4_:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
      fget_z h0 q == 1 /\ state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q))
    (ensures  fun h0 _ h1 ->
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
     (let nq = gsub p01_tmp1_swap 0ul (2ul *! nlimb s) in
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      fget_xz h1 nq == S.montgomery_ladder (fget_x h0 q) (as_seq h0 k)))
[@ Meta.Attribute.inline_ ]
let ladder4_ #s k q p01_tmp1_swap tmp2 =
  let h0 = ST.get () in
  let p01 = sub p01_tmp1_swap 0ul (4ul *! nlimb s) in
  let p0 : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  let p1 : point s = sub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in

  assert (gsub p01_tmp1_swap 0ul (4ul *! nlimb s) == p01);
  assert (gsub p01 0ul (2ul *! nlimb s) == p0);
  assert (gsub p01 (2ul *! nlimb s) (2ul *! nlimb s) == p1);

  ladder3_ #s q p01;
  ladder2_ #s k q p01_tmp1_swap tmp2;
  let h1 = ST.get () in
  assert (fget_xz h1 p0 == M.montgomery_ladder1 (fget_x h0 q) (as_seq h0 k));
  M.lemma_montgomery_ladder (fget_x h0 q) (as_seq h0 k)

val montgomery_ladder:
    #s:field_spec
  -> o:point s
  -> k:scalar
  -> i:point s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 k /\ live h0 i /\
      (disjoint o i \/ o == i) /\ disjoint o k /\ disjoint k i /\
      fget_z h0 i == 1 /\ state_inv_t h0 (get_x i) /\ state_inv_t h0 (get_z i))
    (ensures  fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      state_inv_t h1 (get_x o) /\ state_inv_t h1 (get_z o) /\
      fget_xz h1 o == S.montgomery_ladder (fget_x h0 i) (as_seq h0 k))
[@ Meta.Attribute.specialize ]
let montgomery_ladder #s out key init =
  push_frame();
  let h0 = ST.get () in
  let tmp2 = create (2ul `FStar.UInt32.mul` ((nwide s) <: FStar.UInt32.t)) (wide_zero s) in
  let p01_tmp1_swap = create (8ul *! nlimb s +! 1ul) (limb_zero s) in

  let p0 : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  assert (gsub p01_tmp1_swap 0ul (2ul *! nlimb s) == p0);
  ladder4_ #s key init p01_tmp1_swap tmp2;
  copy out p0;
  pop_frame ()

inline_for_extraction noextract
let g25519_t = x:ilbuffer byte_t 32ul{witnessed x (Lib.Sequence.of_list S.basepoint_list) /\ recallable x}

/// Public API
/// ==========

val scalarmult: (#s: field_spec) -> scalarmult_st s True
[@ Meta.Attribute.specialize ]
let scalarmult #s out priv pub =
  push_frame ();
  let init = create (2ul `FStar.UInt32.mul` ((nlimb s) <: FStar.UInt32.t)) (limb_zero s) in
  decode_point #s init pub;
  montgomery_ladder #s init priv init;
  encode_point #s out init;
  pop_frame()

val secret_to_public (#s:field_spec) (g25519: g25519_t): secret_to_public_st s True
[@ Meta.Attribute.specialize ]
let secret_to_public #s g25519 pub priv =
  push_frame ();
  recall_contents g25519 S.basepoint_lseq;
  let basepoint = create 32ul (u8 0) in
  mapT 32ul basepoint secret g25519;
  scalarmult #s pub priv basepoint;
  pop_frame()

val ecdh: (#s:field_spec) -> ecdh_st s True
[@ Meta.Attribute.specialize ]
let ecdh #s out priv pub =
  push_frame ();
  let zeros = create 32ul (u8 0) in
  scalarmult #s out priv pub;
  let r = lbytes_eq #32ul out zeros in
  pop_frame();
  not r
