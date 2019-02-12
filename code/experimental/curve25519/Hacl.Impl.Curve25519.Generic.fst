module Hacl.Impl.Curve25519.Generic

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Curve25519.Fields

include Hacl.Impl.Curve25519.Finv
include Hacl.Impl.Curve25519.AddAndDouble

module ST = FStar.HyperStack.ST

module F26 = Hacl.Impl.Curve25519.Field26
module F51 = Hacl.Impl.Curve25519.Field51
module F64 = Hacl.Impl.Curve25519.Field64

module S = Spec.Curve25519
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --max_fuel 2 --using_facts_from '* -FStar.Seq'"
//#set-options "--debug Hacl.Impl.Curve25519.Generic --debug_level ExtractNorm"

inline_for_extraction
let scalar = lbuffer uint8 32ul

inline_for_extraction
val scalar_bit:
    s:scalar
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      v r == v (S.ith_bit (as_seq h0 s) (v n)))
let scalar_bit s n = to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)

inline_for_extraction
val decode_point_:
    #s:field_spec
  -> o:point s
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      state_inv_t h1 (get_x o) /\ state_inv_t h1 (get_z o) /\
      fget_x h1 o == S.decodePoint (as_seq h0 i) /\ fget_z h1 o == 1)
let decode_point_ #s o i =
  push_frame();
  let tmp = create 4ul (u64 0) in
  let h0 = ST.get () in
  uints_from_bytes_le #U64 tmp i;
  let tmp3 = tmp.(3ul) in
  tmp.(3ul) <- tmp3 &. u64 0x7fffffffffffffff;
  mod_mask_lemma tmp3 63ul;
  assert_norm (0x7fffffffffffffff = pow2 63 - 1);
  uintv_extensionality (mod_mask #U64 63ul) (u64 0x7fffffffffffffff);
  let h1 = ST.get () in
  assert (v (LSeq.index (as_seq h1 tmp) 3) < pow2 63);
  assume (BSeq.nat_from_intseq_le (as_seq h1 tmp) == BSeq.nat_from_bytes_le (as_seq h0 i) % pow2 255);
  let x : felem s = sub o 0ul (nlimb s) in
  let z : felem s = sub o (nlimb s) (nlimb s) in
  set_one z;
  load_felem x tmp;
  pop_frame()

(* WRAPPER to Prevent Inlining *)
inline_for_extraction
let decode_point_26 (o:point26) i = decode_point_ #M26 o i
inline_for_extraction
let decode_point_51 (o:point51) i = decode_point_ #M51 o i
inline_for_extraction
let decode_point_64 (o:point64) i = decode_point_ #M64 o i

inline_for_extraction
val decode_point:
    #s:field_spec
  -> o:point s
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      state_inv_t h1 (get_x o) /\ state_inv_t h1 (get_z o) /\
      fget_x h1 o == S.decodePoint (as_seq h0 i) /\ fget_z h1 o == 1)
let decode_point #s o i =
  match s with
  | M26 -> decode_point_26 o i
  | M51 -> decode_point_51 o i
  | M64 -> decode_point_64 o i
(* WRAPPER to Prevent Inlining *)


inline_for_extraction
val encode_point_:
    #s:field_spec
  -> o:lbuffer uint8 32ul
  -> i:point s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ disjoint o i /\
      state_inv_t h0 (get_x i) /\ state_inv_t h0 (get_z i))
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.encodePoint (fget_x h0 i, fget_z h0 i))
let encode_point_ #s o i =
  push_frame();
  let x : felem s = sub i 0ul (nlimb s) in
  let z : felem s = sub i (nlimb s) (nlimb s) in
  let tmp = create_felem s in
  let u64s = create 4ul (u64 0) in
  let tmp_w = create (2ul *. nwide s) (wide_zero s) in
  let h0 = ST.get () in
  finv tmp z tmp_w;
  let h1 = ST.get () in
  assert (feval h1 tmp == Hacl.Spec.Curve25519.Finv.pow (feval h0 z) (pow2 255 - 21));
  Hacl.Spec.Curve25519.Finv.lemma_fpow_is_pow (feval h0 z) (pow2 255 - 21);
  fmul tmp tmp x tmp_w;
  let h2 = ST.get () in
  assert (feval h2 tmp == S.fmul (S.fpow (feval h0 z) (pow2 255 - 21)) (feval h0 x));
  assert (feval h2 tmp == S.fmul (feval h0 x) (S.fpow (feval h0 z) (pow2 255 - 21)));
  store_felem u64s tmp;
  let h3 = ST.get () in
  //assert (BSeq.nat_from_intseq_le (as_seq h3 u64s) == feval h2 tmp);
  uints_to_bytes_le #U64 4ul o u64s;
  let h4 = ST.get () in
  //assume (BSeq.nat_from_intseq_le (as_seq h3 u64s) == BSeq.nat_from_intseq_le (as_seq h4 o));
  assume (as_seq h4 o == BSeq.nat_to_bytes_le 32 (feval h2 tmp));
  pop_frame()

(* WRAPPER to Prevent Inlining *)
inline_for_extraction
let encode_point_26 o (i:point26) = encode_point_ #M26 o i
inline_for_extraction
let encode_point_51 o (i:point51) = encode_point_ #M51 o i
inline_for_extraction
let encode_point_64 o (i:point64) = encode_point_ #M64 o i

inline_for_extraction
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
let encode_point #s o i =
  match s with
  | M26 -> encode_point_26 o i
  | M51 -> encode_point_51 o i
  | M64 -> encode_point_64 o i
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val ladder_step:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> i:size_t{v i < 251}
  -> nq:point s
  -> nq_p1:point s
  -> tmp1:lbuffer (limb s) (4ul *. nlimb s)
  -> tmp2:felem_wide2 s
  -> swap:lbuffer uint64 1ul
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 nq /\ live h0 nq_p1 /\
      live h0 tmp1 /\ live h0 tmp2 /\ live h0 swap /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc nq; loc nq_p1; loc tmp1; loc tmp2; loc swap] /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1))
    (ensures  fun h0 _ h1 ->
      modifies (loc swap |+| loc tmp1 |+| loc tmp2 |+| loc nq |+| loc nq_p1) h0 h1 /\
      state_inv_t h1 (get_x q) /\ state_inv_t h1 (get_z q) /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1))
let ladder_step #s k q i nq nq_p1 tmp1 tmp2 swap =
  let bit = scalar_bit k (253ul -. i) in
  let sw = swap.(0ul) ^. bit in
  assume (v sw <= 1);
  cswap2 #s sw nq nq_p1;
  point_add_and_double #s q nq nq_p1 tmp1 tmp2;
  swap.(0ul) <- bit

inline_for_extraction
val ladder_step_loop:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> nq:point s
  -> nq_p1:point s
  -> tmp1:lbuffer (limb s) (4ul *. nlimb s)
  -> tmp2:felem_wide2 s
  -> swap:lbuffer uint64 1ul
  -> Stack unit
    (requires fun h0 ->
      live h0 k /\ live h0 q /\ live h0 nq /\ live h0 nq_p1 /\
      live h0 tmp1 /\ live h0 tmp2 /\ live h0 swap /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc nq; loc nq_p1; loc tmp1; loc tmp2; loc swap] /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1))
    (ensures  fun h0 _ h1 ->
      modifies (loc swap |+| loc tmp1 |+| loc tmp2 |+| loc nq |+| loc nq_p1) h0 h1 /\
      state_inv_t h1 (get_x q) /\ state_inv_t h1 (get_z q) /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1))
let ladder_step_loop #s k q nq nq_p1 tmp1 tmp2 swap =
  let h0 = ST.get () in
  [@ inline_let]
  let inv h (i:nat{i <= 251}) =
    modifies (loc swap |+| loc tmp1 |+| loc tmp2 |+| loc nq |+| loc nq_p1) h0 h /\
    live h k /\ live h q /\ live h nq /\ live h nq_p1 /\
    live h tmp1 /\ live h tmp2 /\ live h swap /\
    LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc nq; loc nq_p1; loc tmp1; loc tmp2; loc swap] /\
    state_inv_t h (get_x q) /\ state_inv_t h (get_z q) /\
    state_inv_t h (get_x nq) /\ state_inv_t h (get_z nq) /\
    state_inv_t h (get_x nq_p1) /\ state_inv_t h (get_z nq_p1) in

  Lib.Loops.for 0ul 251ul inv
    (fun i ->
      ladder_step #s k q i nq nq_p1 tmp1 tmp2 swap)

#set-options "--z3rlimit 150"

inline_for_extraction
val ladder_:
    #s:field_spec
  -> k:scalar
  -> q:point s
  -> p01_tmp1_swap:lbuffer (limb s) (8ul *! nlimb s +! 1ul)
  -> tmp2:felem_wide2 s
  -> Stack unit
    (requires fun h0 -> (
      let nq = gsub p01_tmp1_swap 0ul (2ul *. nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *. nlimb s) (2ul *. nlimb s) in
      live h0 k /\ live h0 q /\ live h0 p01_tmp1_swap /\ live h0 tmp2 /\
      LowStar.Monotonic.Buffer.all_disjoint [loc k; loc q; loc p01_tmp1_swap; loc tmp2] /\
      state_inv_t h0 (get_x q) /\ state_inv_t h0 (get_z q) /\
      state_inv_t h0 (get_x nq) /\ state_inv_t h0 (get_z nq) /\
      state_inv_t h0 (get_x nq_p1) /\ state_inv_t h0 (get_z nq_p1)))
    (ensures  fun h0 _ h1 -> (
      let nq = gsub p01_tmp1_swap 0ul (2ul *. nlimb s) in
      let nq_p1 = gsub p01_tmp1_swap (2ul *. nlimb s) (2ul *. nlimb s) in
      modifies (loc p01_tmp1_swap |+| loc tmp2) h0 h1 /\
      //state_inv_t h1 (get_x q) /\ state_inv_t h1 (get_z q) /\
      state_inv_t h1 (get_x nq) /\ state_inv_t h1 (get_z nq) /\
      state_inv_t h1 (get_x nq_p1) /\ state_inv_t h1 (get_z nq_p1)))
let ladder_ #s k q p01_tmp1_swap tmp2 =
  let nq : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  let nq_p1 : point s = sub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
  let tmp1 = sub p01_tmp1_swap (4ul *! nlimb s) (4ul *! nlimb s) in
  let swap:lbuffer uint64 1ul = sub p01_tmp1_swap (8ul *! nlimb s) 1ul in

  // bit 255 is 0 and bit 254 is 1
  cswap2 #s (u64 1) nq nq_p1;
  point_add_and_double #s q nq nq_p1 tmp1 tmp2;
  swap.(0ul) <- u64 1;

  //Got about 1K speedup by removing 4 iterations here.
  //First iteration can be skipped because top bit of scalar is 0
  ladder_step_loop #s k q nq nq_p1 tmp1 tmp2 swap;
  let h = ST.get () in
  assume (v (LSeq.index (as_seq h swap) 0) <= 1);
  cswap2 #s swap.(0ul) nq nq_p1;
  point_double nq tmp1 tmp2;
  point_double nq tmp1 tmp2;
  point_double nq tmp1 tmp2

inline_for_extraction
val montgomery_ladder_:
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
      state_inv_t h1 (get_x o) /\ state_inv_t h1 (get_z o))
      //fget_xz h1 o == S.montgomery_ladder (fget_x h0 i) (as_seq h0 k))
let montgomery_ladder_ #s out key init =
  push_frame();
  let tmp2 = create (2ul *! nwide s) (wide_zero s) in
  let p01_tmp1_swap = create (4ul *! nlimb s +! 4ul *! nlimb s +! 1ul) (limb_zero s) in
  let p0 : point s = sub p01_tmp1_swap 0ul (2ul *! nlimb s) in
  let p1 : point s = sub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) in
  copy p1 init;
  let x0 : felem s = sub p0 0ul (nlimb s) in
  let z0 : felem s = sub p0 (nlimb s) (nlimb s) in
  set_one x0;
  set_zero z0;
  let h0 = ST.get () in
  assert (gsub p01_tmp1_swap 0ul (2ul *! nlimb s) == p0);
  assert (gsub p01_tmp1_swap (2ul *! nlimb s) (2ul *! nlimb s) == p1);
  assert (gsub p0 0ul (nlimb s) == x0);
  assert (gsub p0 (nlimb s) (nlimb s) == z0);

  assume (fget_x h0 p1 == fget_x h0 init);
  assume (fget_z h0 p1 == 1);
  assume (fget_x h0 p0 == 1);
  assume (fget_z h0 p0 == 0);

  assume (
    state_inv_t h0 (get_x init) /\ state_inv_t h0 (get_z init) /\
    state_inv_t h0 (get_x p0) /\ state_inv_t h0 (get_z p0) /\
    state_inv_t h0 (get_x p1) /\ state_inv_t h0 (get_z p1));

  ladder_ #s key init p01_tmp1_swap tmp2;
  copy out p0;
  pop_frame ()

(* WRAPPER to Prevent Inlining *)
[@CInline]
let montgomery_ladder_26 (out:point26) key (init:point26) = montgomery_ladder_ #M26 out key init
[@CInline]
let montgomery_ladder_51 (out:point51) key (init:point51) = montgomery_ladder_ #M51 out key init
[@CInline]
let montgomery_ladder_64 (out:point64) key (init:point64) = montgomery_ladder_ #M64 out key init

inline_for_extraction
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
let montgomery_ladder #s out key init = admit();
  match s with
  | M26 -> montgomery_ladder_26 out key init
  | M51 -> montgomery_ladder_51 out key init
  | M64 -> montgomery_ladder_64 out key init
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val scalarmult:
    #s:field_spec
  -> o:lbuffer uint8 32ul
  -> k:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 k /\ live h0 i /\
      disjoint o i /\ disjoint o k)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.scalarmult (as_seq h0 k) (as_seq h0 i))
let scalarmult #s out priv pub =
  push_frame ();
  let init = create (2ul *. nlimb s) (limb_zero s) in
  decode_point #s init pub;
  montgomery_ladder #s init priv init;
  encode_point #s out init;
  pop_frame()

let g25519 : x:ilbuffer byte_t 32ul{witnessed x (Lib.Sequence.of_list S.basepoint_list) /\ recallable x} =
  createL_global S.basepoint_list

inline_for_extraction
val secret_to_public:
    #s:field_spec
  -> o:lbuffer uint8 32ul
  -> i:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.secret_to_public (as_seq h0 i))
let secret_to_public #s pub priv =
  push_frame ();
  recall_contents g25519 S.basepoint_lseq;
  let basepoint = create 32ul (u8 0) in
  mapT 32ul basepoint secret g25519;
  scalarmult #s pub priv basepoint;
  pop_frame()
