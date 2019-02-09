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

#set-options "--z3rlimit 50 --max_fuel 2"
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
      fget_x h1 o == S.decodePoint (as_seq h0 i) /\
      fget_z h1 o == 1)
let decode_point_ #s o i =
  push_frame();
  let tmp = create 4ul (u64 0) in
  uints_from_bytes_le #U64 tmp i;
  tmp.(3ul) <- tmp.(3ul) &. u64 0x7fffffffffffffff;
  let x : felem s = sub o 0ul (nlimb s) in
  let z : felem s = sub o (nlimb s) (nlimb s) in
  set_one z;
  load_felem x tmp; admit();
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
      fget_x h1 o == S.decodePoint (as_seq h0 i) /\
      fget_z h1 o == 1)
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
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.encodePoint (fget_x h0 i, fget_z h0 i))
let encode_point_ #s o i =
  push_frame();
  let x : felem s = sub i 0ul (nlimb s) in
  let z : felem s = sub i (nlimb s) (nlimb s) in
  let tmp = create_felem s in
  let u64s = create 4ul (u64 0) in
  let tmp_w = create (2ul *. nwide s) (wide_zero s) in
  admit();
  finv #s tmp z tmp_w;
  fmul #s tmp tmp x tmp_w;
  store_felem u64s tmp;
  uints_to_bytes_le #U64 4ul o u64s;
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
    (requires fun h0 -> live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 _ h1 -> modifies (loc o) h0 h1 /\
      as_seq h1 o == S.encodePoint (fget_x h0 i, fget_z h0 i))
let encode_point #s o i =
  match s with
  | M26 -> encode_point_26 o i
  | M51 -> encode_point_51 o i
  | M64 -> encode_point_64 o i
(* WRAPPER to Prevent Inlining *)

inline_for_extraction
val montgomery_ladder_:
    #s:field_spec
  -> o:point s
  -> k:scalar
  -> i:point s
  -> Stack unit
    (requires fun h0 ->
      live h0 o /\ live h0 k /\ live h0 i /\
      fget_z h0 i == 1)
    (ensures  fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      fget_xz h1 o == S.montgomery_ladder (fget_x h0 i) (as_seq h0 k))
let montgomery_ladder_ #s out key init =
  push_frame();
  let p01 = create (4ul *. nlimb s) (limb_zero s) in
  let p0 : point s = sub p01 0ul (2ul *. nlimb s) in
  let p1 : point s = sub p01 (2ul *. nlimb s) (2ul *. nlimb s) in
  copy p1 init;
  let x0 : felem s = sub p0 0ul (nlimb s) in
  let z0 : felem s = sub p0 (nlimb s) (nlimb s) in
  set_one x0;
  let swap = create 1ul (u64 0) in
  let tmp1 = create (4ul *. nlimb s) (limb_zero s) in
  let tmp2 = create (2ul *. nwide s) (wide_zero s) in
  admit();
  // bit 255 is 0 and bit 254 is 1
  cswap2 #s (u64 1) p0 p1;
  point_add_and_double #s init p0 p1 tmp1 tmp2;
  swap.(0ul) <- u64 1;

  let h0 = ST.get() in
  //Got about 1K speedup by removing 4 iterations here.
  //First iteration can be skipped because top bit of scalar is 0
  loop2 h0 251ul p01 swap
  (fun h -> (fun i s -> s))
  (fun i ->
    let bit = scalar_bit key (253ul -. i) in
    let sw = swap.(0ul) ^. bit in
    cswap2 #s sw p0 p1;
    point_add_and_double #s init p0 p1 tmp1 tmp2;
    swap.(0ul) <- bit;
    admit());
  cswap2 #s swap.(0ul) p0 p1;
  //Last three iterations are point doublings because the bottom 3 bits are 0
  point_double p0 tmp1 tmp2;
  point_double p0 tmp1 tmp2;
  point_double p0 tmp1 tmp2;
  copy out p0;
  pop_frame()

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
      fget_z h0 i == 1)
    (ensures  fun h0 _ h1 ->
      modifies (loc o) h0 h1 /\
      fget_xz h1 o == S.montgomery_ladder (fget_x h0 i) (as_seq h0 k))
let montgomery_ladder #s out key init =
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
