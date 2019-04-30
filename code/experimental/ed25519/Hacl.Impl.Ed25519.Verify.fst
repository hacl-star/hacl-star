module Hacl.Impl.Ed25519.Verify

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

#reset-options "--max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
val verify_step_1:
    r:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> rs:lbuffer uint8 32ul
  -> public:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h r /\ live h msg /\ live h rs /\ live h public /\
      disjoint msg r /\ disjoint rs r /\ disjoint public r)
    (ensures fun h0 _ h1 -> modifies (loc r) h0 h1)
let verify_step_1 r msg len rs public =
  push_frame();
  let r' = create 5ul (u64 0) in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 r' rs public msg len;
  Hacl.Impl.Store56.store_56 r r';
  pop_frame()

inline_for_extraction noextract
val verify_step_2:
    s:lbuffer uint8 32ul
  -> h':lbuffer uint8 32ul
  -> a':point
  -> r':point ->
  Stack bool
    (requires fun h ->
      live h s  /\ live h h' /\ live h a' /\ live h r')
    (ensures fun h0 z h1 -> modifies0 h0 h1)
let verify_step_2 s h' a' r' =
  push_frame();
  let tmp = create 60ul (u64 0) in
  let hA   = sub tmp  0ul  20ul in
  let rhA  = sub tmp 20ul  20ul in
  let sB   = sub tmp 40ul  20ul in
  Hacl.Impl.Ed25519.Ladder.point_mul_g sB s;
  Hacl.Impl.Ed25519.Ladder.point_mul hA h' a';
  Hacl.Impl.Ed25519.PointAdd.point_add rhA r' hA;
  let b = Hacl.Impl.Ed25519.PointEqual.point_equal sB rhA in
  pop_frame();
  b

inline_for_extraction noextract
val verify_:
    public:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul
  -> tmp:lbuffer uint64 45ul
  -> tmp':lbuffer uint8 32ul ->
  Stack bool
    (requires fun h ->
      live h public /\ live h msg /\ live h signature /\ live h tmp /\ live h tmp' /\
      disjoint tmp public /\ disjoint tmp msg /\ disjoint tmp signature /\
      disjoint tmp tmp' /\ disjoint tmp' signature /\ disjoint tmp' public /\ disjoint tmp' msg)
    (ensures fun h0 z h1 -> modifies (loc tmp |+| loc tmp') h0 h1)
let verify_ public msg len signature tmp tmp' =
  let a' = sub tmp 0ul  20ul in
  let r' = sub tmp 20ul 20ul in
  let s  = sub tmp 40ul 5ul  in
  let h'  = tmp' in
  let b = Hacl.Impl.Ed25519.PointDecompress.point_decompress a' public in
  let res =
  if b then (
    let rs = sub signature 0ul 32ul in
    let b' = Hacl.Impl.Ed25519.PointDecompress.point_decompress r' rs in
    if b' then (
      Hacl.Impl.Load56.load_32_bytes s (sub signature 32ul 32ul);
      let b'' = Hacl.Impl.Ed25519.PointEqual.gte_q s in
      if b'' then false
      else (
        verify_step_1 h' msg len rs public;
	verify_step_2 (sub signature 32ul 32ul) h' a' r')
    ) else false
  ) else false in
  res

inline_for_extraction noextract
val verify:
    public:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public /\ live h msg /\ live h signature)
    (ensures  fun h0 z h1 -> modifies0 h0 h1)
let verify public msg len signature =
  push_frame();
  let tmp = create 45ul (u64 0) in
  let tmp' = create 32ul (u8 0) in
  let res = verify_ public msg len signature tmp tmp' in
  pop_frame();
  res
