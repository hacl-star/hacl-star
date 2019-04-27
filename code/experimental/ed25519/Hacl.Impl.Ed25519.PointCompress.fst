module Hacl.Impl.Ed25519.PointCompress

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

inline_for_extraction noextract
val x_mod_2:
  x:felem ->
  Stack uint64
    (requires fun h -> live h x)
    (ensures  fun h0 z h1 -> h0 == h1 /\ v z < 2)
let x_mod_2 x =
  let x0 = x.(0ul) in
  let z  = x0 &. u64 1 in
  mod_mask_lemma x0 1ul;
  uintv_extensionality (u64 1) (mod_mask #U64 1ul);
  z

inline_for_extraction noextract
val add_sign:
    out:lbuffer uint8 32ul
  -> x:uint64{v x < 2} ->
  Stack unit
    (requires fun h -> live h out)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let add_sign out x =
  let xbyte = to_u8 x in
  let o31 = out.(31ul) in
  out.(31ul) <- o31 +. (xbyte <<. 7ul)

inline_for_extraction noextract
val point_compress_:
    tmp:lbuffer uint64 15ul
  -> p:point ->
  Stack unit
    (requires fun h -> live h tmp /\ live h p /\ disjoint tmp p)
    (ensures  fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let point_compress_ tmp p =
  let zinv = sub tmp 0ul  5ul in
  let x    = sub tmp 5ul  5ul in
  let out  = sub tmp 10ul 5ul in
  let px   = getx p in
  let py   = gety p in
  let pz   = getz p in
  inverse zinv pz;
  fmul x px zinv;
  reduce x;
  fmul out py zinv;
  reduce out

val point_compress:
  out:lbuffer uint8 32ul
  -> p:point ->
  Stack unit
    (requires fun h -> live h out /\ live h p)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let point_compress z p =
  push_frame();
  let tmp  = create 15ul (u64 0) in
  let zinv = sub tmp 0ul  5ul in
  let x    = sub tmp 5ul  5ul in
  let out  = sub tmp 10ul 5ul in
  point_compress_ tmp p;
  let b = x_mod_2 x in
  store_51 z out;
  add_sign z b;
  pop_frame()
