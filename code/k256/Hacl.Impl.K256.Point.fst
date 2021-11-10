module Hacl.Impl.K256.Point

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module SD = Hacl.Spec.Bignum.Definitions
module S = Spec.K256

open Hacl.K256.Field

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Affine coordinates

inline_for_extraction noextract
let aff_point = lbuffer uint64 (nlimb *! 2ul)

inline_for_extraction noextract
let aff_getx (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul nlimb /\ h0 == h1)
  = sub p 0ul nlimb

inline_for_extraction noextract
let aff_gety (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p nlimb nlimb /\ h0 == h1)
  = sub p nlimb nlimb


noextract
let aff_point_inv_lseq (p:LSeq.lseq uint64 8) =
  SD.bn_v (LSeq.sub p 0 4) < S.prime /\
  SD.bn_v (LSeq.sub p 4 4) < S.prime

noextract
let aff_point_inv (h:mem) (p:aff_point) =
  aff_point_inv_lseq (as_seq h p)

noextract
let aff_point_as_nat2_lseq (p:LSeq.lseq uint64 8) =
  (SD.bn_v (LSeq.sub p 0 4), SD.bn_v (LSeq.sub p 4 4))

noextract
let aff_point_as_nat3 (h:mem) (p:aff_point) =
  aff_point_as_nat2_lseq (as_seq h p)

noextract
let aff_point_as_nat2_aff_lseq (p:LSeq.lseq uint64 8{aff_point_inv_lseq p}) : GTot Spec.K256.aff_point =
  (SD.bn_v (LSeq.sub p 0 4), SD.bn_v (LSeq.sub p 4 4))

noextract
let aff_point_as_nat2_aff (h:mem) (p:aff_point{aff_point_inv h p}) : GTot Spec.K256.aff_point =
  aff_point_as_nat2_aff_lseq (as_seq h p)


///  Projective coordinates

// (_X, _Y, _Z)
inline_for_extraction noextract
let point = lbuffer uint64 (nlimb *! 3ul)

inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul nlimb /\ h0 == h1)
  = sub p 0ul nlimb

inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p nlimb nlimb /\ h0 == h1)
  = sub p nlimb nlimb

inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p (2ul *! nlimb) nlimb /\ h0 == h1)
  = sub p (2ul *! nlimb) nlimb


noextract
let point_inv_lseq (p:LSeq.lseq uint64 12) =
  SD.bn_v (LSeq.sub p 0 4) < S.prime /\
  SD.bn_v (LSeq.sub p 4 4) < S.prime /\
  SD.bn_v (LSeq.sub p 8 4) < S.prime

noextract
let point_inv (h:mem) (p:point) =
  point_inv_lseq (as_seq h p)

noextract
let point_as_nat3_lseq (p:LSeq.lseq uint64 12) =
  (SD.bn_v (LSeq.sub p 0 4),
   SD.bn_v (LSeq.sub p 4 4),
   SD.bn_v (LSeq.sub p 8 4))

noextract
let point_as_nat3 (h:mem) (p:point) =
  point_as_nat3_lseq (as_seq h p)

noextract
let point_as_nat3_proj_lseq (p:LSeq.lseq uint64 12{point_inv_lseq p}) : GTot S.proj_point =
  (SD.bn_v (LSeq.sub p 0 4),
   SD.bn_v (LSeq.sub p 4 4),
   SD.bn_v (LSeq.sub p 8 4))

noextract
let point_as_nat3_proj (h:mem) (p:point{point_inv h p}) : GTot S.proj_point =
  point_as_nat3_proj_lseq (as_seq h p)

noextract
let point_eval (h:mem) (p:point) =
  (feval h (gsub p 0ul nlimb),
   feval h (gsub p nlimb nlimb),
   feval h (gsub p (2ul *! nlimb) nlimb))

///  Create a point

inline_for_extraction noextract
val create_point: unit -> StackInline point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (3 * v nlimb) (u64 0)))
    //point_inv h1 f /\
    //point_as_nat3_proj h1 f == (S.zero, S.zero, S.zero))

let create_point () =
  create (3ul *! nlimb) (u64 0)


///  Conversion functions between affine and projective coordinates

inline_for_extraction noextract
val to_proj_point (p:point) (x y:lbuffer uint8 32ul) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\ disjoint p x /\ disjoint p y /\

    BSeq.nat_from_bytes_be (as_seq h x) < S.prime /\
    BSeq.nat_from_bytes_be (as_seq h y) < S.prime)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_inv h1 p /\
    point_as_nat3_proj h1 p ==
     (BSeq.nat_from_bytes_be (as_seq h0 x),
      BSeq.nat_from_bytes_be (as_seq h0 y),
      S.one))

let to_proj_point p x y =
  push_frame ();
  let x2 = create nlimb (u64 0) in
  let y2 = create nlimb (u64 0) in
  load_felem x2 x;
  load_felem y2 y;
  let x1, y1, z1 = getx p, gety p, getz p in
  copy x1 x2;
  copy y1 y2;
  set_one z1;
  pop_frame ()
