module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Bignum

module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.P256
module SM = Hacl.Spec.P256.MontgomeryMultiplication

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

///  Affine coordinates

inline_for_extraction noextract
let aff_point_seq = LSeq.lseq uint64 8

let as_aff_point_nat_seq (p:aff_point_seq) =
  felem_seq_as_nat (LSeq.sub p 0 4),
  felem_seq_as_nat (LSeq.sub p 4 4)

let aff_point_inv_seq (p:aff_point_seq) =
  let x, y = as_aff_point_nat_seq p in
  x < S.prime /\ y < S.prime


inline_for_extraction noextract
let aff_point = lbuffer uint64 8ul

noextract
let as_aff_point_nat (h:mem) (p:aff_point) =
  as_aff_point_nat_seq (as_seq h p)

noextract
let aff_point_inv (h:mem) (p:aff_point) =
  aff_point_inv_seq (as_seq h p)

noextract
let aff_point_x_as_nat (h:mem) (p:aff_point) : GTot nat =
  as_nat h (gsub p 0ul 4ul)

noextract
let aff_point_y_as_nat (h:mem) (p:aff_point) : GTot nat =
  as_nat h (gsub p 4ul 4ul)

inline_for_extraction noextract
let aff_getx (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 4ul /\ h0 == h1)
  = sub p 0ul 4ul

inline_for_extraction noextract
let aff_gety (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 4ul 4ul /\ h0 == h1)
  = sub p 4ul 4ul


///  Jacobian coordinates

inline_for_extraction noextract
let point_seq = LSeq.lseq uint64 12

let as_point_nat_seq (p:point_seq) =
  felem_seq_as_nat (LSeq.sub p 0 4),
  felem_seq_as_nat (LSeq.sub p 4 4),
  felem_seq_as_nat (LSeq.sub p 8 4)

let point_inv_seq (p:point_seq) =
  let x, y, z = as_point_nat_seq p in
  x < S.prime /\ y < S.prime /\ z < S.prime


inline_for_extraction noextract
let point = lbuffer uint64 12ul

noextract
let as_point_nat (h:mem) (p:point) =
  as_point_nat_seq (as_seq h p)

noextract
let point_inv (h:mem) (p:point) =
  point_inv_seq (as_seq h p)

noextract
let point_x_as_nat (h:mem) (p:point) : GTot nat =
  as_nat h (gsub p 0ul 4ul)

noextract
let point_y_as_nat (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e 4ul 4ul)

noextract
let point_z_as_nat (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e 8ul 4ul)


inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 4ul /\ h0 == h1)
  = sub p 0ul 4ul

inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 4ul 4ul /\ h0 == h1)
  = sub p 4ul 4ul

inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 8ul 4ul /\ h0 == h1)
  = sub p 8ul 4ul


///  Create a point

inline_for_extraction noextract
val create_point: unit -> StackInline point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 12 (u64 0)))


val make_base_point: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ SM.fromDomainPoint (as_point_nat h1 p) == S.base_point)


val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ SM.fromDomainPoint (as_point_nat h1 p) == S.point_at_inf)


inline_for_extraction noextract
val copy_point: p:point -> res:point -> Stack unit
  (requires fun h -> live h p /\ live h res /\ disjoint p res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == as_seq h0 p)


///  check if a point is a point-at-infinity

val is_point_at_inf: p:point -> Stack uint64
  (requires fun h -> live h p /\ point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if S.is_point_at_inf (SM.fromDomainPoint (as_point_nat h0 p))
     then v r = ones_v U64 else v r = 0) /\
    (if S.is_point_at_inf (as_point_nat h0 p)
     then v r = ones_v U64 else v r = 0))


val is_point_at_inf_vartime: p:point -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_at_inf (as_point_nat h0 p))


///  Point conversion between Montgomery and Regular representations

val point_to_mont: p:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
   (let px, py, pz = as_point_nat h0 p in
    let rx, ry, rz = as_point_nat h1 res in
    rx == SM.toDomain_ px /\
    ry == SM.toDomain_ py /\
    rz == SM.toDomain_ pz))


// NOT used?
val point_from_mont: p:point -> res:point-> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
   (let px, py, pz = as_point_nat h0 p in
    let rx, ry, rz = as_point_nat h1 res in
    rx == SM.fromDomain_ px /\
    ry == SM.fromDomain_ py /\
    rz == SM.fromDomain_ pz))


///  Point conversion between Jacobian and Affine coordinates representations

val norm_jacob_point_x: p:point -> res:felem -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1  /\
   (let rx, _, _ = S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h0 p)) in
    as_nat h1 res == rx))


val norm_jacob_point: p:point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_point_nat h1 res ==
      S.norm_jacob_point (SM.fromDomainPoint (as_point_nat h0 p)))


val to_jacob_point: p:aff_point -> res:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_point_nat h1 res ==
      S.to_jacob_point (aff_point_x_as_nat h0 p, aff_point_y_as_nat h0 p))


///  Check if a point is on the curve

val is_point_on_curve_vartime: p:aff_point -> Stack bool
  (requires fun h -> live h p /\ aff_point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_on_curve (as_aff_point_nat h0 p))


///  Point load and store functions

val aff_store_point: res:lbuffer uint8 64ul -> p:aff_point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.aff_store_point (as_aff_point_nat h0 p))


val load_point_vartime: p:point -> b:lbuffer uint8 64ul -> Stack bool
  (requires fun h ->
    live h p /\ live h b /\ disjoint p b)
  (ensures  fun h0 res h1 -> modifies (loc p) h0 h1 /\
    (let ps = S.load_point (as_seq h0 b) in
    (res <==> Some? ps) /\ (res ==> (point_inv h1 p /\
      as_point_nat h1 p == Some?.v ps))))


val aff_point_decompress_vartime (x y:felem) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    as_nat h1 x < S.prime /\ as_nat h1 y < S.prime /\ as_nat h1 x == xa /\ as_nat h1 y == ya)))
