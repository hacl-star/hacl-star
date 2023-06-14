module Hacl.Impl.P256.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.P256.Bignum

module S = Spec.P256
module SM = Hacl.Spec.P256.Montgomery
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

let from_mont_point (a:tuple3 nat nat nat) : S.proj_point =
  let x, y, z = a in SM.from_mont x, SM.from_mont y, SM.from_mont z


///  Affine coordinates

inline_for_extraction noextract
let aff_point_seq l = LSeq.lseq (limb l) (2 * v (nlimbs l))

let as_aff_point_nat_seq #l (p:aff_point_seq l) =
  BD.bn_v (LSeq.sub p 0 (v (nlimbs l))),
  BD.bn_v (LSeq.sub p (v (nlimbs l)) (v (nlimbs l)))

let aff_point_inv_seq #l (p:aff_point_seq l) =
  let x, y = as_aff_point_nat_seq p in
  x < S.prime /\ y < S.prime


inline_for_extraction noextract
let aff_point l = lbuffer (limb l) (2ul *. nlimbs l)

noextract
let as_aff_point_nat #l (h:mem) (p:aff_point l) =
  as_aff_point_nat_seq (as_seq h p)

noextract
let aff_point_inv #l (h:mem) (p:aff_point l) =
  aff_point_inv_seq (as_seq h p)

noextract
let aff_point_x_as_nat #l (h:mem) (p:aff_point l) : GTot nat =
  as_nat h (gsub p 0ul (nlimbs l))

noextract
let aff_point_y_as_nat #l (h:mem) (p:aff_point l) : GTot nat =
  as_nat h (gsub p (nlimbs l) (nlimbs l))

inline_for_extraction noextract
let aff_getx #l (p:aff_point l) : Stack (felem l)
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul (nlimbs l) /\ h0 == h1)
  = sub p 0ul (nlimbs l)

inline_for_extraction noextract
let aff_gety #l (p:aff_point l) : Stack (felem l)
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p (nlimbs l) (nlimbs l) /\ h0 == h1)
  = sub p (nlimbs l) (nlimbs l)


///  Projective coordinates

inline_for_extraction noextract
let point_seq (l:limb_t) = LSeq.lseq (limb l) (3 * v (nlimbs l))

let as_point_nat_seq #l (p:point_seq l) =
  BD.bn_v (LSeq.sub p 0 (v (nlimbs l))),
  BD.bn_v (LSeq.sub p (v (nlimbs l)) (v (nlimbs l))),
  BD.bn_v (LSeq.sub p (2 * v (nlimbs l)) (v (nlimbs l)))

let point_inv_seq #l (p:point_seq l) =
  let x, y, z = as_point_nat_seq p in
  x < S.prime /\ y < S.prime /\ z < S.prime


inline_for_extraction noextract
let point (l:limb_t) = lbuffer (limb l) (3ul *. nlimbs l)

noextract
let as_point_nat #l (h:mem) (p:point l) =
  as_point_nat_seq (as_seq h p)

noextract
let point_inv #l (h:mem) (p:point l) =
  point_inv_seq (as_seq h p)

noextract
let point_x_as_nat #l (h:mem) (p:point l) : GTot nat =
  as_nat h (gsub p 0ul (nlimbs l))

noextract
let point_y_as_nat #l (h:mem) (e:point l) : GTot nat =
  as_nat h (gsub e (nlimbs l) (nlimbs l))

noextract
let point_z_as_nat #l (h:mem) (e:point l) : GTot nat =
  as_nat h (gsub e (2ul *. nlimbs l) (nlimbs l))


inline_for_extraction noextract
let getx #l (p:point l) : Stack (felem l)
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul (nlimbs l) /\ h0 == h1)
  = sub p 0ul (nlimbs l)

inline_for_extraction noextract
let gety #l (p:point l) : Stack (felem l)
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p (nlimbs l) (nlimbs l) /\ h0 == h1)
  = sub p (nlimbs l) (nlimbs l)

inline_for_extraction noextract
let getz #l (p:point l) : Stack (felem l)
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p (2ul *. nlimbs l) (nlimbs l) /\ h0 == h1)
  = sub p (2ul *. nlimbs l) (nlimbs l)


///  Create a point

inline_for_extraction noextract
val create_aff_point: l:limb_t -> StackInline (aff_point l)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (2 * v (nlimbs l)) (limb_zero l)))


inline_for_extraction noextract
val create_point: l:limb_t -> StackInline (point l)
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (3 * v (nlimbs l)) (limb_zero l)))


val make_base_point: #l:limb_t -> p:point l -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\
    from_mont_point (as_point_nat h1 p) == S.base_point)


val make_point_at_inf: #l:limb_t -> p:point l -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ from_mont_point (as_point_nat h1 p) == S.point_at_inf)


///  Check if a point is a point-at-infinity

val is_point_at_inf: #l:limb_t -> p:point l -> Stack (limb l)
  (requires fun h -> live h p /\ point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (let pM = from_mont_point (as_point_nat h0 p) in
    (if S.is_point_at_inf pM then v r = ones_v l else v r = 0) /\
    (if S.is_point_at_inf (as_point_nat h0 p) then v r = ones_v l else v r = 0)))


val is_point_at_inf_vartime: #l:limb_t -> p:point l -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_at_inf (as_point_nat h0 p) /\
    r == S.is_point_at_inf (from_mont_point (as_point_nat h0 p)))


///  Create a copy of a point

inline_for_extraction noextract
val copy_point: #l:limb_t -> res:point l -> p:point l -> Stack unit
  (requires fun h -> live h p /\ live h res /\ disjoint p res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == as_seq h0 p)


///  Point conversion between Projective and Affine coordinates representations

// to_aff_point = S.to_aff_point + from_mont
val to_aff_point: #l:limb_t -> res:aff_point l -> p:point l -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_aff_point_nat h1 res == S.to_aff_point (from_mont_point (as_point_nat h0 p)))


// to_aff_point = S.to_aff_point + from_mont
val to_aff_point_x: #l:limb_t -> res:felem l -> p:point l -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == fst (S.to_aff_point (from_mont_point (as_point_nat h0 p))))


// to_proj_point = S.to_proj_point + to_mont
val to_proj_point: #l:limb_t -> res:point l -> p:aff_point l -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) == S.to_proj_point (as_aff_point_nat h0 p))


///  Check if a point is on the curve

val is_on_curve_vartime: #l:limb_t -> p:aff_point l -> Stack bool
  (requires fun h -> live h p /\ aff_point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_on_curve (as_aff_point_nat h0 p))


///  Point load and store functions

val aff_point_store: #l:limb_t -> res:lbuffer uint8 64ul -> p:aff_point l -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.aff_point_store (as_aff_point_nat h0 p))


val point_store: #l:limb_t -> res:lbuffer uint8 64ul -> p:point l -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.point_store (from_mont_point (as_point_nat h0 p)))


val aff_point_load_vartime: #l:limb_t -> res:aff_point l -> b:lbuffer uint8 64ul -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.aff_point_load (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (aff_point_inv h1 res /\ as_aff_point_nat h1 res == Some?.v ps))))


val load_point_vartime: #l:limb_t -> res:point l -> b:lbuffer uint8 64ul -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.load_point (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (point_inv h1 res /\
      from_mont_point (as_point_nat h1 res) == Some?.v ps))))


val aff_point_decompress_vartime (#l:limb_t) (x y:felem l) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    as_nat h1 x < S.prime /\ as_nat h1 y < S.prime /\ as_nat h1 x == xa /\ as_nat h1 y == ya)))
