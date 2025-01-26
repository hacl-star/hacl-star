module Hacl.Impl.PCurves.Point

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Field

module S = Spec.PCurves
module SM = Hacl.Spec.PCurves.Montgomery
module BD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence
module CC = Hacl.Impl.PCurves.Constants
module FI = Hacl.Impl.PCurves.InvSqrt

#set-options "--z3rlimit 70 --fuel 0 --ifuel 0"

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let from_mont_point {| S.curve_params |} (a:tuple3 nat nat nat) : S.proj_point =
  let x, y, z = a in SM.from_mont x, SM.from_mont y, SM.from_mont z


///  Affine coordinates

inline_for_extraction noextract
let aff_point_seq {| cp:S.curve_params |} = LSeq.lseq uint64 (2 * v cp.bn_limbs)

inline_for_extraction noextract
let as_aff_point_nat_seq {| cp:S.curve_params |} (p:aff_point_seq) =
  BD.bn_v (LSeq.sub p 0 (v cp.bn_limbs)),
  BD.bn_v (LSeq.sub p (v cp.bn_limbs) (v cp.bn_limbs))

inline_for_extraction noextract
let aff_point_inv_seq {| S.curve_params |} (p:aff_point_seq) =
  let x, y = as_aff_point_nat_seq p in
  x < S.prime /\ y < S.prime

inline_for_extraction noextract
let aff_point {| cp:S.curve_params |} = lbuffer uint64 (2ul *! S.bn_limbs)

noextract
let as_aff_point_nat {| cp:S.curve_params |} (h:mem) (p:aff_point) =
  as_aff_point_nat_seq (as_seq h p)

noextract
let aff_point_inv {| S.curve_params |} (h:mem) (p:aff_point) =
  aff_point_inv_seq (as_seq h p)

noextract
let as_aff_point_nat_inv {| cp:S.curve_params |} (h:mem) (p:aff_point{aff_point_inv h p}) : GTot S.aff_point  =
  let (x,y)= as_aff_point_nat h p in (x,y)

noextract
let aff_point_x_as_nat {| cp:S.curve_params |} (h:mem) (p:aff_point) : GTot nat =
  as_nat h (gsub p 0ul cp.bn_limbs)

noextract
let aff_point_y_as_nat {| cp:S.curve_params |} (h:mem) (p:aff_point) : GTot nat =
  as_nat h (gsub p cp.bn_limbs cp.bn_limbs)

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let aff_getx {| cp:S.curve_params |} (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> v cp.bn_limbs <= 2 * v cp.bn_limbs /\
  	       	       	  f == gsub p 0ul cp.bn_limbs /\
			  h0 == h1 /\ live h1 f)
  = sub p 0ul cp.bn_limbs

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let aff_gety {| cp:S.curve_params |} (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> v cp.bn_limbs + v cp.bn_limbs <= v (2ul *! cp.bn_limbs) /\
  	   f == gsub p cp.bn_limbs cp.bn_limbs /\
	   h0 == h1 /\ live h1 f)
  = sub p cp.bn_limbs cp.bn_limbs


///  Projective coordinates

inline_for_extraction noextract
let point_seq {| cp:S.curve_params |} = LSeq.lseq uint64 (3 * v cp.bn_limbs)

noextract
let as_point_nat_seq {| cp:S.curve_params |} (p:point_seq) =
  BD.bn_v (LSeq.sub p 0 (v cp.bn_limbs)),
  BD.bn_v (LSeq.sub p (v cp.bn_limbs) (v cp.bn_limbs)),
  BD.bn_v (LSeq.sub p (2 * v cp.bn_limbs) (v cp.bn_limbs))

noextract
let point_inv_seq {| S.curve_params |} (p:point_seq) =
  let x, y, z = as_point_nat_seq p in
  x < S.prime /\ y < S.prime /\ z < S.prime


inline_for_extraction noextract
let point {| cp:S.curve_params |} = lbuffer uint64 (3ul *! cp.bn_limbs)

noextract
let as_point_nat {| cp:S.curve_params |} (h:mem) (p:point) =
  as_point_nat_seq (as_seq h p)

noextract
let point_inv {| S.curve_params |} (h:mem) (p:point) =
  point_inv_seq (as_seq h p)

noextract
let as_point_nat_inv {| cp:S.curve_params |} (h:mem) (p:point{point_inv h p}) : GTot S.proj_point =
  let (x,y,z) = as_point_nat h p  in (x,y,z)

noextract
let point_x_as_nat {| cp:S.curve_params |} (h:mem) (p:point) : GTot nat =
  as_nat h (gsub p 0ul cp.bn_limbs)

noextract
let point_y_as_nat {| cp:S.curve_params |} (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e cp.bn_limbs cp.bn_limbs)

noextract
let point_z_as_nat {| cp:S.curve_params |} (h:mem) (e:point) : GTot nat =
  as_nat h (gsub e (2ul *! cp.bn_limbs) (cp.bn_limbs))


[@(strict_on_arguments [0])]
inline_for_extraction noextract
let getx {| cp:S.curve_params |} (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul cp.bn_limbs /\ h0 == h1)
  = sub p 0ul cp.bn_limbs

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let gety {| cp:S.curve_params |} (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 ->
  	   2 * v cp.bn_limbs <= v (3ul *! cp.bn_limbs) /\
  	   f == gsub p cp.bn_limbs cp.bn_limbs /\ h0 == h1)
  = sub p cp.bn_limbs cp.bn_limbs

[@(strict_on_arguments [0])]
inline_for_extraction noextract
let getz {| cp:S.curve_params |} (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> v (2ul *! cp.bn_limbs) == 2 * v cp.bn_limbs /\
   	       	       v (3ul *! cp.bn_limbs) == 3 * v cp.bn_limbs /\
                       f == gsub p (2ul *! cp.bn_limbs) (cp.bn_limbs) /\ h0 == h1)
  = sub p (2ul *! cp.bn_limbs) (cp.bn_limbs)

///  Create a point

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val create_aff_point: {| cp:S.curve_params |} -> StackInline aff_point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (2 * v cp.bn_limbs) (u64 0)))


[@(strict_on_arguments [0])]
inline_for_extraction noextract
val create_point: {| cp:S.curve_params |} -> StackInline point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (3 * v cp.bn_limbs) (u64 0)))


[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val make_base_point {| S.curve_params |} {| bn_ops |} {| CC.curve_constants |}:
  p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ from_mont_point (as_point_nat h1 p) == S.base_point)


[@(strict_on_arguments [0;1])]
inline_for_extraction noextract
val make_point_at_inf {| S.curve_params |} {| bn_ops |} {| CC.curve_constants |}:
  p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ from_mont_point (as_point_nat h1 p) == S.point_at_inf)


///  Check if a point is a point-at-infinity

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val is_point_at_inf {| S.curve_params |} {| bn_ops |}:
  p:point -> Stack uint64
  (requires fun h -> live h p /\ point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (let pM = from_mont_point (as_point_nat h0 p) in
    (if S.is_point_at_inf pM then v r = ones_v U64 else v r = 0) /\
    (if S.is_point_at_inf (as_point_nat_inv h0 p) then v r = ones_v U64 else v r = 0)))


[@(strict_on_arguments [0])]
inline_for_extraction noextract
val is_point_at_inf_vartime {| S.curve_params |} {| bn_ops |}:
  p:point -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_point_at_inf (as_point_nat_inv h0 p) /\
    r == S.is_point_at_inf (from_mont_point (as_point_nat h0 p)))


///  Create a copy of a point

[@(strict_on_arguments [0])]
inline_for_extraction noextract
val copy_point: {| S.curve_params |} -> res:point -> p:point -> Stack unit
  (requires fun h -> live h p /\ live h res /\ disjoint p res)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == as_seq h0 p)


///  Point conversion between Projective and Affine coordinates representations

// to_aff_point = S.to_aff_point + from_mont

[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val to_aff_point {| S.curve_params |} {| bn_ops |} {| CC.curve_constants |} {| field_ops |} {| FI.curve_inv_sqrt|}:
  res:aff_point -> p:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    aff_point_inv h1 res /\
    as_aff_point_nat_inv h1 res == S.to_aff_point (from_mont_point (as_point_nat h0 p)))


// to_aff_point = S.to_aff_point + from_mont
[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val to_aff_point_x {| S.curve_params |} {| bn_ops |} {| CC.curve_constants |} {| field_ops |} {| FI.curve_inv_sqrt|}:
  res:felem -> p:point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ eq_or_disjoint p res /\
    point_inv h p)
  (ensures fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_nat h1 res == fst (S.to_aff_point (from_mont_point (as_point_nat h0 p))))


// to_proj_point = S.to_proj_point + to_mont
[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val to_proj_point {| S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| field_ops |} :
  res:point -> p:aff_point -> Stack unit
  (requires fun h ->
    live h p /\ live h res /\ disjoint p res /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    point_inv h1 res /\
    from_mont_point (as_point_nat h1 res) == S.to_proj_point (as_aff_point_nat_inv h0 p))


///  Check if a point is on the curve

[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val is_on_curve_vartime {| S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |}:
  p:aff_point -> Stack bool
  (requires fun h -> live h p /\ aff_point_inv h p)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    r == S.is_on_curve (as_aff_point_nat_inv h0 p))


///  Point load and store functions

[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val aff_point_store {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |}:
  res:lbuffer uint8 (2ul *! size cp.bytes) -> p:aff_point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.aff_point_store (as_aff_point_nat_inv h0 p))


[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction noextract
val point_store {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |} {| FI.curve_inv_sqrt|}:
  res:lbuffer uint8 (2ul *! size cp.bytes) -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.point_store (from_mont_point (as_point_nat h0 p)))


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val aff_point_load_vartime {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |}:
  res:aff_point -> b:lbuffer uint8 (2ul *! size cp.bytes) -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.aff_point_load (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (aff_point_inv h1 res /\ as_aff_point_nat_inv h1 res == Some?.v ps))))


[@(strict_on_arguments [0;1;2;3])]
inline_for_extraction noextract
val load_point_vartime {| cp:S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |}:
  res:point -> b:lbuffer uint8 (2ul *! size cp.bytes) -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.load_point (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (point_inv h1 res /\
      from_mont_point (as_point_nat h1 res) == Some?.v ps))))


[@(strict_on_arguments [0;1;2;3;4])]
inline_for_extraction noextract
val aff_point_decompress_vartime {| S.curve_params |}  {| bn_ops |} {| CC.curve_constants |} {| f:field_ops |} {| FI.curve_inv_sqrt |}
  (x y:felem) (s:lbuffer uint8 (1ul +. (size S.bytes))) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    as_nat h1 x < S.prime /\ as_nat h1 y < S.prime /\ as_nat h1 x == xa /\ as_nat h1 y == ya)))
