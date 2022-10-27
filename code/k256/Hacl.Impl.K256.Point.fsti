module Hacl.Impl.K256.Point

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence

module S = Spec.K256
open Hacl.K256.Field

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Projective coordinates

// (_X, _Y, _Z)
inline_for_extraction noextract
let point = lbuffer uint64 15ul

inline_for_extraction noextract
let getx (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 5ul /\ h0 == h1)
  = sub p 0ul 5ul

inline_for_extraction noextract
let gety (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 5ul 5ul /\ h0 == h1)
  = sub p 5ul 5ul

inline_for_extraction noextract
let getz (p:point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 10ul 5ul /\ h0 == h1)
  = sub p 10ul 5ul


inline_for_extraction noextract
let as_felem5_lseq (s:LSeq.lseq uint64 5) : felem5 =
  let open Lib.Sequence in
  (s.[0],s.[1],s.[2],s.[3],s.[4])


inline_for_extraction noextract
let point_inv_lseq (p:LSeq.lseq uint64 15) =
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 0 5)) /\
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 5 5)) /\
  inv_lazy_reduced2_5 (as_felem5_lseq (LSeq.sub p 10 5))

inline_for_extraction noextract
let point_inv (h:mem) (p:point) =
  inv_lazy_reduced2 h (gsub p 0ul 5ul) /\
  inv_lazy_reduced2 h (gsub p 5ul 5ul) /\
  inv_lazy_reduced2 h (gsub p 10ul 5ul)


inline_for_extraction noextract
let point_eval_lseq (p:LSeq.lseq uint64 15) : GTot S.proj_point =
 (feval5 (as_felem5_lseq (LSeq.sub p 0 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 5 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 10 5)))

inline_for_extraction noextract
let point_eval (h:mem) (p:point) : GTot S.proj_point =
 (feval h (gsub p 0ul 5ul),
  feval h (gsub p 5ul 5ul),
  feval h (gsub p 10ul 5ul))


///  Create a point

inline_for_extraction noextract
val create_point: unit -> StackInline point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create (3 * v 5ul) (u64 0)))


val make_point_at_inf: p:point -> Stack unit
  (requires fun h -> live h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\ S.to_aff_point (point_eval h1 p) == S.aff_point_at_inf)


inline_for_extraction noextract
val make_g: g:point -> Stack unit
  (requires fun h -> live h g)
  (ensures  fun h0 _ h1 -> modifies (loc g) h0 h1 /\
    point_inv h1 g /\ point_eval h1 g == S.g)

///  Conversion functions between affine and projective coordinates

inline_for_extraction noextract
val to_proj_point (p:point) (x y:felem) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\ disjoint p x /\ disjoint p y /\
    inv_lazy_reduced2 h x /\ inv_lazy_reduced2 h y)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_inv h1 p /\
    point_eval h1 p == S.to_proj_point (feval h0 x, feval h0 y))


inline_for_extraction noextract
val to_aff_point (x y:felem) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\
    disjoint p x /\ disjoint p y /\ disjoint x y /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc x |+| loc y) h0 h1 /\
    inv_lazy_reduced2 h1 x /\ inv_lazy_reduced2 h1 y /\
    (feval h1 x, feval h1 y) == S.to_aff_point (point_eval h0 p))

///  Is a point in affine coordinates on the curve

inline_for_extraction noextract
val is_on_curve_vartime (x y:felem) : Stack bool
  (requires fun h -> live h x /\ live h y /\
    inv_fully_reduced h x /\ inv_fully_reduced h y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.is_on_curve (as_nat h0 x, as_nat h0 y))


inline_for_extraction noextract
val is_proj_point_at_inf_vartime: p:point -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b = S.is_proj_point_at_inf (point_eval h0 p))


val point_negate (out p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h out /\ eq_or_disjoint p out /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\ point_eval h1 out == S.point_negate (point_eval h0 p))


val point_eq (p q:point) : Stack bool
  (requires fun h ->
    live h p /\ live h q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    (z <==> S.point_equal (point_eval h0 p) (point_eval h0 q)))

///  Decompress / Compress

val aff_point_decompress_vartime (x y:felem) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    inv_fully_reduced h1 x /\ inv_fully_reduced h1 y /\ feval h1 x == xa /\ feval h1 y == ya)))


inline_for_extraction noextract
val point_decompress_vartime (p:point) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h p /\ live h s /\ disjoint p s)
  (ensures fun h0 b h1 -> modifies (loc p) h0 h1 /\
    (b <==> Some? (S.point_decompress (as_seq h0 s))) /\
    (b ==> (let (px, py, pz) = Some?.v (S.point_decompress (as_seq h0 s)) in
      inv_fully_reduced h1 (gsub p 0ul 5ul) /\ feval h1 (gsub p 0ul 5ul) == px /\
      inv_fully_reduced h1 (gsub p 5ul 5ul) /\ feval h1 (gsub p 5ul 5ul) == py /\
      inv_fully_reduced h1 (gsub p 10ul 5ul) /\ feval h1 (gsub p 10ul 5ul) == pz)))


val aff_point_compress_vartime (s:lbuffer uint8 33ul) (x y:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s /\
    inv_lazy_reduced2 h x /\ inv_lazy_reduced2 h y)
  (ensures fun h0 b h1 -> modifies (loc s |+| loc x |+| loc y) h0 h1 /\
    as_seq h1 s == S.aff_point_compress (feval h0 x, feval h0 y))


inline_for_extraction noextract
val point_compress_vartime (s:lbuffer uint8 33ul) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h s /\ disjoint p s /\
    point_inv h p)
  (ensures fun h0 b h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.point_compress (point_eval h0 p))
