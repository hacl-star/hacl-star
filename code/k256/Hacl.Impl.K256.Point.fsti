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

inline_for_extraction noextract
let as_felem5_lseq (s:LSeq.lseq uint64 5) : felem5 =
  let open Lib.Sequence in
  (s.[0],s.[1],s.[2],s.[3],s.[4])


///  Affine coordinates

inline_for_extraction noextract
let aff_point_seq = LSeq.lseq uint64 10

let aff_point_inv_seq (p:aff_point_seq) =
  inv_fully_reduced5 (as_felem5_lseq (LSeq.sub p 0 5)) /\
  inv_fully_reduced5 (as_felem5_lseq (LSeq.sub p 5 5))

let aff_point_eval_seq (p:aff_point_seq{aff_point_inv_seq p}) : S.aff_point =
  as_nat5 (as_felem5_lseq (LSeq.sub p 0 5)),
  as_nat5 (as_felem5_lseq (LSeq.sub p 5 5))

inline_for_extraction noextract
let aff_point = lbuffer uint64 10ul

noextract
let aff_point_inv (h:mem) (p:aff_point) =
  aff_point_inv_seq (as_seq h p)

noextract
let aff_point_eval (h:mem) (p:aff_point{aff_point_inv h p}) : GTot S.aff_point =
  aff_point_eval_seq (as_seq h p)


inline_for_extraction noextract
let aff_getx (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 0ul 5ul /\ h0 == h1)
  = sub p 0ul 5ul

inline_for_extraction noextract
let aff_gety (p:aff_point) : Stack felem
  (requires fun h -> live h p)
  (ensures fun h0 f h1 -> f == gsub p 5ul 5ul /\ h0 == h1)
  = sub p 5ul 5ul


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
  feval5 (as_felem5_lseq (LSeq.sub p 0 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 5 5)),
  feval5 (as_felem5_lseq (LSeq.sub p 10 5))

inline_for_extraction noextract
let point_eval (h:mem) (p:point) : GTot S.proj_point =
  feval h (gsub p 0ul 5ul),
  feval h (gsub p 5ul 5ul),
  feval h (gsub p 10ul 5ul)


///  Create a point

inline_for_extraction noextract
val create_aff_point: unit -> StackInline aff_point
  (requires fun h -> True)
  (ensures  fun h0 f h1 ->
    stack_allocated f h0 h1 (LSeq.create 10 (u64 0)))


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


inline_for_extraction noextract
val copy_point (out p:point) : Stack unit
  (requires fun h ->
    live h out /\ live h p /\ eq_or_disjoint out p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == point_eval h0 p)


///  Conversion functions between affine and projective coordinates

inline_for_extraction noextract
val to_proj_point (p:point) (p_aff:aff_point) : Stack unit
  (requires fun h ->
    live h p /\ live h p_aff /\ disjoint p p_aff /\
    aff_point_inv h p_aff)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_inv h1 p /\
    point_eval h1 p == S.to_proj_point (aff_point_eval h0 p_aff))


val to_aff_point (p_aff:aff_point) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h p_aff /\ disjoint p p_aff /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc p_aff) h0 h1 /\
    aff_point_inv h1 p_aff /\
    aff_point_eval h1 p_aff == S.to_aff_point (point_eval h0 p))


val to_aff_point_x (x:felem) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ disjoint p x /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc x) h0 h1 /\
    inv_fully_reduced h1 x /\
    as_nat h1 x == fst (S.to_aff_point (point_eval h0 p)))


///  Is a point in affine coordinates on the curve

val is_on_curve_vartime (p:aff_point) : Stack bool
  (requires fun h ->
    live h p /\ aff_point_inv h p)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.is_on_curve (aff_point_eval h0 p))


inline_for_extraction noextract
val is_proj_point_at_inf_vartime: p:point -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b = S.is_proj_point_at_inf (point_eval h0 p))


///  Point negation

val point_negate (out p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h out /\ eq_or_disjoint p out /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\ point_eval h1 out == S.point_negate (point_eval h0 p))


val point_negate_conditional_vartime: p:point -> is_negate:bool -> Stack unit
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\
    point_inv h1 p /\
    point_eval h1 p ==
      (if is_negate then S.point_negate (point_eval h0 p) else point_eval h0 p))


///  Point load and store functions

val aff_point_store: res:lbuffer uint8 64ul -> p:aff_point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    aff_point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.aff_point_store (aff_point_eval h0 p))


val point_store: res:lbuffer uint8 64ul -> p:point -> Stack unit
  (requires fun h ->
    live h res /\ live h p /\ disjoint res p /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.point_store (point_eval h0 p))


val aff_point_load_vartime: res:aff_point -> b:lbuffer uint8 64ul -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.aff_point_load (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (aff_point_inv h1 res /\ aff_point_eval h1 res == Some?.v ps))))


val load_point_vartime: res:point -> b:lbuffer uint8 64ul -> Stack bool
  (requires fun h ->
    live h res /\ live h b /\ disjoint res b)
  (ensures  fun h0 r h1 -> modifies (loc res) h0 h1 /\
    (let ps = S.load_point (as_seq h0 b) in
    (r <==> Some? ps) /\ (r ==> (point_inv h1 res /\ point_eval h1 res == Some?.v ps))))


inline_for_extraction noextract
val load_point_nocheck: out:point -> b:lbuffer uint8 64ul -> Stack unit
  (requires fun h ->
    live h out /\ live h b /\ disjoint out b /\
    S.point_inv_bytes (as_seq h b))
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\
    point_eval h1 out == S.load_point_nocheck (as_seq h0 b))


val aff_point_decompress_vartime (x y:felem) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    inv_fully_reduced h1 x /\ inv_fully_reduced h1 y /\ feval h1 x == xa /\ feval h1 y == ya)))
