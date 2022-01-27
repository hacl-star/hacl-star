module Hacl.Impl.K256.Point

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence

module S = Spec.K256
module BI = Hacl.Spec.K256.Field52
module BL = Hacl.Spec.K256.Field52.Lemmas

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
let point_nat (h:mem) (p:point) =
 (as_nat h (gsub p 0ul 5ul),
  as_nat h (gsub p 5ul 5ul),
  as_nat h (gsub p 10ul 5ul))


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

let create_point () =
  create (3ul *! 5ul) (u64 0)


///  Conversion functions between affine and projective coordinates

inline_for_extraction noextract
val to_proj_point (p:point) (x y:felem) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\ disjoint p x /\ disjoint p y /\
    inv_lazy_reduced2 h x /\ inv_lazy_reduced2 h y)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_inv h1 p /\
    point_nat h1 p == (as_nat h0 x, as_nat h0 y, S.one))

let to_proj_point p x y =
  let x1, y1, z1 = getx p, gety p, getz p in
  copy x1 x;
  copy y1 y;
  set_one z1


///  Is a point in affine coordinates on the curve

inline_for_extraction noextract
val is_on_curve_vartime (x y:felem) : Stack bool
  (requires fun h -> live h x /\ live h y /\
    inv_fully_reduced h x /\ inv_fully_reduced h y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.is_on_curve (as_nat h0 x, as_nat h0 y))

let is_on_curve_vartime x y =
  push_frame ();
  let y2 = create_felem () in
  let x3 = create_felem () in
  let b = create_felem () in

  let h = ST.get () in
  fsqr y2 y;
  fsqr x3 x;
  fmul x3 x3 x;
  let h0 = ST.get () in
  //assert (feval h0 y2 == S.fmul (feval h y) (feval h y));
  assert (felem_fits5 (as_felem5 h0 y2) (1,1,1,1,2));

  //assert (feval h0 x3 == S.fmul (S.fmul (feval h x) (feval h x)) (feval h x));
  assert (felem_fits5 (as_felem5 h0 x3) (1,1,1,1,2));

  make_u52_5 b (make_b_k256 ());
  let h0' = ST.get () in
  assert (as_nat h0' b == S.b);
  assert (felem_fits5 (as_felem5 h0' b) (1,1,1,1,1));

  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,1) (as_felem5 h0 x3) (as_felem5 h0' b);
  fadd x3 x3 b;
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 x3) (2,2,2,2,3));

  fnormalize x3 x3;
  fnormalize y2 y2;
  BL.normalize5_lemma (2,2,2,2,3) (as_felem5 h1 x3);
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h1 y2);

  let res = is_felem_eq_vartime y2 x3 in
  pop_frame ();
  res


inline_for_extraction noextract
val is_proj_point_at_inf_vartime: p:point -> Stack bool
  (requires fun h -> live h p /\ point_inv h p)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b = S.is_proj_point_at_inf (point_eval h0 p))

let is_proj_point_at_inf_vartime p =
  push_frame ();
  let tmp = create_felem () in
  let pz = getz p in

  let h0 = ST.get () in
  assert (inv_lazy_reduced2 h0 (gsub p 10ul 5ul));
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h0 pz);
  fnormalize tmp pz;
  let b = is_felem_zero_vartime tmp in
  pop_frame ();
  b
