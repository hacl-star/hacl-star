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
open Hacl.Impl.K256.Finv

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

let create_point () =
  create (3ul *! 5ul) (u64 0)


///  Conversion functions between affine and projective coordinates

inline_for_extraction noextract
val to_proj_point (p:point) (x y:felem) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\ disjoint p x /\ disjoint p y /\
    inv_lazy_reduced2 h x /\ inv_lazy_reduced2 h y)
  (ensures  fun h0 _ h1 -> modifies (loc p) h0 h1 /\ point_inv h1 p /\
    point_eval h1 p == S.to_proj_point (feval h0 x, feval h0 y))

let to_proj_point p x y =
  let x1, y1, z1 = getx p, gety p, getz p in
  copy x1 x;
  copy y1 y;
  set_one z1


inline_for_extraction noextract
val to_aff_point (x y:felem) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h x /\ live h y /\
    disjoint p x /\ disjoint p y /\ disjoint x y /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc x |+| loc y) h0 h1 /\
    inv_lazy_reduced2 h1 x /\ inv_lazy_reduced2 h1 y /\
    (feval h1 x, feval h1 y) == S.to_aff_point (point_eval h0 p))

let to_aff_point x y p =
  push_frame ();
  let x1, y1, z1 = getx p, gety p, getz p in
  let zinv = create_felem () in
  finv zinv z1;
  fmul x x1 zinv;
  fmul y y1 zinv;
  pop_frame ()


///  Is a point in affine coordinates on the curve

inline_for_extraction noextract
val compute_expected_y2 (y2 x:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y2 /\ disjoint x y2 /\
    inv_fully_reduced h x)
  (ensures  fun h0 _ h1 -> modifies (loc y2) h0 h1 /\
   (let xn = as_nat h0 x in inv_fully_reduced h1 y2 /\
   as_nat h1 y2 == S.fadd (S.fmul (S.fmul xn xn) xn) S.b))

let compute_expected_y2 y2 x =
  push_frame ();
  let b = create_felem () in

  fsqr y2 x;
  fmul y2 y2 x;
  make_u52_5 b (make_b_k256 ());
  let h0 = ST.get () in
  assert (inv_lazy_reduced2 h0 y2);
  assert (inv_fully_reduced h0 b);

  BL.fadd5_lemma (1,1,1,1,2) (1,1,1,1,1) (as_felem5 h0 y2) (as_felem5 h0 b);
  fadd y2 y2 b;
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 y2) (2,2,2,2,3));

  fnormalize y2 y2;
  BL.normalize5_lemma (2,2,2,2,3) (as_felem5 h1 y2);
  pop_frame ()


inline_for_extraction noextract
val is_y_sqr_is_y2_vartime (y2 y:felem) : Stack bool
  (requires fun h ->
    live h y /\ live h y2 /\ disjoint y y2 /\
    inv_fully_reduced h y2 /\ inv_fully_reduced h y)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == (as_nat h0 y2 = S.fmul (as_nat h0 y) (as_nat h0 y)))

let is_y_sqr_is_y2_vartime y2 y =
  push_frame ();
  let y2_comp = create_felem () in

  fsqr y2_comp y;
  let h0 = ST.get () in
  assert (inv_lazy_reduced2 h0 y2);
  fnormalize y2_comp y2_comp;
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h0 y2_comp);

  let res = is_felem_eq_vartime y2 y2_comp in
  pop_frame ();
  res


inline_for_extraction noextract
val is_on_curve_vartime (x y:felem) : Stack bool
  (requires fun h -> live h x /\ live h y /\
    inv_fully_reduced h x /\ inv_fully_reduced h y)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.is_on_curve (as_nat h0 x, as_nat h0 y))

let is_on_curve_vartime x y =
  push_frame ();
  let y2_exp = create_felem () in
  compute_expected_y2 y2_exp x;
  let res = is_y_sqr_is_y2_vartime y2_exp y in
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


inline_for_extraction noextract
val recover_y_vartime (y x:felem) (is_odd:bool) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ disjoint x y /\
    inv_fully_reduced h x /\ 0 < as_nat h x)
  (ensures fun h0 b h1 -> modifies (loc y) h0 h1 /\
    (b <==> Some? (S.recover_y (as_nat h0 x) is_odd)) /\
    (b ==> (inv_fully_reduced h1 y /\
      as_nat h1 y == Some?.v (S.recover_y (as_nat h0 x) is_odd))))

let recover_y_vartime y x is_odd =
  push_frame ();
  let y2 = create_felem () in
  compute_expected_y2 y2 x; //y2 = x *% x *% x +% b
  fsqrt y y2;
  let h = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h y);
  fnormalize y y;

  let is_y_valid = is_y_sqr_is_y2_vartime y2 y in
  let res =
    if not is_y_valid then false
    else begin
      let is_y_odd = is_fodd_vartime y in
      fnegate_conditional_vartime y (is_y_odd <> is_odd);
      true end in
  pop_frame ();
  res


val aff_point_decompress_vartime (x y:felem) (s:lbuffer uint8 33ul) : Stack bool
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s)
  (ensures fun h0 b h1 -> modifies (loc x |+| loc y) h0 h1 /\
    (b <==> Some? (S.aff_point_decompress (as_seq h0 s))) /\
    (b ==> (let (xa, ya) = Some?.v (S.aff_point_decompress (as_seq h0 s)) in
    inv_fully_reduced h1 x /\ inv_fully_reduced h1 y /\ feval h1 x == xa /\ feval h1 y == ya)))

let aff_point_decompress_vartime x y s =
  let s0 = s.(0ul) in
  if not (Lib.RawIntTypes.u8_to_UInt8 s0 = 0x02uy ||
    Lib.RawIntTypes.u8_to_UInt8 s0 = 0x03uy) then false
  else begin
    let xb = sub s 1ul 32ul in
    let is_x_valid = load_felem_vartime x xb in
    let is_y_odd = Lib.RawIntTypes.u8_to_UInt8 s0 = 0x03uy in

    if not is_x_valid then false
    else recover_y_vartime y x is_y_odd end


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

let point_decompress_vartime p s =
  let px, py, pz = getx p, gety p, getz p in
  let b = aff_point_decompress_vartime px py s in
  set_one pz;
  b


val aff_point_compress_vartime (s:lbuffer uint8 33ul) (x y:felem) : Stack unit
  (requires fun h ->
    live h x /\ live h y /\ live h s /\
    disjoint x y /\ disjoint x s /\ disjoint y s /\
    inv_lazy_reduced2 h x /\ inv_lazy_reduced2 h y)
  (ensures fun h0 b h1 -> modifies (loc s |+| loc x |+| loc y) h0 h1 /\
    as_seq h1 s == S.aff_point_compress (feval h0 x, feval h0 y))

let aff_point_compress_vartime s x y =
  let h = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h y);
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h x);
  fnormalize y y;
  fnormalize x x;

  let is_y_odd = is_fodd_vartime y in
  let h0 = ST.get () in
  s.(0ul) <- if is_y_odd then u8 0x03 else u8 0x02;
  let h1 = ST.get () in
  update_sub_f h1 s 1ul 32ul
    (fun h -> BSeq.nat_to_bytes_be 32 (feval h1 x))
    (fun _ -> store_felem (sub s 1ul 32ul) x);
  let h2 = ST.get () in
  LSeq.eq_intro (as_seq h2 s) (S.aff_point_compress (feval h x, feval h y))


inline_for_extraction noextract
val point_compress_vartime (s:lbuffer uint8 33ul) (p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h s /\ disjoint p s /\
    point_inv h p)
  (ensures fun h0 b h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == S.point_compress (point_eval h0 p))

let point_compress_vartime s p =
  push_frame ();
  let xa = create_felem () in
  let ya = create_felem () in
  to_aff_point xa ya p;
  aff_point_compress_vartime s xa ya;
  pop_frame ()


val point_negate (out p:point) : Stack unit
  (requires fun h ->
    live h p /\ live h out /\ eq_or_disjoint p out /\
    point_inv h p)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    point_inv h1 out /\ point_eval h1 out == S.point_negate (point_eval h0 p))

let point_negate out p =
  let h0 = ST.get () in
  let px, py, pz = getx p, gety p, getz p in
  let ox, oy, oz = getx out, gety out, getz out in
  copy_felem ox px;
  copy_felem oz pz;

  BL.fnegate5_lemma (1,1,1,1,2) (as_felem5 h0 py) (u64 2);
  make_u52_5 oy (BI.fnegate5 (py.(0ul), py.(1ul), py.(2ul), py.(3ul), py.(4ul)) (u64 2));
  let h1 = ST.get () in
  assert (felem_fits5 (as_felem5 h1 oy) (4,4,4,4,4));
  assert (as_nat h1 oy == 4 * S.prime - as_nat h0 py);
  BL.normalize_weak5_lemma (4,4,4,4,4) (as_felem5 h1 oy);
  fnormalize_weak oy oy;
  let h2 = ST.get () in
  assert (feval h2 ox == feval h0 px);
  assert (feval h2 oz == feval h0 pz);
  assert (feval h2 oy == (4 * S.prime - as_nat h0 py) % S.prime);
  Math.Lemmas.modulo_addition_lemma (- as_nat h0 py) S.prime 4;
  Math.Lemmas.lemma_mod_sub_distr 0 (as_nat h0 py) S.prime;
  assert (feval h2 oy == (- feval h0 py) % S.prime)


val fmul_fmul_eq_vartime (a bz c dz: felem) : Stack bool
  (requires fun h ->
    live h a /\ live h bz /\ live h c /\ live h dz /\
    eq_or_disjoint a bz /\ eq_or_disjoint c dz /\
    inv_lazy_reduced2 h a /\ inv_lazy_reduced2 h bz /\
    inv_lazy_reduced2 h c /\ inv_lazy_reduced2 h dz)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    z == (S.fmul (feval h0 a) (feval h0 bz) = S.fmul (feval h0 c) (feval h0 dz)))

[@CInline]
let fmul_fmul_eq_vartime a bz c dz =
  push_frame ();
  let a_bz = create_felem () in
  let c_dz = create_felem () in
  fmul a_bz a bz;
  fmul c_dz c dz;
  let h1 = ST.get () in
  fnormalize a_bz a_bz;
  fnormalize c_dz c_dz;
  let h2 = ST.get () in
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h1 a_bz);
  BL.normalize5_lemma (1,1,1,1,2) (as_felem5 h1 c_dz);
  let z = is_felem_eq_vartime a_bz c_dz in
  pop_frame ();
  z


val point_eq (p q:point) : Stack bool
  (requires fun h ->
    live h p /\ live h q /\ eq_or_disjoint p q /\
    point_inv h p /\ point_inv h q)
  (ensures  fun h0 z h1 -> modifies0 h0 h1 /\
    (z <==> S.point_equal (point_eval h0 p) (point_eval h0 q)))

let point_eq p q =
  let px, py, pz = getx p, gety p, getz p in
  let qx, qy, qz = getx q, gety q, getz q in

  let z0 = fmul_fmul_eq_vartime px qz qx pz in
  if not z0 then false
  else begin
    let z1 = fmul_fmul_eq_vartime py qz qy pz in
    if not z1 then false else true end
