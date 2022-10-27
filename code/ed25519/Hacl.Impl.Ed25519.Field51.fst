module Hacl.Impl.Ed25519.Field51

open FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open FStar.Mul

module LSeq = Lib.Sequence
module P = Hacl.Impl.Curve25519.Field51
module S = Spec.Curve25519

let felem = lbuffer uint64 5ul
let point = lbuffer uint64 20ul

let as_nat (h:mem) (f:felem) : GTot nat = P.as_nat h f

let fevalh (h:mem) (f:felem) : GTot S.elem = P.fevalh h f

noextract
val point_eval:h:mem -> p:point -> GTot Spec.Ed25519.ext_point
let point_eval h p =
  let x = gsub p 0ul 5ul in
  let y = gsub p 5ul 5ul in
  let z = gsub p 10ul 5ul in
  let t = gsub p 15ul 5ul in
  (fevalh h x, fevalh h y, fevalh h z, fevalh h t)

noextract
val felem_fits: h:mem -> f:felem -> m:Hacl.Spec.Curve25519.Field51.Definition.scale64_5 -> Type0
let felem_fits h f m = P.felem_fits h f m

noextract
let as_felem (h:mem) (f:felem) =
  P.as_felem h f

noextract
let mul_inv_t (h:mem) (f:felem) : GTot Type0 =
  P.mul_inv_t h f

noextract
let point_inv_t (h:mem) (p:point) : GTot Type0 =
  mul_inv_t h (gsub p 0ul 5ul) /\
  mul_inv_t h (gsub p 5ul 5ul) /\
  mul_inv_t h (gsub p 10ul 5ul) /\
  mul_inv_t h (gsub p 15ul 5ul)


unfold
let lseq_as_felem (a:LSeq.lseq uint64 5) : Hacl.Spec.Curve25519.Field51.Definition.felem5 =
  let open Lib.Sequence in
  (a.[0], a.[1], a.[2], a.[3], a.[4])

unfold
let refl_ext_point (a:LSeq.lseq uint64 20) : GTot Spec.Ed25519.ext_point =
  let open Hacl.Spec.Curve25519.Field51.Definition in
  let x = feval (lseq_as_felem (LSeq.sub a 0 5)) in
  let y = feval (lseq_as_felem (LSeq.sub a 5 5)) in
  let z = feval (lseq_as_felem (LSeq.sub a 10 5)) in
  let t = feval (lseq_as_felem (LSeq.sub a 15 5)) in
  (x, y, z, t)

unfold
let inv_ext_point (a:LSeq.lseq uint64 20) : Type0 =
  Spec.Ed25519.point_inv (refl_ext_point a)

unfold
let linv (a:LSeq.lseq uint64 20) : Type0 =
  let open Hacl.Spec.Curve25519.Field51 in
  mul_inv_t (lseq_as_felem (LSeq.sub a 0 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 5 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 10 5)) /\
  mul_inv_t (lseq_as_felem (LSeq.sub a 15 5)) /\
  inv_ext_point a
