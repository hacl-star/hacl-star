module Spec.EC.Projective

open FStar.Mul

include Spec.EC

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let proj_point (k:curve) =
  p:tuple3 nat nat nat{let (px, py, pz) = p in px < prime /\ py < prime /\ pz < prime}


let point_at_inf (k:curve) : proj_point k =
  (zero k, one k, zero k)

let is_point_at_inf (k:curve) (p:proj_point k) =
  let (_, _, z) = p in z = zero k


let to_proj_point (k:curve) (p:aff_point k) : proj_point k =
  let (x, y) = p in (x, y, one k)

let to_aff_point (k:curve) (p:proj_point k) : aff_point k =
  // if is_proj_point_at_inf p then aff_point_at_inf
  let (px, py, pz) = p in
  let zinv = finv k pz in
  let x = fmul k px zinv in
  let y = fmul k py zinv in
  (x, y)
