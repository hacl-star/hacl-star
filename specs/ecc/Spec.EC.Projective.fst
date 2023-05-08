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


let point_negate (k:curve) (p:proj_point k) : proj_point k =
  let x, y, z = p in
  x, (-y) % prime, z


// Alg 4 from https://eprint.iacr.org/2015/1060.pdf
let point_add_a3 (k:curve{k.coeff_a = (-3) % k.prime}) (p q:proj_point k) : proj_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in

  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let t0 = x1 *% x2 in
  let t1 = y1 *% y2 in
  let t2 = z1 *% z2 in
  let t3 = x1 +% y1 in
  let t4 = x2 +% y2 in
  let t3 = t3 *% t4 in
  let t4 = t0 +% t1 in
  let t3 = t3 -% t4 in
  let t4 = y1 +% z1 in
  let t5 = y2 +% z2 in
  let t4 = t4 *% t5 in
  let t5 = t1 +% t2 in
  let t4 = t4 -% t5 in
  let x3 = x1 +% z1 in
  let y3 = x2 +% z2 in
  let x3 = x3 *% y3 in
  let y3 = t0 +% t2 in
  let y3 = x3 -% y3 in
  let z3 = k.coeff_b *% t2 in
  let x3 = y3 -% z3 in
  let z3 = x3 +% x3 in
  let x3 = x3 +% z3 in
  let z3 = t1 -% x3 in
  let x3 = t1 +% x3 in
  let y3 = k.coeff_b *% y3 in
  let t1 = t2 +% t2 in
  let t2 = t1 +% t2 in
  let y3 = y3 -% t2 in
  let y3 = y3 -% t0 in
  let t1 = y3 +% y3 in
  let y3 = t1 +% y3 in
  let t1 = t0 +% t0 in
  let t0 = t1 +% t0 in
  let t0 = t0 -% t2 in
  let t1 = t4 *% y3 in
  let t2 = t0 *% y3 in
  let y3 = x3 *% z3 in
  let y3 = y3 +% t2 in
  let x3 = t3 *% x3 in
  let x3 = x3 -% t1 in
  let z3 = t4 *% z3 in
  let t1 = t3 *% t0 in
  let z3 = z3 +% t1 in
  (x3, y3, z3)


// Alg 6 from https://eprint.iacr.org/2015/1060.pdf
let point_double_a3 (k:curve{k.coeff_a = (-3) % k.prime}) (p:proj_point k) : proj_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in

  let (x, y, z) = p in
  let t0 = x *% x in
  let t1 = y *% y in
  let t2 = z *% z in
  let t3 = x *% y in
  let t3 = t3 +% t3 in
  let t4 = y *% z in
  let z3 = x *% z in
  let z3 = z3 +% z3 in
  let y3 = k.coeff_b *% t2 in
  let y3 = y3 -% z3 in
  let x3 = y3 +% y3 in
  let y3 = x3 +% y3 in
  let x3 = t1 -% y3 in
  let y3 = t1 +% y3 in
  let y3 = x3 *% y3 in
  let x3 = x3 *% t3 in
  let t3 = t2 +% t2 in
  let t2 = t2 +% t3 in
  let z3 = k.coeff_b *% z3 in
  let z3 = z3 -% t2 in
  let z3 = z3 -% t0 in
  let t3 = z3 +% z3 in
  let z3 = z3 +% t3 in
  let t3 = t0 +% t0 in
  let t0 = t3 +% t0 in
  let t0 = t0 -% t2 in
  let t0 = t0 *% z3 in
  let y3 = y3 +% t0 in
  let t0 = t4 +% t4 in
  let z3 = t0 *% z3 in
  let x3 = x3 -% z3 in
  let z3 = t0 *% t1 in
  let z3 = z3 +% z3 in
  let z3 = z3 +% z3 in
  (x3, y3, z3)


let point_add_a0 (k:curve{k.coeff_a = 0}) (p q:proj_point k) : proj_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in

  let x1, y1, z1 = p in
  let x2, y2, z2 = q in
  let xx = x1 *% x2 in
  let yy = y1 *% y2 in
  let zz = z1 *% z2 in
  let xy_pairs = (x1 +% y1) *% (x2 +% y2) -% (xx +% yy) in
  let yz_pairs = (y1 +% z1) *% (y2 +% z2) -% (yy +% zz) in
  let xz_pairs = (x1 +% z1) *% (x2 +% z2) -% (xx +% zz) in
  let bzz3 = 3 *% k.coeff_b *% zz in
  let yy_m_bzz3 = yy -% bzz3 in
  let yy_p_bzz3 = yy +% bzz3 in
  let byz3 = 3 *% k.coeff_b *% yz_pairs in
  let xx3 = 3 *% xx in
  let bxx9 = 3 *% k.coeff_b *% xx3 in
  let x3 = xy_pairs *% yy_m_bzz3 -% byz3 *% xz_pairs in
  let y3 = yy_p_bzz3 *% yy_m_bzz3 +% bxx9 *% xz_pairs in
  let z3 = yz_pairs *% yy_p_bzz3 +% xx3 *% xy_pairs in
  x3, y3, z3


let point_double_a0 (k:curve{k.coeff_a = 0}) (p:proj_point k) : proj_point k =
  let ( +% ) = fadd k in
  let ( -% ) = fsub k in
  let ( *% ) = fmul k in

  let x, y, z = p in
  let yy = y *% y in
  let zz = z *% z in
  let xy2 = 2 *% x *% y in
  let bzz3 = 3 *% k.coeff_b *% zz in
  let bzz9 = 3 *% bzz3 in
  let yy_m_bzz9 = yy -% bzz9 in
  let yy_p_bzz3 = yy +% bzz3 in
  let yy_zz = yy *% zz in
  let t = 24 *% k.coeff_b *% yy_zz in
  let x3 = xy2 *% yy_m_bzz9 in
  let y3 = yy_m_bzz9 *% yy_p_bzz3 +% t in
  let z3 = yy *% y *% z *% 8 in
  x3, y3, z3
