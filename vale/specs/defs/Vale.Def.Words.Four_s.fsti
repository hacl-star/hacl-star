module Vale.Def.Words.Four_s
open Vale.Def.Words_s
open FStar.Mul

unfold let four_map (#a #b:Type) (f:a -> b) (x:four a) : four b =
  let Mkfour x0 x1 x2 x3 = x in
  Mkfour (f x0) (f x1) (f x2) (f x3)

unfold let four_map2 (#a #b:Type) (f:a -> a -> b) (x y:four a) : four b =
  let Mkfour x0 x1 x2 x3 = x in
  let Mkfour y0 y1 y2 y3 = y in
  Mkfour (f x0 y0) (f x1 y1) (f x2 y2) (f x3 y3)

let two_two_to_four (#a:Type) (x:two (two a)) : four a =
  let (Mktwo (Mktwo x0 x1) (Mktwo x2 x3)) = x in
  Mkfour x0 x1 x2 x3

let four_to_two_two (#a:Type) (x:four a) : two (two a) =
  let Mkfour x0 x1 x2 x3 = x in
  Mktwo (Mktwo x0 x1) (Mktwo x2 x3)

unfold
let nat_to_four_unfold (size:nat) (n:natN (pow2 (4 * size))) : four (natN (pow2 size)) =
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  Mkfour (n % n1) ((n / n1) % n1) ((n / n2) % n1) ((n / n3) % n1)

[@"opaque_to_smt"]
let nat_to_four (size:nat) (n:natN (pow2 (4 * size))) : four (natN (pow2 size)) =
  nat_to_four_unfold size n

unfold
let four_to_nat_unfold (size:nat) (x:four (natN (pow2 size))) : natN (pow2 (4 * size)) =
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let n3 = pow2_norm (3 * size) in
  let n4 = pow2_norm (4 * size) in
  let Mkfour x0 x1 x2 x3 = x in
  int_to_natN n4 (x0 + x1 * n1 + x2 * n2 + x3 * n3)

[@"opaque_to_smt"]
let four_to_nat (size:nat) (x:four (natN (pow2 size))) : natN (pow2 (4 * size)) =
  four_to_nat_unfold size x

let four_select (#a:Type) (x:four a) (selector:nat2) : a =
  match selector with
  | 0 -> x.lo0
  | 1 -> x.lo1
  | 2 -> x.hi2
  | 3 -> x.hi3

let four_insert (#a:Type) (x:four a) (y:a) (selector:nat2) : four a =
  match selector with
  | 0 -> Mkfour y x.lo1 x.hi2 x.hi3
  | 1 -> Mkfour x.lo0 y x.hi2 x.hi3
  | 2 -> Mkfour x.lo0 x.lo1 y x.hi3
  | 3 -> Mkfour x.lo0 x.lo1 x.hi2 y

let four_reverse (#a:Type) (x:four a) : four a =
  let Mkfour x0 x1 x2 x3 = x in
  Mkfour x3 x2 x1 x0
