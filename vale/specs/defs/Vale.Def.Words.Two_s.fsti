module Vale.Def.Words.Two_s
open Vale.Def.Words_s
open FStar.Mul

unfold let two_map (#a #b:Type) (f:a -> b) (x:two a) : two b =
  let Mktwo x0 x1 = x in
  Mktwo (f x0) (f x1)

unfold let two_map2 (#a #b:Type) (f:a -> a -> b) (x y:two a) : two b =
  let Mktwo x0 x1 = x in
  let Mktwo y0 y1 = y in
  Mktwo (f x0 y0) (f x1 y1)

unfold
let nat_to_two_unfold (size:nat) (n:natN (pow2 (2 * size))) : two (natN (pow2 size)) =
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  Mktwo (n % n1) ((n / n1) % n1)

let nat_to_two (size:nat) (n:natN (pow2 (2 * size))) : two (natN (pow2 size)) =
  nat_to_two_unfold size n

unfold
let two_to_nat_unfold (size:nat) (x:two (natN (pow2 size))) : natN (pow2 (2 * size)) =
  let n1 = pow2_norm size in
  let n2 = pow2_norm (2 * size) in
  let Mktwo x0 x1 = x in
  int_to_natN n2 (x0 + x1 * n1)

let two_to_nat (size:nat) (x:two (natN (pow2 size))) : natN (pow2 (2 * size)) =
  two_to_nat_unfold size x

let two_select (#a:Type) (x:two a) (selector:nat1) : a =
  match selector with
  | 0 -> x.lo
  | 1 -> x.hi

let two_insert (#a:Type) (x:two a) (y:a) (selector:nat1) : two a =
  match selector with
  | 0 -> Mktwo y x.hi
  | 1 -> Mktwo x.lo y

let two_reverse (#a:Type) (x:two a) : two a =
  let Mktwo x0 x1 = x in
  Mktwo x1 x0
