module Spec.Lib.IntVec

open FStar.Mul
open Spec.Lib.IntSeq
module Ints = Spec.Lib.IntTypes

type intvec (vt:vectype) = lseq (Ints.uint_t vt.it) vt.len

let intvec_v #vt v =
  ghost_map Ints.uint_v v

let vec_add #vt (v1:intvec vt) (v2:intvec vt) : intvec vt =
map2 (Ints.add_mod #vt.it) v1 v2

let vec_sub #vt (v1:intvec vt) (v2:intvec vt) : intvec vt =
map2 (Ints.sub_mod #vt.it) v1 v2

let vec_mul #vt (v1:intvec vt) (v2:intvec vt): intvec vt =
map2 (Ints.mul_mod #vt.it) v1 v2

let vec_xor #vt (v1:intvec vt) (v2:intvec vt) : intvec vt =
map2 (Ints.logxor #vt.it) v1 v2

let vec_and #vt (v1:intvec vt) (v2:intvec vt) : intvec vt =
map2 (Ints.logand #vt.it) v1 v2

let vec_or #vt (v1:intvec vt) (v2:intvec vt) : intvec vt =
map2 (Ints.logor #vt.it) v1 v2

let vec_not #vt (v1:intvec vt) : intvec vt =
map (Ints.lognot #vt.it) v1

let vec_shift_right #vt v1 s =
map (fun x -> Ints.shift_right x s) v1

let vec_shift_left #vt v1 s =
map (fun x -> Ints.shift_left #vt.it x s) v1

let vec_rotate_right #vt v1 s =
map (fun x -> Ints.rotate_right  #vt.it x s) v1

let vec_rotate_left #vt v1 s =
map (fun x -> Ints.rotate_left #vt.it x s) v1

let op_Plus_Bar = vec_add
let op_Subtraction_Bar = vec_sub
let op_Star_Bar = vec_mul
let op_Hat_Bar = vec_xor
let op_Amp_Bar = vec_and
let op_Bar_Bar = vec_or
let op_Tilde_Bar = vec_not
let op_Greater_Greater_Bar = vec_shift_right
let op_Less_Less_Bar = vec_shift_left
let op_Greater_Greater_Greater_Bar = vec_rotate_right
let op_Less_Less_Less_Bar = vec_rotate_left

let vec_load vt i =
  create vt.len i

let u32x4 i1 i2 i3 i4 =
  createL [i1;i2;i3;i4]

let u32x8 i1 i2 i3 i4 i5 i6 i7 i8 =
  let l = [i1;i2;i3;i4;i5;i6;i7;i8] in
  assert_norm (List.Tot.length l = 8);
  createL l

let u64x4 i1 i2 i3 i4 =
  createL [i1;i2;i3;i4]

let u64x2 i1 i2 =
  createL [i1;i2]
