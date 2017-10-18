module Spec.Lib.IntVec

open FStar.Seq
open FStar.Mul

module Ints = Spec.Lib.IntTypes

type intvec (vt:vectype) = 
  s:seq (Ints.uint_t vt.it){length s = vt.len}

val seq_map_ghost:
  #a:Type -> #b:Type ->
  f:(a -> GTot b) ->
  s:Seq.seq a ->
  GTot (s':Seq.seq b{Seq.length s = Seq.length s' /\
    (forall (i:nat). {:pattern (Seq.index s' i)} i < Seq.length s' ==> Seq.index s' i == f (Seq.index s i))})
    (decreases (Seq.length s))
let rec seq_map_ghost #a #b f s =
  if Seq.length s = 0 then
    Seq.createEmpty
  else
    let s' = Seq.cons (f (Seq.head s)) (seq_map_ghost f (Seq.tail s)) in
    s'

val seq_map:
  #a:Type -> #b:Type ->
  f:(a -> Tot b) ->
  s:Seq.seq a ->
  Tot (s':Seq.seq b{Seq.length s = Seq.length s' /\
    (forall (i:nat). {:pattern (Seq.index s' i)} i < Seq.length s' ==> Seq.index s' i == f (Seq.index s i))})
    (decreases (Seq.length s))
let rec seq_map #a #b f s =
  if Seq.length s = 0 then
    Seq.createEmpty
  else
    let s' = Seq.cons (f (Seq.head s)) (seq_map f (Seq.tail s)) in
    s'

val seq_map2:
  #a:Type -> #b:Type -> #c:Type ->
  f:(a -> b -> Tot c) ->
  s:Seq.seq a -> s':Seq.seq b{Seq.length s = Seq.length s'} ->
  Tot (s'':Seq.seq c{Seq.length s = Seq.length s'' /\
    (forall (i:nat). {:pattern (Seq.index s'' i)} i < Seq.length s'' ==> Seq.index s'' i == f (Seq.index s i) (Seq.index s' i))})
    (decreases (Seq.length s))
let rec seq_map2 #a #b #c f s s' =
  if Seq.length s = 0 then Seq.createEmpty
  else
    let s'' = Seq.cons (f (Seq.head s) (Seq.head s')) (seq_map2 f (Seq.tail s) (Seq.tail s')) in
    s''


let intvec_v #vt v =
  seq_map_ghost Ints.uint_v v

let vec_add #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (Ints.add_mod #vt.it) v1 v2

let vec_sub #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (Ints.sub_mod #vt.it) v1 v2

let vec_mul #vt (v1:intvec vt) (v2:intvec vt): intvec vt = 
seq_map2 (Ints.mul_mod #vt.it) v1 v2

let vec_xor #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (Ints.logxor #vt.it) v1 v2

let vec_and #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (Ints.logand #vt.it) v1 v2

let vec_or #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (Ints.logor #vt.it) v1 v2

let vec_not #vt (v1:intvec vt) : intvec vt = 
seq_map (Ints.lognot #vt.it) v1 

let vec_shift_right #vt v1 s = 
seq_map (fun x -> Ints.shift_right x s) v1 

let vec_shift_left #vt v1 s =
seq_map (fun x -> Ints.shift_left #vt.it x s) v1 

let vec_rotate_right #vt v1 s = 
seq_map (fun x -> Ints.rotate_right  #vt.it x s) v1 

let vec_rotate_left #vt v1 s = 
seq_map (fun x -> Ints.rotate_left #vt.it x s) v1 

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
  Seq.create vt.len i

let u32x4 i1 i2 i3 i4 = 
  Seq.createL [i1;i2;i3;i4]

let u32x8 i1 i2 i3 i4 i5 i6 i7 i8 = 
  Seq.createL [i1;i2;i3;i4;i5;i6;i7;i8]

let u64x4 i1 i2 i3 i4 =
  Seq.createL [i1;i2;i3;i4]

let u64x2 i1 i2 = 
  Seq.createL [i1;i2]

