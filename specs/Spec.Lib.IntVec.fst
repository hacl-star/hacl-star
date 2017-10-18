module Spec.Lib.IntVec

open Spec.Lib.IntTypes
open FStar.Seq
open FStar.Mul
let bits vt = bits vt.t
let size vt = size vt.t * vt.len

type intvec (vt:vectype) = 
  s:seq (uint_t vt.t){length s = vt.len}

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
  seq_map_ghost uint_v v

let vec_add #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (add_mod #vt.t) v1 v2

let vec_sub #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (sub_mod #vt.t) v1 v2

let vec_mul (#vt:vectype{vt.t <> U128}) (v1:intvec vt) (v2:intvec vt): intvec vt = 
seq_map2 (mul_mod #vt.t) v1 v2

let vec_xor #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (logxor #vt.t) v1 v2

let vec_and #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (logand #vt.t) v1 v2

let vec_or #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
seq_map2 (logor #vt.t) v1 v2

let vec_not #vt (v1:intvec vt) : intvec vt = 
seq_map (lognot #vt.t) v1 

let vec_shift_right #vt v1 s = 
seq_map (fun x -> shift_right x s) v1 

let vec_shift_left #vt (v1:intvec vt) (s:uint32{uint_v s < bits vt}) : intvec vt = 
seq_map (fun x -> shift_left #vt.t x s) v1 

let vec_rotate_right #vt (v1:intvec vt) (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) : intvec vt = 
seq_map (fun x -> rotate_right  #vt.t x s) v1 

let vec_rotate_left #vt (v1:intvec vt) (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) : intvec vt = 
seq_map (fun x -> rotate_left #vt.t x s) v1 

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

