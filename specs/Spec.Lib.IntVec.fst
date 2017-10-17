module Spec.Lib.IntVec

open Spec.Lib.IntTypes
open FStar.Seq
open FStar.Mul
let bits vt = bits vt.t
let size vt = size vt.t * vt.len

type intvec (vt:vectype) = 
  s:seq (uint_t vt.t){length s = vt.len}
  
let vec_add #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
Spec.Loops.seq_map2 (add_mod #vt.t) v1 v2

let vec_sub #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
Spec.Loops.seq_map2 (sub_mod #vt.t) v1 v2

let vec_mul (#vt:vectype{vt.t <> U128}) (v1:intvec vt) (v2:intvec vt): intvec vt = 
Spec.Loops.seq_map2 (mul_mod #vt.t) v1 v2

let vec_xor #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
Spec.Loops.seq_map2 (logxor #vt.t) v1 v2

let vec_and #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
Spec.Loops.seq_map2 (logand #vt.t) v1 v2

let vec_or #vt (v1:intvec vt) (v2:intvec vt) : intvec vt = 
Spec.Loops.seq_map2 (logor #vt.t) v1 v2

let vec_not #vt (v1:intvec vt) : intvec vt = 
Spec.Loops.seq_map (lognot #vt.t) v1 

let vec_shift_right #vt v1 s = 
Spec.Loops.seq_map (fun x -> shift_right x s) v1 

let vec_shift_left #vt (v1:intvec vt) (s:uint32{uint_v s < bits vt}) : intvec vt = 
Spec.Loops.seq_map (fun x -> shift_left #vt.t x s) v1 

let vec_rotate_right #vt (v1:intvec vt) (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) : intvec vt = 
Spec.Loops.seq_map (fun x -> rotate_right  #vt.t x s) v1 

let vec_rotate_left #vt (v1:intvec vt) (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) : intvec vt = 
Spec.Loops.seq_map (fun x -> rotate_left #vt.t x s) v1 

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

