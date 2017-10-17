module Spec.Lib.IntVec

open Spec.Lib.IntTypes
open FStar.Seq
open FStar.Mul

type vectype = 
  | V: t:inttype -> len:nat -> vectype
val bits: vt:vectype -> n:nat{n = bits vt.t}
val size: vt:vectype -> n:nat{n = size vt.t * vt.len}

val intvec: vt:vectype -> Type0

val vec_add: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_sub: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_mul: #vt:vectype{vt.t <> U128} -> intvec vt -> intvec vt -> intvec vt
val vec_xor: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_and: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_or: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_not: #vt:vectype -> intvec vt -> intvec vt

val vec_shift_right: #vt:vectype -> intvec vt -> (s:uint32{uint_v s < bits vt}) -> intvec vt
val vec_shift_left: #vt:vectype -> intvec vt -> (s:uint32{uint_v s < bits vt}) -> intvec vt
val vec_rotate_right: #vt:vectype -> intvec vt -> (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) -> intvec vt
val vec_rotate_left: #vt:vectype -> intvec vt -> (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) -> intvec vt



val ( +| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( -| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( *| ): #vt:vectype{vt.t <> U128} -> intvec vt -> intvec vt -> intvec vt
val ( ^| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( &| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( || ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( ~| ): #vt:vectype -> intvec vt -> intvec vt

val ( >>| ): #vt:vectype -> intvec vt -> (s:uint32{uint_v s < bits vt}) -> intvec vt
val ( <<| ): #vt:vectype -> intvec vt -> (s:uint32{uint_v s < bits vt}) -> intvec vt
val ( >>>| ): #vt:vectype -> intvec vt -> (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) -> intvec vt
val ( <<<| ): #vt:vectype -> intvec vt -> (s:uint32{uint_v s > 0 /\ uint_v s < bits vt}) -> intvec vt


