module Lib.IntVector

open FStar.Mul
open Lib.Sequence
module Ints = Lib.IntTypes

type vectype =
  | V: it:Ints.m_inttype -> len:Ints.size_nat -> vectype
let bits vt = Ints.bits vt.it
let size vt = Ints.numbytes vt.it * vt.len

val intvec: vt:vectype -> Type0
val intvec_v: #vt:vectype -> intvec vt -> GTot (lseq nat vt.len)

val vec_add: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_sub: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_mul: #vt:vectype{vt.it <> Ints.U128} -> intvec vt -> intvec vt -> intvec vt
val vec_xor: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_and: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_or: #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val vec_not: #vt:vectype -> intvec vt -> intvec vt

val vec_shift_right: #vt:vectype -> intvec vt -> Ints.shiftval vt.it -> intvec vt
val vec_shift_left: #vt:vectype -> intvec vt -> Ints.shiftval vt.it -> intvec vt
val vec_rotate_right: #vt:vectype -> intvec vt -> Ints.rotval vt.it -> intvec vt
val vec_rotate_left: #vt:vectype -> intvec vt -> Ints.rotval vt.it -> intvec vt



val ( +| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( -| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( *| ): #vt:vectype{vt.it <> Ints.U128} -> intvec vt -> intvec vt -> intvec vt
val ( ^| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( &| ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( || ): #vt:vectype -> intvec vt -> intvec vt -> intvec vt
val ( ~| ): #vt:vectype -> intvec vt -> intvec vt

val ( >>| ): #vt:vectype -> intvec vt -> Ints.shiftval vt.it -> intvec vt
val ( <<| ): #vt:vectype -> intvec vt -> Ints.shiftval vt.it -> intvec vt
val ( >>>| ): #vt:vectype -> intvec vt -> Ints.rotval vt.it -> intvec vt
val ( <<<| ): #vt:vectype -> intvec vt -> Ints.rotval vt.it -> intvec vt


val vec_load: vt:vectype -> Ints.uint_t vt.it -> intvec vt

type uint32x4 = intvec (V Ints.U32 4)
type uint32x8 = intvec (V Ints.U32 8)
type uint64x4 = intvec (V Ints.U64 4)
type uint64x2 = intvec (V Ints.U64 2)

val u32x4: Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> uint32x4
val u32x8: Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> Ints.uint32 -> uint32x8
val u64x4: Ints.uint64 -> Ints.uint64 -> Ints.uint64 -> Ints.uint64 -> uint64x4
val u64x2: Ints.uint64 -> Ints.uint64 -> uint64x2
