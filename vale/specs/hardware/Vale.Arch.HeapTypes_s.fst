module Vale.Arch.HeapTypes_s
open FStar.Mul

let __reduce__ = ()

type base_typ:eqtype =
  | TUInt8
  | TUInt16
  | TUInt32
  | TUInt64
  | TUInt128

type taint:eqtype =
  | Public
  | Secret

type memTaint_t = (m:Map.t int taint{Set.equal (Map.domain m) (Set.complement Set.empty)})
