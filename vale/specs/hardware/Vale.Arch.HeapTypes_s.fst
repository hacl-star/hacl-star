module Vale.Arch.HeapTypes_s
open FStar.Mul
open Vale.Def.Words_s

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

let machine_heap = Map.t int nat8
let memTaint_t = (m:Map.t int taint{Set.equal (Map.domain m) (Set.complement Set.empty)})
let heaplet_id = n:nat{n < 16}

let heaplets8 (ptr:int) (k:heaplet_id) (m:option (int -> option heaplet_id)) : bool =
  match m with None -> true | Some d -> d ptr = Some k

let heaplets16 (ptr:int) (k:heaplet_id) (m:option (int -> option heaplet_id)) : bool =
  heaplets8 ptr k m && heaplets8 (ptr + 1) k m 

let heaplets32 (ptr:int) (k:heaplet_id) (m:option (int -> option heaplet_id)) : bool =
  heaplets16 ptr k m && heaplets16 (ptr + 2) k m 

[@"opaque_to_smt"]
let heaplets64 (ptr:int) (k:heaplet_id) (m:option (int -> option heaplet_id)) : bool =
  heaplets32 ptr k m && heaplets32 (ptr + 4) k m 

let heaplets128 (ptr:int) (k:heaplet_id) (m:option (int -> option heaplet_id)) : bool =
  heaplets64 ptr k m && heaplets64 (ptr + 8) k m 
