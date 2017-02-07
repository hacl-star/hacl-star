module Hacl.Spec.Endianness

open FStar.Endianness

module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128

module H8   = Hacl.UInt8
module H16  = Hacl.UInt16
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let h8_to_u8 (x:H8.t) : GTot (y:U8.t{U8.v y = H8.v x}) = U8.uint_to_t (H8.v x)

private val seq_map_:
  #a:Type -> #b:Type ->
  f:(a -> GTot b) ->
  s:Seq.seq a ->
  j:nat{j <= Seq.length s} ->
  s':Seq.seq b{Seq.length s' = Seq.length s /\ (forall (i:nat). {:pattern (Seq.index s' i)}
    i < j ==> Seq.index s' i == f (Seq.index s i))} ->
    GTot (s'':Seq.seq b{Seq.length s'' = Seq.length s
      /\ (forall (i:nat). {:pattern (Seq.index s'' i)} i < Seq.length s ==> Seq.index s'' i == f (Seq.index s i))})
  (decreases (Seq.length s - j))
private let rec seq_map_ #a #b f s j s' =
  if j = Seq.length s then s'
  else (
    let s' = Seq.upd s' j (f (Seq.index s j)) in
    seq_map_ f s (j+1) s'
  )

val seq_map: #a:Type -> #b:Type -> f:(a -> GTot b) -> s:Seq.seq a ->
  GTot (s':Seq.seq b{Seq.length s' = Seq.length s /\ (forall (i:nat). i < Seq.length s ==> Seq.index s' i == f (Seq.index s i))})
let seq_map #a #b f s =
  if Seq.length s = 0 then Seq.createEmpty #b
  else seq_map_ f s 0 (Seq.create (Seq.length s) (f (Seq.index s 0)))
  

unfold inline_for_extraction
let reveal_sbytes (s:Seq.seq H8.t) : GTot (s:Seq.seq U8.t) = seq_map h8_to_u8 s


unfold inline_for_extraction 
let hlittle_endian (s:Seq.seq H8.t) : GTot nat =
  little_endian (reveal_sbytes s)

unfold inline_for_extraction
let hbig_endian (s:Seq.seq H8.t) : GTot nat =
  big_endian (reveal_sbytes s)
