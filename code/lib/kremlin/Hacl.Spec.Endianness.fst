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

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

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

abstract val seq_map: #a:Type -> #b:Type -> f:(a -> GTot b) -> s:Seq.seq a ->
  GTot (s':Seq.seq b{Seq.length s' = Seq.length s /\ (forall (i:nat). i < Seq.length s ==> Seq.index s' i == f (Seq.index s i))})
let seq_map #a #b f s =
  if Seq.length s = 0 then Seq.createEmpty #b
  else seq_map_ f s 0 (Seq.create (Seq.length s) (f (Seq.index s 0)))
  

unfold inline_for_extraction
let reveal_sbytes (s:Seq.seq H8.t) : GTot (s:Seq.seq U8.t) = s

unfold inline_for_extraction
let intro_sbytes (s:Seq.seq U8.t) : GTot (s:Seq.seq H8.t) = s

unfold inline_for_extraction
let hlittle_endian (s:Seq.seq H8.t) : GTot nat =
  little_endian s

unfold inline_for_extraction
let hbig_endian (s:Seq.seq H8.t) : GTot nat =
  big_endian s

open FStar.Mul

unfold inline_for_extraction
let hlittle_bytes  (len:U32.t) (n:nat{n < pow2 (8 * U32.v len)}) : GTot (b:Seq.seq H8.t{Seq.length b = U32.v len}) =
  little_bytes len n

unfold inline_for_extraction
let hbig_bytes (len:U32.t) (n:nat{n < pow2 (8 * U32.v len)}) : GTot (b:Seq.seq H8.t{Seq.length b = U32.v len}) =
  big_bytes len n
