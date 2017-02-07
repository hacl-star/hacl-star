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

assume val seq_map: #a:Type -> #b:Type -> f:(a -> GTot b) -> s:Seq.seq a ->
  GTot (s':Seq.seq b{Seq.length s' = Seq.length s /\ (forall (i:nat). i < Seq.length s ==> Seq.index s' i == f (Seq.index s i))})

inline_for_extraction let hlittle_endian (s:Seq.seq H8.t) : GTot nat =
  little_endian s

inline_for_extraction let hbig_endian (s:Seq.seq H8.t) : GTot nat =
  big_endian s
