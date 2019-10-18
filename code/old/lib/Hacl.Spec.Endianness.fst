module Hacl.Spec.Endianness

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Old.Endianness

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

let h8_to_u8     (x:H8.t) : GTot (y:U8.t{U8.v y = H8.v x}) = U8.uint_to_t (H8.v x)
let h32_to_u32   (x:H32.t) : GTot (y:U32.t{U32.v y = H32.v x}) = U32.uint_to_t (H32.v x)
let h64_to_u64   (x:H64.t) : GTot (y:U64.t{U64.v y = H64.v x}) = U64.uint_to_t (H64.v x)
let h128_to_u128 (x:H128.t) : GTot (y:U128.t{U128.v y = H128.v x}) = U128.uint_to_t (H128.v x)

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
  if Seq.length s = 0 then Seq.empty #b
  else seq_map_ f s 0 (Seq.create (Seq.length s) (f (Seq.index s 0)))
  

unfold inline_for_extraction
let reveal_sbytes (s:Seq.seq H8.t) : GTot (s:Seq.seq U8.t) = seq_map h8_to_u8 s

unfold inline_for_extraction
let reveal_h32s (s:Seq.seq H32.t) : GTot (s:Seq.seq U32.t) = seq_map h32_to_u32 s

unfold inline_for_extraction
let reveal_h64s (s:Seq.seq H64.t) : GTot (s:Seq.seq U64.t) = seq_map h64_to_u64 s

unfold inline_for_extraction
let reveal_h128s (s:Seq.seq H128.t) : GTot (s:Seq.seq U128.t) = seq_map h128_to_u128 s

unfold inline_for_extraction
let intro_sbytes (s:Seq.seq U8.t) : GTot (s:Seq.seq H8.t) = seq_map Hacl.Cast.uint8_to_sint8 s

unfold inline_for_extraction
let intro_h32s (s:Seq.seq U32.t) : GTot (s:Seq.seq H32.t) = seq_map Hacl.Cast.uint32_to_sint32 s

unfold inline_for_extraction
let intro_h64s (s:Seq.seq U64.t) : GTot (s:Seq.seq H64.t) = seq_map Hacl.Cast.uint64_to_sint64 s


unfold inline_for_extraction 
let hlittle_endian (s:Seq.seq H8.t) : GTot nat =
  little_endian (reveal_sbytes s)

unfold inline_for_extraction
let hbig_endian (s:Seq.seq H8.t) : GTot nat =
  big_endian (reveal_sbytes s)

open FStar.Mul

unfold inline_for_extraction
let hlittle_bytes  (len:U32.t) (n:nat{n < pow2 (8 * U32.v len)}) : GTot (b:Seq.seq H8.t{Seq.length b = U32.v len}) =
  intro_sbytes (little_bytes len n)

unfold inline_for_extraction
let hbig_bytes (len:U32.t) (n:nat{n < pow2 (8 * U32.v len)}) : GTot (b:Seq.seq H8.t{Seq.length b = U32.v len}) =
  intro_sbytes (big_bytes len n)

assume val lift_8 (f:(Seq.seq U8.t -> Tot (Seq.seq U8.t))) (s:Seq.seq H8.t) : Tot (s':Seq.seq H8.t{
  reveal_sbytes s' == (f (reveal_sbytes s))})

assume val lift_32 (#p:(Seq.seq U32.t -> Type0)) (f:(s:Seq.seq U32.t{p s} -> Tot (Seq.seq U32.t))) (s:Seq.seq H32.t{p (reveal_h32s s)}) : Tot (s':Seq.seq H32.t{reveal_h32s s' == f (reveal_h32s s)})

assume val lift_64 (f:(Seq.seq U64.t -> Tot (Seq.seq U64.t))) (s:Seq.seq H64.t) : Tot (s':Seq.seq H64.t{
  reveal_h64s s' == f (reveal_h64s s)})
