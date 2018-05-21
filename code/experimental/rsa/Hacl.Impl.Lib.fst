module Hacl.Impl.Lib

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open FStar.Mul

inline_for_extraction
let v = size_v

inline_for_extraction
let lbytes (len:size_t) = lbuffer uint8 (v len)
inline_for_extraction
let lbignum (len:size_t) = lbuffer uint64 (v len)

val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r > 0 /\ v x <= v m * v r}
[@ "substitute"]
let blocks x m = add_mod #SIZE ((sub_mod #SIZE x (size 1)) /. m) (size 1)

val eq_u64: a:uint64 -> b:uint64 -> Tot bool
[@ "substitute"]
let eq_u64 a b = FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

val lt_u64: a:uint64 -> b:uint64 -> Tot bool
[@ "substitute"]
let lt_u64 a b = FStar.UInt64.(u64_to_UInt64 a <^ u64_to_UInt64 b)

val le_u64: a:uint64 -> b:uint64 -> Tot bool
[@ "substitute"]
let le_u64 a b = FStar.UInt64.(u64_to_UInt64 a <=^ u64_to_UInt64 b)

val eq_u8: a:uint8 -> b:uint8 -> Tot bool
[@ "substitute"]
let eq_u8 a b = FStar.UInt8.(u8_to_UInt8 a =^ u8_to_UInt8 b)

(* check if input[ind] is equal to 1 *)
val bn_is_bit_set:
  len:size_t -> input:lbignum len ->
  ind:size_t{v ind / 64 < v len} -> Stack bool
  (requires (fun h -> live h input))
  (ensures  (fun h0 r h1 -> preserves_live h0 h1 /\ h0 == h1))
  [@"c_inline"]
let bn_is_bit_set len input ind =
  let i = ind /. size 64 in
  let j = ind %. size 64 in
  let tmp = input.(i) in
  let tmp = (shift_right #U64 tmp (size_to_uint32 j)) &. u64 1 in
  eq_u64 tmp (u64 1)

val bn_set_bit:
  len:size_t -> input:lbignum len ->
  ind:size_t{v ind / 64 < v len} -> Stack unit
  (requires (fun h -> live h input))
  (ensures  (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1))
  [@"c_inline"]
let bn_set_bit len input ind =
  let i = ind /. size 64 in
  let j = ind %. size 64 in
  let tmp = input.(i) in
  input.(i) <- (tmp |. (shift_left #U64 (u64 1) (size_to_uint32 j)))

val bval:
  len:size_t -> b:lbignum len ->
  i:size_t -> Stack uint64
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
  [@"c_inline"]
let bval len b i =
  if (i <. len) then b.(i) else u64 0

(* temporal functions *)
val fill:
  len:size_t -> b:lbignum len ->
  z:uint64 -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1))
  [@"c_inline"]
let fill len b z =
  let h0 = FStar.HyperStack.ST.get () in
  alloc1 #h0 len z b
  (fun h -> (fun _ r -> True))
  (fun tmp ->
    copy b len tmp
  )

val mul_wide: a:uint64 -> b:uint64 -> Tot uint128
[@ "substitute"]
let mul_wide a b = u128_from_UInt128 (FStar.UInt128.mul_wide (u64_to_UInt64 a) (u64_to_UInt64 b))

val eq_b_:
  len:size_t ->
  b1:lbytes len -> b2:lbytes len ->
  res:lbuffer bool 1 -> Stack unit
  (requires (fun h -> live h b1 /\ live h b2 /\ live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@ "substitute"]
let eq_b_ len b1 b2 res =
  iteri_simple #bool #1 len
  (fun i res ->
    let h = FStar.HyperStack.ST.get() in
    assume (live h b1 /\ live h b2);
    let a1 = res.(size 0) in
    let a2 = eq_u8 b1.(i) b2.(i) in
    res.(size 0) <- a1 && a2
  ) res

val eq_b:
  len:size_t ->
  b1:lbytes len -> b2:lbytes len -> Stack bool
  (requires (fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))
  [@"c_inline"]
let eq_b len b1 b2 =
  alloc #bool #bool #1 (size 1) (true) [BufItem b1; BufItem b2] []
  (fun h0 _ h1 -> True)
  (fun res ->
    eq_b_ len b1 b2 res;
    res.(size 0)
  )
