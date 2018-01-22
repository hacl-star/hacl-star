module Hacl.Impl.Lib

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open Spec.Lib.RawIntTypes
open FStar.Mul

inline_for_extraction
let v = size_v

type lbytes (len:size_nat) = lbuffer uint8 len
type lbignum (len:size_nat) = lbuffer uint64 len

val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r > 0 /\ v x <= v m * v r}
[@ "substitute"]
let blocks x m = add_mod #SIZE ((sub_mod #SIZE x (size 1)) /. m) (size 1)

(* text_to_bn *)
val get_size_nat: lenText:size_t{v lenText > 0} -> Tot (res:size_t{v res > 0})
[@ "substitute"]
let get_size_nat lenText = blocks lenText (size 8)

val bits_to_bn: bits:size_t{v bits > 0} -> Tot (res:size_t{v res > 0})
[@ "substitute"]
let bits_to_bn bits = blocks bits (size 64)

val bits_to_text: bits:size_t{v bits > 0} -> Tot (res:size_t{v res > 0})
[@ "substitute"]
let bits_to_text bits = blocks bits (size 8)

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
    #len:size_nat -> clen:size_t{v clen == len} ->
    input:lbignum len ->
    ind:size_t{v ind / 64 < len} -> Stack bool
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> preserves_live h0 h1 /\ h0 == h1))
    
let bn_is_bit_set #len clen input ind =
    let i = ind /. size 64 in
    let j = ind %. size 64 in
    let tmp = input.(i) in
    let tmp = (shift_right #U64 tmp (size_to_uint32 j)) &. u64 1 in
    eq_u64 tmp (u64 1)

val bn_set_bit:
    #len:size_nat -> clen:size_t{v clen == len} ->
    input:lbignum len ->
    ind:size_t{v ind / 64 < len} -> Stack unit
    (requires (fun h -> live h input))
    (ensures  (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 input h0 h1))
    
let bn_set_bit #len clen input ind =
    let i = ind /. size 64 in
    let j = ind %. size 64 in
    let tmp = input.(i) in
    input.(i) <- (tmp |. (shift_left #U64 (u64 1) (size_to_uint32 j)))
    
(* temporal functions *)
val fill:
  #len:size_nat -> clen:size_t{v clen == len} ->
  b:lbignum len -> z:uint64 -> Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ modifies1 b h0 h1))
  
let fill #len clen b z =
  alloc #uint64 #unit #len clen z [] [BufItem b]
  (fun h0 _ h1 -> True)
  (fun tmp ->
      copy clen tmp b
  )

val mul_wide: a:uint64 -> b:uint64 -> Tot uint128
[@ "substitute"]
let mul_wide a b = u128_from_UInt128 (FStar.UInt128.mul_wide (u64_to_UInt64 a) (u64_to_UInt64 b))

val eq_b_:
    #len:size_nat -> clen:size_t{v clen == len} ->
    b1:lbytes len -> b2:lbytes len ->
    i:size_t{v i <= len} -> Stack bool
    (requires (fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
    
let rec eq_b_ #len clen b1 b2 i =
    if (i <. clen) then begin
       if (eq_u8 b1.(i) b2.(i))
       then eq_b_ #len clen b1 b2 (size_incr i)
       else false end 
    else true

val eq_b:
    #len:size_nat -> clen:size_t{v clen == len} ->
    b1:lbytes len -> b2:lbytes len -> Stack bool
    (requires (fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
[@ "substitute"]    
let eq_b #len clen b1 b2 = eq_b_ #len clen b1 b2 (size 0)
