module Hacl.Impl.Curve25519.Field64

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open FStar.Mul

#reset-options "--z3rlimit 20"


let felem = lbuffer uint64 4ul
let felem_wide = lbuffer uint64 8ul

inline_for_extraction
val create_felem: unit -> StackInline felem
		       (requires (fun _ -> True))
		       (ensures (fun h0 f h1 -> stack_allocated f h0 h1 (Seq.create 4 (u64 0))))
inline_for_extraction
let create_felem () = create 4ul (u64 0)

inline_for_extraction
val create_wide: unit -> StackInline felem_wide
		       (requires (fun _ -> True))
		       (ensures (fun h0 f h1 -> stack_allocated f h0 h1 (Seq.create 8 (u64 0))))
inline_for_extraction
let create_wide () = create 8ul (u64 0)


inline_for_extraction
val set_bit1: f:felem -> i:size_t{v i < 255} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let set_bit1 f i = 
    f.(i /. size 64) <- f.(i /. size 64) |. (u64 1 <<. (i %. size 64))

inline_for_extraction
val set_bit0: f:felem -> i:size_t{v i < 255} -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
inline_for_extraction
let set_bit0 f i = 
    f.(i /. size 64) <- f.(i /. size 64) &. lognot (u64 1 <<. (i %. size 64))

inline_for_extraction
val set_zero: f:felem -> Stack unit
                   (requires (fun h -> live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let set_zero f = 
  f.(0ul) <- u64 0;
  f.(1ul) <- u64 0;
  f.(2ul) <- u64 0;
  f.(3ul) <- u64 0

inline_for_extraction
val copy_felem: f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc f1) h0 h1))
let copy_felem f1 f2 =
    f1.(size 0) <- f2.(size 0);
    f1.(size 1) <- f2.(size 1);
    f1.(size 2) <- f2.(size 2);
    f1.(size 3) <- f2.(size 3)

inline_for_extraction
let uint64_eq_mask (a:uint64) (b:uint64) : uint64
  = let x = a ^. b in
    let minus_x = (lognot x) +. (u64 1) in
    let x_or_minus_x = x |. minus_x in
    let xnx = x_or_minus_x >>. 63ul in
    let c = xnx -. (u64 1) in
    c

inline_for_extraction
let uint64_gte_mask (a:uint64) (b:uint64) : uint64
  = let x = a in
    let y = b in
    let x_xor_y = logxor x y in
    let x_sub_y = x -. y in
    let x_sub_y_xor_y = x_sub_y ^. y in
    let q = logor x_xor_y x_sub_y_xor_y in
    let x_xor_q = logxor x q in
    let x_xor_q_ = shift_right x_xor_q 63ul in
    let c = sub_mod x_xor_q_ (u64 1) in
    c

[@CInline]
let addcarry (x:uint64) (y:uint64) (cin:uint64) =
  let res1 = x +. cin in
  let mask = lognot (uint64_gte_mask res1 x) in
  let res2 = res1 +. y in
  let mask = mask |. lognot (uint64_gte_mask res2 res1) in
  let carry = u64 1 &. mask in
  res2, carry

[@CInline]
let subborrow (x:uint64) (y:uint64) (cin:uint64) =
  let res1 = x -. cin in
  let mask = lognot (uint64_gte_mask x res1) in
  let res2 = res1 -. y in
  let mask = mask |. lognot (uint64_gte_mask res1 res2) in
  let carry = u64 1 &. mask in
  res2, carry


inline_for_extraction
let mul64 (x:uint64) (y:uint64) =
  let res = mul64_wide x y in
  (to_u64 res, to_u64 (res >>. 64ul))

[@ CInline]
val fadd1: out:felem ->  f1:felem  -> f2:uint64  -> Stack uint64
                   (requires (fun h -> live h f1 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fadd1 out f1 f2 = 
  let f10 = f1.(0ul) in
  let f11 = f1.(1ul) in
  let f12 = f1.(2ul) in
  let f13 = f1.(3ul) in
  let (o0,carry) = addcarry f10 f2 (u64 0) in
  let (o1,carry) = addcarry f11 (u64 0) carry in
  let (o2,carry) = addcarry f12 (u64 0) carry in
  let (o3,carry) = addcarry f13 (u64 0) carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3;
  carry

[@ CInline]
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
          (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
	  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fadd out f1 f2 = 
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (o0,carry) = addcarry f10 f20 (u64 0) in
  let (o1,carry) = addcarry f11 f21 carry in
  let (o2,carry) = addcarry f12 f22 carry in
  let (o3,carry) = addcarry f13 f23 carry in
  let (o0,carry) = addcarry o0 (u64 38 *. carry) (u64 0) in
  let (o1,carry) = addcarry o1 (u64 0) carry in
  let (o2,carry) = addcarry o2 (u64 0) carry in
  let (o3,carry) = addcarry o3 (u64 0) carry in
  let o0 = o0 +. (u64 38 *. carry) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3


  


[@ CInline]
val fsub: out:felem ->  f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 ))
[@ CInline]
let fsub out f1 f2 = 
  let f10 = f1.(0ul) in
  let f20 = f2.(0ul) in
  let f11 = f1.(1ul) in
  let f21 = f2.(1ul) in
  let f12 = f1.(2ul) in
  let f22 = f2.(2ul) in
  let f13 = f1.(3ul) in
  let f23 = f2.(3ul) in
  let (o0,carry) = subborrow f10 f20 (u64 0) in
  let (o1,carry) = subborrow f11 f21 carry in
  let (o2,carry) = subborrow f12 f22 carry in
  let (o3,carry) = subborrow f13 f23 carry in
  let (o0,carry) = subborrow o0 (u64 38 *. carry) (u64 0) in
  let (o1,carry) = subborrow o1 (u64 0) carry in
  let (o2,carry) = subborrow o2 (u64 0) carry in
  let (o3,carry) = subborrow o3 (u64 0) carry in
  let o0 = o0 -. (u64 38 *. carry) in
  out.(0ul) <- o0;
  out.(1ul) <- o1;
  out.(2ul) <- o2;
  out.(3ul) <- o3



[@ CInline]
val smul_felem: out:felem -> u1:uint64 -> f2:felem -> Stack uint64
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_felem out u1 f2 = 
  let f20 = f2.(size 0) in
  let f21 = f2.(size 1) in
  let f22 = f2.(size 2) in
  let f23 = f2.(size 3) in
  let l0,h0 = mul64 u1 f20 in
  let l1,h1 = mul64 u1 f21 in
  let l2,h2 = mul64 u1 f22 in
  let l3,h3 = mul64 u1 f23 in
  let o0 = l0 in
  let o1,carry = addcarry l1 h0 (u64 0) in
  let o2,carry = addcarry l2 h1 carry in
  let o3,carry = addcarry l3 h2 carry in
  let carry = h3 +. carry in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  carry

[@ CInline]
val smul_add_felem: out:felem -> u1:uint64 -> f2:felem -> Stack uint64
                   (requires (fun h -> live h out /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let smul_add_felem out u1 f2 = 
  let o0 = out.(0ul) in
  let o1 = out.(1ul) in
  let o2 = out.(2ul) in
  let o3 = out.(3ul) in
  let o4 = smul_felem out u1 f2 in
  let o0,carry = addcarry out.(0ul) o0 (u64 0) in
  let o1,carry = addcarry out.(1ul) o1 carry in
  let o2,carry = addcarry out.(2ul) o2 carry in
  let o3,carry = addcarry out.(3ul) o3 carry in
  out.(size 0) <- o0;
  out.(size 1) <- o1;
  out.(size 2) <- o2;
  out.(size 3) <- o3;
  o4 +. carry



[@ CInline]
val mul_felem: out:felem_wide -> f1:felem -> r:felem  -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h r))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let mul_felem out f1 r = 
  let s4 = smul_felem (sub out 0ul 4ul) f1.(size 0) r in
  out.(4ul) <- s4;
  let s5 = smul_add_felem (sub out 1ul 4ul) f1.(size 1) r in
  out.(5ul) <- s5;
  let s6 = smul_add_felem (sub out 2ul 4ul) f1.(size 2) r in
  out.(6ul) <- s6;
  let s7 = smul_add_felem (sub out 3ul 4ul) f1.(size 3) r in
  out.(7ul) <- s7


[@ CInline]
val carry_wide: out:felem -> inp:felem_wide -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc inp) h0 h1))
[@ CInline]
let carry_wide out inp =
  copy out (sub inp 0ul 4ul);
  let s5 = smul_add_felem out (u64 38) (sub inp 4ul 4ul) in
  let carry = fadd1 out out (u64 38 *. s5) in
  let o0,carry = addcarry out.(0ul) (u64 38 *. carry) (u64 0) in
  let o1 = out.(1ul) +. carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1


[@ CInline]
val fmul: out:felem -> f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul out f1 f2 =
  push_frame();
  let tmp_w = create_wide () in
  mul_felem tmp_w f1 f2;
  carry_wide out tmp_w;
  pop_frame()

[@ CInline]
val fmul2: out1:felem -> out2:felem -> f1:felem -> f2:felem -> f3:felem -> f4:felem -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2 /\ live h f3 /\ live h f4))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
[@ CInline]
let fmul2 out1 out2 f1 f2 f3 f4 =
  fmul out1 f1 f2;
  fmul out2 f3 f4

[@ CInline]
val fmul1: out:felem -> f1:felem -> f2:uint64 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul1 out f1 f2 =
  let s4 = smul_felem out f2 f1 in
  let carry = fadd1 out out (u64 38 *. s4) in
  let o0,carry = addcarry out.(0ul) (u64 38 *. carry) (u64 0) in
  let o1 = out.(1ul) +. carry in
  out.(0ul) <- o0;
  out.(1ul) <- o1

[@ CInline]
val fsqr: out:felem -> f1:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fsqr out f = fmul out f f 

[@ CInline]
val fsqr2: out1:felem -> out2:felem -> f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h out1 /\ live h out2 /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out1 |+| loc out2) h0 h1))
[@ CInline]
let fsqr2 out1 out2 f1 f2 = 
  fsqr out1 f1;
  fsqr out2 f2
 

inline_for_extraction
val load_felem: f:felem -> u64s:lbuffer uint64 4ul -> Stack unit
                   (requires (fun h -> live h u64s /\ live h f))
		   (ensures (fun h0 _ h1 -> modifies (loc f) h0 h1))
let load_felem f u64s = 
    f.(0ul) <- u64s.(0ul);
    f.(1ul) <- u64s.(1ul);
    f.(2ul) <- u64s.(2ul);
    f.(3ul) <- u64s.(3ul)

val store_felem: u64s:lbuffer uint64 4ul -> f:felem -> Stack unit
                   (requires (fun h -> live h f /\ live h u64s))
		   (ensures (fun h0 _ h1 -> modifies (loc u64s) h0 h1))
let store_felem u64s f = 
    let f0 = f.(0ul) in
    let f1 = f.(1ul) in
    let f2 = f.(2ul) in
    let f3 = f.(3ul) in
    let top_bit = f3 >>. 63ul in
    let f3 = f3 &. u64 0x7fffffffffffffff in
    let f0,carry = addcarry f0 (u64 19 *. top_bit) (u64 0) in
    let f1,carry = addcarry f1 (u64 0) carry in
    let f2,carry = addcarry f2 (u64 0) carry in
    let f3,carry = addcarry f3 (u64 0) carry in
    let top_bit = f3 >>. 63ul in
    let f3 = f3 &. u64 0x7fffffffffffffff in
    let f0,carry = addcarry f0 (u64 19 *. top_bit) (u64 0) in
    let f1,carry = addcarry f1 (u64 0) carry in
    let f2,carry = addcarry f2 (u64 0) carry in
    let f3 = f3 +. carry in
    u64s.(0ul) <- f0;
    u64s.(1ul) <- f1;
    u64s.(2ul) <- f2;
    u64s.(3ul) <- f3

