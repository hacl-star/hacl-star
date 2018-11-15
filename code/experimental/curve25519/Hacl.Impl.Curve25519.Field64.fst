module Hacl.Impl.Curve25519.Field64

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer
open FStar.Mul
module Core64=Hacl.Impl.Curve25519.Field64.Core
#reset-options "--z3rlimit 20"


let felem = lbuffer uint64 4ul
let felem2 = lbuffer uint64 8ul
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


[@ CInline]
val fadd: out:felem -> f1:felem  -> f2:felem  -> Stack unit
          (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
	  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let fadd out f1 f2 =
  let carry = Core64.add out f1 f2 in
  let carry = Core64.add1 out out (u64 38 *. carry) in
  out.(0ul) <- out.(0ul) +. (u64 38 *. carry)
  


[@ CInline]
val fsub: out:felem ->  f1:felem  -> f2:felem  -> Stack unit
                   (requires (fun h -> live h f1 /\ live h f2 /\ live h out))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 ))
[@ CInline]
let fsub out f1 f2 = 
  let carry = Core64.sub out f1 f2 in
  let carry = Core64.sub1 out out (u64 38 *. carry) in
  out.(0ul) <- out.(0ul) -. (u64 38 *. carry)




[@ CInline]
val carry_wide: out:felem -> inp:felem_wide -> Stack unit
                   (requires (fun h -> live h out /\ live h inp))
		   (ensures (fun h0 _ h1 -> modifies (loc out |+| loc inp) h0 h1))
[@ CInline]
let carry_wide out inp =
  out.(0ul) <- inp.(0ul);
  out.(1ul) <- inp.(1ul);
  out.(2ul) <- inp.(2ul);
  out.(3ul) <- inp.(3ul);
  let s5 = Core64.mul1_add out (sub inp 4ul 4ul) (u64 38) in
  let carry = Core64.add1 out out (u64 38 *. s5) in
  out.(0ul) <- out.(0ul) +. (u64 38 *. carry)


[@ CInline]
val fmul: out:felem -> f1:felem -> f2:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1 /\ live h f2))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul out f1 f2 =
  push_frame();
  let tmp_w = create_wide () in
  Core64.mul tmp_w f1 f2;
  carry_wide out tmp_w;
  pop_frame()

[@ CInline]
val fmul2:
    out:felem2
  -> f1:felem2
  -> f2:felem2
  -> Stack unit
  (requires (fun h -> live h out /\ live h f1 /\ live h f2))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul2 out f1 f2 =
  push_frame();
  let tmp = create 16ul (u64 0) in
  Core64.mul2 tmp f1 f2;
  let out1 = sub out 0ul 4ul in
  let out2 = sub out 4ul 4ul in
  let tmp1 = sub tmp 0ul 8ul in
  let tmp2 = sub tmp 8ul 8ul in
  carry_wide out1 tmp1;
  carry_wide out2 tmp2;
  pop_frame()

[@ CInline]
val fmul1: out:felem -> f1:felem -> f2:uint64 -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fmul1 out f1 f2 =
  let s4 = Core64.mul1 out f1 f2 in
  let carry = Core64.add1 out out (u64 38 *. s4) in
  out.(0ul) <- out.(0ul) +. carry

[@ CInline]
val fsqr: out:felem -> f1:felem -> Stack unit
                   (requires (fun h -> live h out /\ live h f1))
		   (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fsqr out f = 
  push_frame();
  let tmp = create_wide () in
  Core64.sqr tmp f;
  carry_wide out tmp;
  pop_frame()

[@ CInline]
val fsqr2: out:felem2 -> f:felem2 -> Stack unit
        (requires (fun h -> live h out /\ live h f))
	(ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
[@ CInline]
let fsqr2 out f = 
  push_frame();
  let tmp = create 16ul (u64 0) in
  let tmp1 = sub tmp 0ul 8ul in
  let tmp2 = sub tmp 8ul 8ul in
  let out1 = sub out 0ul 4ul in
  let out2 = sub out 4ul 4ul in
  Core64.sqr2 tmp f;
  carry_wide out1 tmp1;
  carry_wide out2 tmp2;
  pop_frame()
 

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
		   (ensures (fun h0 _ h1 -> modifies (loc u64s |+| loc f) h0 h1))
let store_felem u64s f = 
    let f3 = f.(3ul) in
    let top_bit = f3 >>. 63ul in
    f.(3ul) <- f3 &. u64 0x7fffffffffffffff;
    let carry = Core64.add1 f f (u64 19 *. top_bit) in
    let f3 = f.(3ul) in
    let top_bit = f3 >>. 63ul in
    f.(3ul) <- f3 &. u64 0x7fffffffffffffff;
    let carry = Core64.add1 f f (u64 19 *. top_bit) in
    u64s.(0ul) <- f.(0ul);
    u64s.(1ul) <- f.(1ul);
    u64s.(2ul) <- f.(2ul);
    u64s.(3ul) <- f.(3ul)

