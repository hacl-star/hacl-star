module Hacl.Impl.BignumQ.Mul

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt64

open Hacl.Spec.BignumQ.Eval

module Spec = Hacl.Spec.BignumQ.Mul


#reset-options "--max_fuel 0 --z3rlimit 20"

let h64 = Hacl.UInt64.t

val make_m:
  m:qelemB ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1
      /\ reveal_h64s (as_seq h1 m) == Spec.m))
let make_m m =
  Hacl.Lib.Create64.make_h64_5 m (uint64_to_sint64 0x12631a5cf5d3eduL)
                                 (uint64_to_sint64 0xf9dea2f79cd658uL)
                                 (uint64_to_sint64 0x000000000014deuL)
                                 (uint64_to_sint64 0x00000000000000uL)
                                 (uint64_to_sint64 0x00000010000000uL)

val make_mu:
  m:qelemB ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1
      /\ reveal_h64s (as_seq h1 m) == Spec.mu))
let make_mu m =
  Hacl.Lib.Create64.make_h64_5 m (uint64_to_sint64 0x9ce5a30a2c131buL)
                                 (uint64_to_sint64 0x215d086329a7eduL)
                                 (uint64_to_sint64 0xffffffffeb2106uL)
                                 (uint64_to_sint64 0xffffffffffffffuL)
                                 (uint64_to_sint64 0x00000fffffffffuL)

val choose:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  b:h64{v b == 0 \/ v b == 1} ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 z /\ modifies_1 z h0 h1
      /\ (reveal_h64s (as_seq h1 z) == Spec.choose (reveal_h64s (as_seq h0 x)) (reveal_h64s (as_seq h0 y)) (h64_to_u64 b))))
let choose z x y b =
  let mask = b -%^ (uint64_to_sint64 1uL) in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let z0 = ((y0 ^^ x0) &^ mask) ^^ x0 in
  let z1 = ((y1 ^^ x1) &^ mask) ^^ x1 in
  let z2 = ((y2 ^^ x2) &^ mask) ^^ x2 in
  let z3 = ((y3 ^^ x3) &^ mask) ^^ x3 in
  let z4 = ((y4 ^^ x4) &^ mask) ^^ x4 in
  Hacl.Lib.Create64.make_h64_5 z z0 z1 z2 z3 z4


let lt (a:h64{v a < pow2 63}) (b:h64{v b < pow2 63}) :
  Tot (c:h64{if v a >= v b then v c == 0x0 else v c == 0x1})
  = let r = (a -%^ b) >>^ 63ul in r

let shiftl_56 (b:h64{v b == 0 \/ v b == 1}) :
  Tot (c:h64{(v b == 1 ==> v c == 0x100000000000000) /\ (v b == 0 ==> v c == 0)})
  = assert_norm(pow2 56 = 0x100000000000000);
    b <<^ 56ul

open FStar.Mul

inline_for_extraction
val subm_step:
  x:h64{v x < 0x100000000000000} ->
  y:h64{v y <= 0x100000000000000} ->
  Tot (t:(tuple2 h64 h64){
    let b, t = t in
    (v b == 0 \/ v b == 1)
    /\ v x - v y == v t - 0x100000000000000 * v b
    /\ v t < 0x100000000000000})
let subm_step x y =
  let b  = lt x y in
  let t = (shiftl_56 b +^ x) -^ y in
  b, t

inline_for_extraction
let shiftl_40 (b:h64{v b == 0 \/ v b == 1}) :
  Tot (c:h64{(v b == 1 ==> v c == 0x10000000000) /\ (v b == 0 ==> v c == 0)})
  = assert_norm(pow2 40 = 0x10000000000);
    b <<^ 40ul

inline_for_extraction
val subm_last_step:
  x:h64{v x < 0x10000000000} ->
  y:h64{v y <= 0x10000000000} ->
  Tot (t:(tuple2 h64 h64){(v (fst t) == 0 \/ v (fst t) == 1)
    /\ v x - v y == v (snd t) - 0x10000000000 * v (fst t)
    /\ v (snd t) < 0x10000000000})
let subm_last_step x y =
  let b  = lt x y in
  let t = (shiftl_40 b +^ x) -^ y in
  b, t

#reset-options "--max_fuel 0 --z3rlimit 100"

val sub_mod_264:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z
      /\ within_56 h x /\ within_56 h y
      /\ eval_q (reveal_h64s (as_seq h x)) < pow2 264
      /\ eval_q (reveal_h64s (as_seq h y)) < pow2 264))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 z /\ modifies_1 z h0 h1
      /\ within_56 h0 x /\ within_56 h0 y
      /\ eval_q (reveal_h64s (as_seq h0 x)) < pow2 264
      /\ eval_q (reveal_h64s (as_seq h0 y)) < pow2 264
      /\ (reveal_h64s (as_seq h1 z) == Spec.sub_mod_264 (reveal_h64s (as_seq h0 x)) (reveal_h64s (as_seq h0 y)))))
let sub_mod_264 z x y =
  assert_norm(pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 32 = 0x100000000);
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let pb = y0 in
  let b  = lt x0 y0 in
  let t0 = (shiftl_56 b +^ x0) -^ (y0) in
  let y1 = y1 +^ b in
  let b  = lt x1 (y1) in
  let t1 = (shiftl_56 b +^ x1) -^ (y1) in
  let y2 = y2 +^ b in
  let b  = lt x2 (y2) in
  let t2 = (shiftl_56 b +^ x2) -^ (y2) in
  let y3 = y3 +^ b in
  let b  = lt x3 (y3) in
  let t3 = (shiftl_56 b +^ x3) -^ (y3) in
  let y4 = y4 +^ b in
  let b  = lt x4 (y4) in
  let t4 = (shiftl_40 b +^ x4) -^ (y4) in
  Hacl.Lib.Create64.make_h64_5 z t0 t1 t2 t3 t4


val subm_conditional:
  z:qelemB ->
  x:qelemB ->
  Stack unit
    (requires (fun h -> live h x /\ live h z /\ within_56 h x))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h1 z /\ modifies_1 z h0 h1 /\ within_56 h0 x
      /\ (reveal_h64s (as_seq h1 z) == Spec.subm_conditional (reveal_h64s (as_seq h0 x)))))
let subm_conditional z x =
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 32 = 0x100000000);
  push_frame();
  let h0 = ST.get() in
  let tmp = create (uint64_to_sint64 0uL) 5ul in
  let h1 = ST.get() in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  Hacl.Lib.Create64.make_h64_5 tmp x0 x1 x2 x3 x4;
  let y0 = uint64_to_sint64 0x12631a5cf5d3eduL in
  let y1 = uint64_to_sint64 0xf9dea2f79cd658uL in
  let y2 = uint64_to_sint64 0x000000000014deuL in
  let y3 = uint64_to_sint64 0x00000000000000uL in
  let y4 = uint64_to_sint64 0x00000010000000uL in
  let b  = lt x0 y0 in
  let t0 = (shiftl_56 b +^ x0) -^ (y0) in
  let y1 = y1 +^ b in
  let b  = lt x1 (y1) in
  let t1 = (shiftl_56 b +^ x1) -^ (y1) in
  let y2 = y2 +^ b in
  let b  = lt x2 (y2) in
  let t2 = (shiftl_56 b +^ x2) -^ (y2) in
  let y3 = y3 +^ b in
  let b  = lt x3 (y3) in
  let t3 = (shiftl_56 b +^ x3) -^ (y3) in
  let y4 = y4 +^ b in
  let b  = lt x4 (y4) in
  let t4 = (shiftl_56 b +^ x4) -^ (y4) in
  let h2 = ST.get() in
  lemma_modifies_0_1' tmp h0 h1 h2;
  lemma_live_disjoint h0 z tmp;
  Hacl.Lib.Create64.make_h64_5 z t0 t1 t2 t3 t4;
  choose z tmp z b;
  pop_frame()


inline_for_extraction
let op_Star_Star (x:h64{v x < 0x100000000000000}) (y:h64{v y < 0x100000000000000}) :
  Tot (z:Hacl.UInt128.t{Hacl.UInt128.v z < 0x10000000000000000000000000000 /\ Hacl.UInt128.v z = v x * v y})
  = assert_norm(0x100000000000000 * 0x100000000000000 = 0x10000000000000000000000000000);
  Spec.lemma_mul_ineq (v x) (v y) 0x100000000000000;
  Hacl.UInt128.mul_wide x y

inline_for_extraction
val split_56:
  x:Hacl.UInt128.t{Hacl.UInt128.v x < 0x100000000000000000000000000000} ->
  Tot (t:tuple2 Hacl.UInt128.t h64{
    Hacl.UInt128.v (fst t) == Hacl.UInt128.v x / 0x100000000000000
    /\ Hacl.UInt64.v (snd t) == Hacl.UInt128.v x % 0x100000000000000
    /\ Hacl.UInt128.v (fst t) <= 0x1000000000000000})
let split_56 x =
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  carry, t

inline_for_extraction
val mod_40: x:Hacl.UInt128.t -> Tot (z:h64{v z = Hacl.UInt128.v x % (pow2 40)})
let mod_40 x =
  let x' = sint128_to_sint64 x in
  let x'' = x' &^ (uint64_to_sint64 0xffffffffffuL) in
  UInt.logand_mask (v x') 40;
  assert_norm(pow2 40   = 0x10000000000);
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 40 64;
  x''


val low_mul_5:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ modifies_1 z h0 h1
      /\ within_56 h0 x /\ within_56 h0 y /\
      reveal_h64s (as_seq h1 z) == Spec.low_mul_5 (reveal_h64s (as_seq h0 x)) (reveal_h64s (as_seq h0 y))))
let low_mul_5 z x y =
  assert_norm(pow2 128  = 0x100000000000000000000000000000000);
  assert_norm(pow2 40   = 0x10000000000);
  assert_norm(pow2 56   = 0x100000000000000);
  assert_norm(pow2 112  = 0x10000000000000000000000000000);
  assert_norm(pow2 168  = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224  = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 264  = 0x1000000000000000000000000000000000000000000000000000000000000000000);
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let xy00 = x0 ** y0 in
  let xy01 = x0 ** y1 in
  let xy02 = x0 ** y2 in
  let xy03 = x0 ** y3 in
  let xy04 = x0 ** y4 in
  let xy10 = x1 ** y0 in
  let xy11 = x1 ** y1 in
  let xy12 = x1 ** y2 in
  let xy13 = x1 ** y3 in
  let xy20 = x2 ** y0 in
  let xy21 = x2 ** y1 in
  let xy22 = x2 ** y2 in
  let xy30 = x3 ** y0 in
  let xy31 = x3 ** y1 in
  let xy40 = x4 ** y0 in
  let x    = xy00 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let t0  = t in
  let x = Hacl.UInt128.(xy01 +^ xy10 +^ carry) in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let t1 = t in
  let x = Hacl.UInt128.(xy02 +^ xy11 +^ xy20 +^ carry) in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let t2 = t in
  let x = Hacl.UInt128.(xy03 +^ xy12 +^ xy21 +^ xy30 +^ carry) in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let t3 = t in
  let open Hacl.UInt128 in
  let        t4 = mod_40   (xy04 +^ xy13 +^ xy22 +^ xy31 +^ xy40 +^ carry) in
  Hacl.Lib.Create64.make_h64_5 z t0 t1 t2 t3 t4


val mul_5:
  z:buffer Hacl.UInt128.t{length z = 9} ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ modifies_1 z h0 h1
      /\ within_56 h0 x /\ within_56 h0 y /\
      reveal_h128s (as_seq h1 z) == Spec.mul_5 (reveal_h64s (as_seq h0 x)) (reveal_h64s (as_seq h0 y))))
let mul_5 z x y =
  assert_norm(pow2 128  = 0x100000000000000000000000000000000);
  assert_norm(pow2 40   = 0x10000000000);
  assert_norm(pow2 56   = 0x100000000000000);
  assert_norm(pow2 112  = 0x10000000000000000000000000000);
  assert_norm(pow2 168  = 0x1000000000000000000000000000000000000000000);
  assert_norm(pow2 224  = 0x100000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 280  = 0x10000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 336  = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 392  = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 448  = 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let xy00 = x0 ** y0 in
  let xy01 = x0 ** y1 in
  let xy02 = x0 ** y2 in
  let xy03 = x0 ** y3 in
  let xy04 = x0 ** y4 in
  let xy10 = x1 ** y0 in
  let xy11 = x1 ** y1 in
  let xy12 = x1 ** y2 in
  let xy13 = x1 ** y3 in
  let xy14 = x1 ** y4 in
  let xy20 = x2 ** y0 in
  let xy21 = x2 ** y1 in
  let xy22 = x2 ** y2 in
  let xy23 = x2 ** y3 in
  let xy24 = x2 ** y4 in
  let xy30 = x3 ** y0 in
  let xy31 = x3 ** y1 in
  let xy32 = x3 ** y2 in
  let xy33 = x3 ** y3 in
  let xy34 = x3 ** y4 in
  let xy40 = x4 ** y0 in
  let xy41 = x4 ** y1 in
  let xy42 = x4 ** y2 in
  let xy43 = x4 ** y3 in
  let xy44 = x4 ** y4 in
  let open Hacl.UInt128 in
  let z0 = xy00 in
  let z1 = xy01 +^ xy10 in
  let z2 = xy02 +^ xy11 +^ xy20 in
  let z3 = xy03 +^ xy12 +^ xy21 +^ xy30 in
  let z4 = xy04 +^ xy13 +^ xy22 +^ xy31 +^ xy40 in
  let z5 =         xy14 +^ xy23 +^ xy32 +^ xy41 in
  let z6 =                 xy24 +^ xy33 +^ xy42 in
  let z7 =                         xy34 +^ xy43 in
  let z8 =                                 xy44 in
  Hacl.Lib.Create128.make_h128_9 z z0 z1 z2 z3 z4 z5 z6 z7 z8


val carry_step:
  x:Hacl.UInt128.t -> y:Hacl.UInt128.t{Hacl.UInt128.v y < 0x50000000000000000000000000000} ->
  Tot (t:tuple2 Hacl.UInt64.t Hacl.UInt128.t{
    Hacl.UInt128.v x + 0x100000000000000 * Hacl.UInt128.v y == v (fst t) + 0x100000000000000 * Hacl.UInt128.v (snd t)
    /\ v (fst t) < 0x100000000000000})
let carry_step x y =
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  t, Hacl.UInt128.add y carry


#reset-options "--z3rlimit 100 --max_fuel 0"


val carry:
  t:buffer h64{length t = 10} ->
  z:buffer Hacl.UInt128.t{length z = 9} ->
  Stack unit
    (requires (fun h -> live h z /\ live h t /\
      (let z = as_seq h z in eval_q_wide (h128_to_u128 z.[0]) (h128_to_u128 z.[1]) (h128_to_u128 z.[2]) (h128_to_u128 z.[3]) (h128_to_u128 z.[4]) (h128_to_u128 z.[5]) (h128_to_u128 z.[6]) (h128_to_u128 z.[7]) (h128_to_u128 z.[8]) < pow2 528
    /\ Hacl.UInt128.v z.[0] < 0x10000000000000000000000000000
    /\ Hacl.UInt128.v z.[1] < 0x20000000000000000000000000000
    /\ Hacl.UInt128.v z.[2] < 0x30000000000000000000000000000
    /\ Hacl.UInt128.v z.[3] < 0x40000000000000000000000000000
    /\ Hacl.UInt128.v z.[4] < 0x50000000000000000000000000000
    /\ Hacl.UInt128.v z.[5] < 0x40000000000000000000000000000
    /\ Hacl.UInt128.v z.[6] < 0x30000000000000000000000000000
    /\ Hacl.UInt128.v z.[7] < 0x20000000000000000000000000000
    /\ Hacl.UInt128.v z.[8] < 0x10000000000000000000000000000)))
   (ensures (fun h0 _ h1 -> live h1 t /\ live h0 z /\ modifies_1 t h0 h1 /\
     (let z = as_seq h0 z in 
     eval_q_wide (h128_to_u128 z.[0]) (h128_to_u128 z.[1]) (h128_to_u128 z.[2]) (h128_to_u128 z.[3]) (h128_to_u128 z.[4]) (h128_to_u128 z.[5]) (h128_to_u128 z.[6]) (h128_to_u128 z.[7]) (h128_to_u128 z.[8]) < pow2 528
     /\ Hacl.UInt128.v z.[0] < 0x10000000000000000000000000000
     /\ Hacl.UInt128.v z.[1] < 0x20000000000000000000000000000
     /\ Hacl.UInt128.v z.[2] < 0x30000000000000000000000000000
     /\ Hacl.UInt128.v z.[3] < 0x40000000000000000000000000000
     /\ Hacl.UInt128.v z.[4] < 0x50000000000000000000000000000
     /\ Hacl.UInt128.v z.[5] < 0x40000000000000000000000000000
     /\ Hacl.UInt128.v z.[6] < 0x30000000000000000000000000000
     /\ Hacl.UInt128.v z.[7] < 0x20000000000000000000000000000
     /\ Hacl.UInt128.v z.[8] < 0x10000000000000000000000000000
     /\ reveal_h64s (as_seq h1 t) == Spec.carry (reveal_h128s (z)))))
let carry out z =
  let z0 = z.(0ul) in
  let z1 = z.(1ul) in
  let z2 = z.(2ul) in
  let z3 = z.(3ul) in
  let z4 = z.(4ul) in
  let z5 = z.(5ul) in
  let z6 = z.(6ul) in
  let z7 = z.(7ul) in
  let z8 = z.(8ul) in
  
  let x = z0  in let y = z1 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x0 = t in let z1' = Hacl.UInt128.add y carry in

  let x = z1' in let y = z2 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x1 = t in let z2' = Hacl.UInt128.add y carry in

  let x = z2' in let y = z3 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x2 = t in let z3' = Hacl.UInt128.add y carry in

  let x = z3' in let y = z4 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x3 = t in let z4' = Hacl.UInt128.add y carry in

  let x = z4' in let y = z5 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x4 = t in let z5' = Hacl.UInt128.add y carry in

  let x = z5' in let y = z6 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x5 = t in let z6' = Hacl.UInt128.add y carry in

  let x = z6' in let y = z7 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x6 = t in let z7' = Hacl.UInt128.add y carry in

  let x = z7' in let y = z8 in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x7 = t in let z8' = Hacl.UInt128.add y carry in

  let x = z8' in let y = sint64_to_sint128 (uint64_to_sint64 0uL) in
  let carry = Hacl.UInt128.(x >>^ 56ul) in
  let t     = Hacl.Cast.sint128_to_sint64 x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  UInt.logand_mask #64 (Hacl.UInt128.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt128.v x) 56 64;
  let x8 = t in let z9' = Hacl.UInt128.add y carry in
  let x9 = sint128_to_sint64 z9' in
  Hacl.Lib.Create64.make_h64_10 out x0 x1 x2 x3 x4 x5 x6 x7 x8 x9


val mod_264:
  r:qelemB ->
  t:buffer h64{length t = 10} ->
  Stack unit
    (requires (fun h -> live h r /\ live h t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h t))))
    (ensures (fun h0 _ h1 -> live h1 r /\ live h0 t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h0 t))
      /\ modifies_1 r h0 h1
      /\ reveal_h64s (as_seq h1 r) == Spec.mod_264 (reveal_h64s (as_seq h0 t))))
let mod_264 r t =
  let x0 = t.(0ul) in
  let x1 = t.(1ul) in
  let x2 = t.(2ul) in
  let x3 = t.(3ul) in
  let x4 = t.(4ul) in
  let x4' = x4 &^ (uint64_to_sint64 0xffffffffffuL) in
  Hacl.Lib.Create64.make_h64_5 r x0 x1 x2 x3 x4'

inline_for_extraction
val div_2_24_step:
  x:h64{v x < 0x100000000000000} -> y:h64 ->
  Tot (z:h64{v z = v x / pow2 24 + pow2 32 * (v y % pow2 24) /\ v z < pow2 56})
inline_for_extraction
let div_2_24_step x y =
  let y' = (y &^ uint64_to_sint64 0xffffffuL) <<^ 32ul in
  let x' = x >>^ 24ul in
  let z = y' |^ x' in
  assert_norm(pow2 24 = 0x1000000);
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  UInt.logand_mask (v y) 24;
  Math.Lemmas.modulo_lemma ((v y % pow2 24) * pow2 32) (pow2 64);
  assert(v y' = (v y % pow2 24) * pow2 32);
  UInt.logor_disjoint #64 (v y') (v x') 32;
  z


inline_for_extraction
val div_2_40_step:
  x:h64{v x < 0x100000000000000} -> y:h64 ->
  Tot (z:h64{v z = v x / pow2 40 + pow2 16 * (v y % pow2 40) /\ v z < pow2 56})
inline_for_extraction
let div_2_40_step x y =
  let y' = (y &^ uint64_to_sint64 0xffffffffffuL) <<^ 16ul in
  let x' = x >>^ 40ul in
  let z = y' |^ x' in
  assert_norm(pow2 16 = 0x10000);
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  UInt.logand_mask (v y) 40;
  Math.Lemmas.modulo_lemma ((v y % pow2 40) * pow2 16) (pow2 64);
  assert(v y' = (v y % pow2 40) * pow2 16);
  UInt.logor_disjoint #64 (v y') (v x') 16;
  z


val div_248:
  q:qelemB ->
  t:buffer h64 ->
  Stack unit
    (requires (fun h -> live h q /\ live h t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h t))
      /\ (let t = reveal_h64s (as_seq h t) in eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)))
    (ensures (fun h0 _ h1 -> live h1 q /\ live h0 t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h0 t))
      /\ modifies_1 q h0 h1
      /\ (let t = reveal_h64s (as_seq h0 t) in eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)
      /\ reveal_h64s (as_seq h1 q) == Spec.div_248 (reveal_h64s (as_seq h0 t))))
let div_248 out t =
  let x0 = t.(0ul) in
  let x1 = t.(1ul) in
  let x2 = t.(2ul) in
  let x3 = t.(3ul) in
  let x4 = t.(4ul) in
  let x5 = t.(5ul) in
  let x6 = t.(6ul) in
  let x7 = t.(7ul) in
  let x8 = t.(8ul) in
  let x9 = t.(9ul) in
  assert_norm(pow2 512 = 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 24 = 0x1000000);
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  let z0 = div_2_24_step x4 x5 in
  let z1 = div_2_24_step x5 x6 in
  let z2 = div_2_24_step x6 x7 in
  let z3 = div_2_24_step x7 x8 in
  let z4 = div_2_24_step x8 x9 in
  Hacl.Lib.Create64.make_h64_5 out z0 z1 z2 z3 z4


val div_264:
  q:qelemB ->
  t:buffer h64 ->
  Stack unit
    (requires (fun h -> live h q /\ live h t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h t))
      /\ (let t = reveal_h64s (as_seq h t) in eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 528)))
    (ensures (fun h0 _ h1 -> live h1 q /\ live h0 t /\ Spec.all_10_bellow_56 (reveal_h64s (as_seq h0 t))
      /\ modifies_1 q h0 h1
      /\ (let t = reveal_h64s (as_seq h0 t) in eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 528)
      /\ reveal_h64s (as_seq h1 q) == Spec.div_264 (reveal_h64s (as_seq h0 t))))
let div_264 out t =
  let x0 = t.(0ul) in
  let x1 = t.(1ul) in
  let x2 = t.(2ul) in
  let x3 = t.(3ul) in
  let x4 = t.(4ul) in
  let x5 = t.(5ul) in
  let x6 = t.(6ul) in
  let x7 = t.(7ul) in
  let x8 = t.(8ul) in
  let x9 = t.(9ul) in
  assert_norm(pow2 528 = 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
  assert_norm(pow2 32 = 0x100000000);
  assert_norm(pow2 40 = 0x10000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  let z0 = div_2_40_step x4 x5 in
  let z1 = div_2_40_step x5 x6 in
  let z2 = div_2_40_step x6 x7 in
  let z3 = div_2_40_step x7 x8 in
  let z4 = div_2_40_step x8 x9 in
  Hacl.Lib.Create64.make_h64_5 out z0 z1 z2 z3 z4


(* private *)
(* let lemma_mul_ineq_ (a:nat) (b:nat) (x:nat) (y:nat) : Lemma (requires (a < x /\ b < y)) (ensures (a * b < x * y)) *)
(*   = () *)

(* private *)
(* let lemma_mul_ineq__ (a:nat) (b:nat) (x:nat) (y:nat) : Lemma (requires (a < pow2 x /\ b < pow2 y)) (ensures (a * b < pow2 (x+y))) *)
(*   = lemma_mul_ineq_ a b (pow2 x) (pow2 y); *)
(*     Math.Lemmas.pow2_plus x y *)

(* private  *)
(* let lemma_ineq (a:nat) (b:nat) : Lemma (requires (a < b)) (ensures (a <= b - 1)) = () *)


#reset-options "--max_fuel 0 --z3rlimit 100"

val barrett_reduction__1:
  qmu:buffer Hacl.UInt128.t{length qmu = 9} ->
  t:buffer h64{length t = 10} ->
  mu:qelemB ->
  tmp:buffer h64{length tmp = 30 /\ disjoint tmp mu /\ disjoint tmp qmu} ->
  Stack unit
    (requires (fun h -> live h t /\ live h qmu /\ live h mu /\ live h tmp /\
      (let t = reveal_h64s (as_seq h t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512) /\
      reveal_h64s (as_seq h mu) == Spec.mu
      ))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 tmp /\ (let t = reveal_h64s (as_seq h0 t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)
      /\ within_56 h1 (Buffer.sub tmp 20ul 5ul)
      /\ (let qmu_264' = Buffer.sub tmp 20ul 5ul in
         let t = reveal_h64s (as_seq h0 t) in
         let q = Spec.div_248 t in
         Math.Lemmas.lemma_div_lt (eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9]) 512 248;
         assert_norm(pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000);
         Spec.lemma_mul_ineq__ (eval_q q) (eval_q Spec.mu) 264 264;
         let qmu = Spec.mul_5 q Spec.mu in
         let qmu' = Spec.carry qmu in
         let qmu_264 = Spec.div_264 qmu' in
         reveal_h64s (as_seq h1 qmu_264') == qmu_264)
      /\ modifies_2 qmu tmp h0 h1
    ))

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let barrett_reduction__1 qmu t mu tmp =
  let q   = Buffer.sub tmp 0ul 5ul in
  let qmu'  = Buffer.sub tmp 10ul 10ul in
  let qmu_264 = Buffer.sub tmp 20ul 5ul in
  let h0 = ST.get() in
  div_248 q t;
  let h1 = ST.get() in
  no_upd_lemma_1 h0 h1 q qmu;
  no_upd_lemma_1 h0 h1 q mu;
  Math.Lemmas.lemma_div_lt
    (let t = reveal_h64s (as_seq h0 t) in
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9]) 512 248;
  assert_norm(pow2 264 = 0x1000000000000000000000000000000000000000000000000000000000000000000);
  Spec.lemma_mul_ineq__
    (eval_q (reveal_h64s (as_seq h1 q))) (eval_q (reveal_h64s (as_seq h1 mu))) 264 264;
  mul_5 qmu q mu;
  let h2 = ST.get() in
  carry qmu' qmu;
  let h3 = ST.get() in
  div_264 qmu_264 qmu';
  let h4 = ST.get() in
//  assert (modifies_1 tmp h0 h1);
//  assert (modifies_1 qmu h1 h2);
//  assert (modifies_1 tmp h2 h3);
//  assert (modifies_1 tmp h3 h4);
  lemma_modifies_1_1 tmp qmu h0 h1 h2;
  lemma_modifies_2_1' tmp qmu h0 h2 h3;
  lemma_modifies_2_1' tmp qmu h0 h3 h4

#reset-options "--max_fuel 0 --z3rlimit 100"

val barrett_reduction__2:
  t:buffer h64{length t = 10} ->
  m:qelemB ->
  tmp:buffer h64{length tmp = 30 /\ disjoint tmp m /\ disjoint tmp t} ->
  Stack unit
    (requires (fun h -> live h t /\ live h m /\ live h tmp /\
      (let t = reveal_h64s (as_seq h t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512) /\
      reveal_h64s (as_seq h m) == Spec.m /\
      within_56 h (Buffer.sub tmp 20ul 5ul)
      ))
    (ensures (fun h0 _ h1 -> live h0 t /\ live h1 tmp /\ live h0 tmp /\ live h0 m /\ (let t = reveal_h64s (as_seq h0 t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)
      /\ within_56 h0 (Buffer.sub tmp 20ul 5ul)
      /\ within_56 h1 (Buffer.sub tmp 25ul 5ul)
      /\ (let qmu_264 = reveal_h64s (as_seq h0 (Buffer.sub tmp 20ul 5ul)) in
         let s' = reveal_h64s (as_seq h1 (Buffer.sub tmp 25ul 5ul)) in
         let qmul = Spec.low_mul_5 qmu_264 Spec.m in
         let r    = Spec.mod_264 (reveal_h64s (as_seq h0 t)) in
         let s = Spec.sub_mod_264 r qmul in
         s' == s)
      /\ modifies_1 tmp h0 h1
    ))


#reset-options "--max_fuel 0 --z3rlimit 100"

let barrett_reduction__2 t m tmp =
  let qmul = Buffer.sub tmp 0ul 5ul in
  let r    = Buffer.sub tmp 5ul 5ul in
  let qmu_264 = Buffer.sub tmp 20ul 5ul in
  let s    = Buffer.sub tmp 25ul 5ul in
  let h1   = ST.get() in
  Math.Lemmas.lemma_div_lt (let t = reveal_h64s (as_seq h1 t) in eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9]) 512 248;
  mod_264 r t;
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 r m;
  let h5 = ST.get() in
  low_mul_5 qmul qmu_264 m;
  let h6 = ST.get() in
  no_upd_lemma_1 h5 h6 qmul r;
  sub_mod_264 s r qmul


#reset-options "--max_fuel 0 --z3rlimit 100"

inline_for_extraction
val barrett_reduction__:
  z:qelemB ->
  t:buffer h64{length t = 10} ->
  m:qelemB ->
  mu:qelemB ->
  tmp:buffer h64{length tmp = 30 /\ disjoint tmp t /\ disjoint tmp mu /\ disjoint tmp m /\ disjoint tmp z} ->
  Stack unit
    (requires (fun h -> live h z /\ live h t /\ live h m /\ live h mu /\ live h tmp /\
      (let t = reveal_h64s (as_seq h t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512) /\
      reveal_h64s (as_seq h m) == Spec.m /\
      reveal_h64s (as_seq h mu) == Spec.mu
      ))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 t /\ (let t = reveal_h64s (as_seq h0 t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)
      /\ reveal_h64s (as_seq h1 z) == Spec.barrett_reduction (reveal_h64s (as_seq h0 t))
      /\ modifies_2 z tmp h0 h1
    ))


#reset-options "--max_fuel 0 --z3rlimit 100"

let lemma_modifies_1 #a #a' h h' (b:buffer a) (b':buffer a') : Lemma
  (requires (live h b /\ live h b' /\ modifies_1 b h h'))
  (ensures (live h' b'))
  = lemma_reveal_modifies_1 b h h'

#reset-options "--max_fuel 0 --z3rlimit 10"

let lemma_sub_eq h h' (b:buffer h64{live h b /\ live h' b /\ length b = 30}) : Lemma
  (requires (within_56 h (Buffer.sub b 25ul 5ul) /\ as_seq h' b == as_seq h b))
  (ensures (within_56 h' (Buffer.sub b 25ul 5ul)))
  = ()

#reset-options "--max_fuel 0 --z3rlimit 200"

let barrett_reduction__ z t m mu tmp =
  let s   = Buffer.sub tmp 25ul 5ul in
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let qmu = create (uint64_to_sint128 0uL) 9ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 m;
  no_upd_lemma_0 h1 h2 mu;
  no_upd_lemma_0 h1 h2 t;
  barrett_reduction__1 qmu t mu tmp;
  let h3 = ST.get() in
  assert(modifies_2_1 tmp h1 h3);
  no_upd_lemma_2 h2 h3 qmu tmp t;
  no_upd_lemma_2 h2 h3 qmu tmp m;
  barrett_reduction__2 t m tmp;
  let h4 = ST.get() in
  assert(within_56 h4 s);
  pop_frame();
  let h5 = ST.get() in
  assert(as_seq h4 tmp == as_seq h5 tmp);
  lemma_sub_eq h4 h5 tmp;
  assert(within_56 h5 s);
  assert(modifies_1 tmp h0 h5);
  lemma_modifies_1 h0 h5 tmp z;
  subm_conditional z s;
  let h6 = ST.get() in
  ()


#reset-options "--max_fuel 0 --z3rlimit 100"

private
val lemma_modifies_0_2_: #a:Type -> #a':Type -> #a'':Type -> h0:mem -> h1:mem -> h2:mem -> b:buffer a -> b':buffer a' -> b'':buffer a'' ->
  Lemma (requires (live h0 b /\ live h0 b' /\ ~(contains h0 b'') /\ live h1 b'' /\ frameOf b'' = (HS.get_tip h0)
    /\ modifies_0 h0 h1 /\ modifies_2 b b' h1 h2))
       (ensures (modifies_3_2 b b' h0 h2))
let lemma_modifies_0_2_ #a #a' #a'' h0 h1 h2 b b' b'' =
  lemma_reveal_modifies_0 h0 h1;
  lemma_reveal_modifies_2 b b' h1 h2;
  lemma_intro_modifies_3_2 b b' h0 h2

inline_for_extraction
val barrett_reduction_:
  z:qelemB ->
  t:buffer h64{length t = 10} ->
  Stack unit
    (requires (fun h -> live h z /\ live h t /\ (let t = reveal_h64s (as_seq h t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 t /\ (let t = reveal_h64s (as_seq h0 t) in
      Spec.all_10_bellow_56 t /\
      eval_q_10 t.[0] t.[1] t.[2] t.[3] t.[4] t.[5] t.[6] t.[7] t.[8] t.[9] < pow2 512)
      /\ reveal_h64s (as_seq h1 z) == Spec.barrett_reduction (reveal_h64s (as_seq h0 t))
      /\ modifies_1 z h0 h1
    ))

#reset-options "--max_fuel 0 --z3rlimit 200"

let barrett_reduction_ z t =
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let tmp = create (uint64_to_sint64 0uL) 40ul in
  let m   = Buffer.sub tmp 0ul 5ul in
  let mu  = Buffer.sub tmp 5ul 5ul in
  let tmp = Buffer.sub tmp 10ul 30ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 t;
  make_m m;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 m t;
  make_mu mu;
  let h4 = ST.get() in
  no_upd_lemma_1 h3 h4 mu m;
  no_upd_lemma_1 h3 h4 mu t;
  barrett_reduction__ z t m mu tmp;
  let h5 = ST.get() in
  assert(modifies_2_1 z h1 h5);
  pop_frame();
  let h6 = ST.get() in
  assert(modifies_1 z h0 h6);
  assert(as_seq h6 z == as_seq h5 z);
  assert(as_seq h4 t == as_seq h0 t)

let barrett_reduction z t =
  barrett_reduction_ z t


(* val mul_modq_: *)
(*   z:qelemB -> *)
(*   x:qelemB -> *)
(*   y:qelemB -> *)
(*   z':buffer Hacl.UInt64.t{length z' = 10 /\ disjoint } -> *)
(*   z'':buffer Hacl.UInt64.t{length z'' = 9} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y /\ *)
(*       (let x = as_seq h x in let y = as_seq h y in *)
(*       eval_q x < pow2 256 /\ eval_q y < pow2 256))) *)
(*     (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ *)
(*       (let x = as_seq h0 x in let y = as_seq h0 y in *)
(*        eval_q x < pow2 256 /\ eval_q y < pow2 256) /\ *)
(*        eval_q (as_seq h1 z) == (eval_q (as_seq h0 x) * eval_q (as_seq h0 y)) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)) *)

#reset-options "--max_fuel 0 --z3rlimit 40"

let mul_modq out x y =
  assert_norm(pow2 32 = 0x100000000);
  let h0 = ST.get() in
  push_frame();
  let h1 = ST.get() in
  let z' = create (uint64_to_sint64 0uL) 10ul in
  let h2 = ST.get() in
  no_upd_lemma_0 h1 h2 x;
  no_upd_lemma_0 h1 h2 y;
  no_upd_lemma_0 h1 h2 out;
  push_frame();
  let h3 = ST.get() in
  let z  = create (uint64_to_sint128 0uL) 9ul in
  let h4 = ST.get() in
  no_upd_lemma_0 h3 h4 x;
  no_upd_lemma_0 h3 h4 y;
  no_upd_lemma_0 h3 h4 out;
  no_upd_lemma_0 h3 h4 z';
  Spec.lemma_mul_ineq__ (eval_q (reveal_h64s (as_seq h0 x))) (eval_q (reveal_h64s (as_seq h0 y))) 256 256;
  assert(as_seq h4 x == as_seq h0 x);
  assert(as_seq h4 y == as_seq h0 y);
  mul_5 z x y;
  let h5 = ST.get() in
  lemma_modifies_0_1' z h3 h4 h5;
  no_upd_lemma_1 h4 h5 z out;
  no_upd_lemma_1 h4 h5 z z';
  assert(modifies_0 h3 h5);
  Math.Lemmas.pow2_lt_compat 528 512;
  carry z' z;
  let h6 = ST.get() in
  lemma_modifies_0_1 z' h3 h5 h6;
  no_upd_lemma_1 h5 h6 z' out;
  assert(modifies_2_1 z' h3 h6);
  pop_frame();
  let h7 = ST.get() in
  modifies_popped_1 z' h2 h3 h6 h7;
  lemma_modifies_0_1' z' h1 h2 h7;
  assert(modifies_0 h1 h7);
  barrett_reduction_ out z';
  let h8 = ST.get() in
  assert(live h8 out);
  assert(live h0 x);
  assert(live h0 y);
  assert(let out = reveal_h64s (as_seq h8 out) in
         let x = reveal_h64s (as_seq h0 x) in
         let y = reveal_h64s (as_seq h0 y) in
         out == Spec.mul_modq x y);
  assert(modifies_2_1 out h1 h8);
  pop_frame();
  let h9 = ST.get() in
  modifies_popped_1 out h0 h1 h8 h9


(* val add_modq: *)
(*   z:qelemB -> *)
(*   x:qelemB -> *)
(*   y:qelemB -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y /\ *)
(*       (let x = as_seq h x in let y = as_seq h y in *)
(*       eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\ *)
(*       eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed))) *)
(*     (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\  *)
(*       (let x = as_seq h0 x in let y = as_seq h0 y in *)
(*        eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\ *)
(*        eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) /\ *)
(*        eval_q (as_seq h1 z) == (eval_q (as_seq h0 x) + eval_q (as_seq h0 y)) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)) *)


val add_modq_:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h z /\ live h x /\ live h y /\ within_56 h x /\ within_56 h y /\
      (let x = reveal_h64s (as_seq h x) in let y = reveal_h64s (as_seq h y) in
      eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\
      eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)))
    (ensures (fun h0 _ h1 -> live h1 z /\ live h0 x /\ live h0 y /\ within_56 h0 x /\ within_56 h0 y /\
      modifies_1 z h0 h1 /\
      (let x = reveal_h64s (as_seq h0 x) in let y = reveal_h64s (as_seq h0 y) in
       eval_q x < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed /\
       eval_q y < 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) /\
       reveal_h64s (as_seq h1 z) == Spec.add_modq (reveal_h64s (as_seq h0 x)) (reveal_h64s (as_seq h0 y))))
       (* eval_q (as_seq h1 z) == (eval_q (as_seq h0 x) + eval_q (as_seq h0 y)) % 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed)) *)

#reset-options "--max_fuel 0 --z3rlimit 200"

let add_modq_ out x y =
  let h0 = ST.get() in
  push_frame();
  let tmp = create (uint64_to_sint64 0uL) 5ul in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  let y0 = y.(0ul) in
  let y1 = y.(1ul) in
  let y2 = y.(2ul) in
  let y3 = y.(3ul) in
  let y4 = y.(4ul) in
  let z0 = x0 +^ y0 in
  let z1 = x1 +^ y1 in
  let z2 = x2 +^ y2 in
  let z3 = x3 +^ y3 in
  let z4 = x4 +^ y4 in
  let x = z0  in let y = z1 in
  let carry = Hacl.UInt64.(x >>^ 56ul) in
  let t     = x &^ (uint64_to_sint64 0xffffffffffffffuL) in
  assert_norm(pow2 56 = 0x100000000000000);
  UInt.logand_mask #64 (Hacl.UInt64.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt64.v x) 56 64;
  let x0 = t in let z1' = Hacl.UInt64.add y carry in
  let x = z1' in let y = z2 in
  let carry = Hacl.UInt64.(x >>^ 56ul) in
  let t     = x &^ uint64_to_sint64 0xffffffffffffffuL in
  UInt.logand_mask #64 (Hacl.UInt64.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt64.v x) 56 64;
  let x1 = t in let z2' = Hacl.UInt64.add y carry in
  let x = z2' in let y = z3 in
  let carry = Hacl.UInt64.(x >>^ 56ul) in
  let t     = x &^ uint64_to_sint64 0xffffffffffffffuL in
  UInt.logand_mask #64 (Hacl.UInt64.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt64.v x) 56 64;
  let x2 = t in let z3' = Hacl.UInt64.add y carry in
  let x = z3' in let y = z4 in
  let carry = Hacl.UInt64.(x >>^ 56ul) in
  let t     = x &^ uint64_to_sint64 0xffffffffffffffuL in
  UInt.logand_mask #64 (Hacl.UInt64.v x % pow2 64) 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 (Hacl.UInt64.v x) 56 64;
  let x3 = t in let x4 = Hacl.UInt64.add y carry in
  Hacl.Lib.Create64.make_h64_5 tmp x0 x1 x2 x3 x4;
  subm_conditional out tmp;
  pop_frame()

let add_modq out x y = add_modq_ out x y
