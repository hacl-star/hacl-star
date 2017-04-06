module Hacl.Impl.BignumQ.Mul

open FStar.HyperStack
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt64

open Hacl.Spec.BignumQ.Eval

module Spec = Hacl.Spec.BignumQ.Mul

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let h64 = Hacl.UInt64.t
let qelemB = b:buffer h64{length b = 5}

let within_56 (h:mem) (b:qelemB) : GTot Type0 =
  live h b /\ (let b = as_seq h b in
    v b.[0] < 0x100000000000000 /\ v b.[1] < 0x100000000000000 /\ v b.[2] < 0x100000000000000 /\ 
    v b.[3] < 0x100000000000000 /\ v b.[4] < 0x100000000000000)

val make_m:
  m:qelemB ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1
      /\ as_seq h1 m == Spec.m))
let make_m m =
  Hacl.Lib.Create64.make_h64_5 m 0x12631a5cf5d3eduL 0xf9dea2f79cd658uL 0x000000000014deuL
                              0x00000000000000uL 0x00000010000000uL

val make_mu:
  m:qelemB ->
  Stack unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1
      /\ as_seq h1 m == Spec.mu))
let make_mu m =
  Hacl.Lib.Create64.make_h64_5 m 0x9ce5a30a2c131buL 0x215d086329a7eduL 0xffffffffeb2106uL
                              0xffffffffffffffuL 0x00000fffffffffuL

val choose:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  b:h64{v b == 0 \/ v b == 1} ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 z /\ modifies_1 z h0 h1
      /\ (as_seq h1 z == Spec.choose (as_seq h0 x) (as_seq h0 y) (b))))
let choose z x y b =
  let mask = b -%^ 1uL in
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

let shiftl_56 (b:h64{b == 0uL \/ b == 1uL}) :
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
let shiftl_40 (b:u64{b == 0uL \/ b == 1uL}) :
  Tot (c:u64{(b == 1uL ==> c == 0x10000000000uL) /\ (b == 0uL ==> c == 0uL)})
  = assert_norm(pow2 40 = 0x10000000000);
    b <<^ 40ul

inline_for_extraction
val subm_last_step:
  x:u64{v x < 0x10000000000} ->
  y:u64{v y <= 0x10000000000} ->
  Tot (t:(tuple2 u64 u64){(fst t == 0uL \/ fst t == 1uL)
    /\ v x - v y == v (snd t) - 0x10000000000 * v (fst t)
    /\ v (snd t) < 0x10000000000})
let subm_last_step x y =
  let b  = lt x y in
  let t = (shiftl_40 b +^ x) -^ y in
  b, t

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

val sub_mod_264:
  z:qelemB ->
  x:qelemB ->
  y:qelemB ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z
      /\ within_56 h x /\ within_56 h y
      /\ eval_q (as_seq h x) < pow2 264
      /\ eval_q (as_seq h y) < pow2 264))
    (ensures (fun h0 _ h1 -> live h0 x /\ live h0 y /\ live h1 z /\ modifies_1 z h0 h1
      /\ within_56 h0 x /\ within_56 h0 y
      /\ eval_q (as_seq h0 x) < pow2 264
      /\ eval_q (as_seq h0 y) < pow2 264
      /\ (as_seq h1 z == Spec.sub_mod_264 (as_seq h0 x) (as_seq h0 y))))
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
  (* let (b, t0) : Tot _ (\* : Tot (tuple2 h64 h64) *\) = subm_step x0 y0 <: Tot (tuple2 h64 h64) in *)
  (* let (b, t1) (\* : Tot _) *\) = subm_step x1 (y1+^b) <: Tot (tuple2 h64 h64) in *)
  (* let (b, t2) (\* : Tot _) *\) = subm_step x2 (y2+^b) <: Tot (tuple2 h64 h64) in *)
  (* let (b, t3) (\* : Tot _)  *\)= subm_step x3 (y3+^b) <: Tot (tuple2 h64 h64) in *)
  (* let (b, t4) (\* : Tot _) *\) = subm_last_step x4 (y4+^b) <: Tot (tuple2 h64 h64) in *)
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
      /\ (as_seq h1 z == Spec.subm_conditional (as_seq h0 x))))
let subm_conditional z x =
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 56 = 0x100000000000000);
  assert_norm(pow2 32 = 0x100000000);
  push_frame();
  let tmp = create 0uL 5ul in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  Hacl.Lib.Create64.make_h64_5 tmp x0 x1 x2 x3 x4;
  let y0 = 0x12631a5cf5d3eduL in
  let y1 = 0xf9dea2f79cd658uL in
  let y2 = 0x000000000014deuL in
  let y3 = 0x00000000000000uL in
  let y4 = 0x00000010000000uL in
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
  Hacl.Lib.Create64.make_h64_5 z t0 t1 t2 t3 t4;
  choose z tmp z b;
  pop_frame()

