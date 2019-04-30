module Hacl.Impl.BignumQ.Mul

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

inline_for_extraction noextract
val make_m:
  m:qelemB ->
  Stack unit
    (requires fun h -> live h m)
    (ensures  fun h0 _ h1 -> modifies (loc m) h0 h1)
let make_m m =
  m.(0ul) <- u64 0x12631a5cf5d3ed;
  m.(1ul) <- u64 0xf9dea2f79cd658;
  m.(2ul) <- u64 0x000000000014de;
  m.(3ul) <- u64 0x00000000000000;
  m.(4ul) <- u64 0x00000010000000

inline_for_extraction noextract
val make_mu:
  m:qelemB ->
  Stack unit
    (requires fun h -> live h m)
    (ensures  fun h0 _ h1 -> modifies (loc m) h0 h1)
let make_mu m =
  m.(0ul) <- u64 0x9ce5a30a2c131b;
  m.(1ul) <- u64 0x215d086329a7ed;
  m.(2ul) <- u64 0xffffffffeb2106;
  m.(3ul) <- u64 0xffffffffffffff;
  m.(4ul) <- u64 0x00000fffffffff

inline_for_extraction noextract
val choose:
    z:qelemB
  -> x:qelemB
  -> y:qelemB
  -> b:uint64{v b == 0 \/ v b == 1} ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h z)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)
let choose z x y b =
  let mask = b -. u64 1 in
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
  let z0 = ((y0 ^. x0) &. mask) ^. x0 in
  let z1 = ((y1 ^. x1) &. mask) ^. x1 in
  let z2 = ((y2 ^. x2) &. mask) ^. x2 in
  let z3 = ((y3 ^. x3) &. mask) ^. x3 in
  let z4 = ((y4 ^. x4) &. mask) ^. x4 in
  Hacl.Bignum25519.make_u64_5 z z0 z1 z2 z3 z4

inline_for_extraction noextract
let lt (a:uint64) (b:uint64) : uint64 = (a -. b) >>. 63ul

inline_for_extraction noextract
let shiftl_56 (b:uint64) : uint64 = b <<. 56ul

inline_for_extraction noextract
val subm_step: x:uint64 -> y:uint64 -> uint64 & uint64
let subm_step x y =
  let b  = lt x y in
  let t = (shiftl_56 b +. x) -. y in
  b, t

inline_for_extraction noextract
let shiftl_40 (b:uint64) : uint64 = b <<. 40ul

inline_for_extraction noextract
val subm_last_step: x:uint64 -> y:uint64 -> uint64 & uint64
let subm_last_step x y =
  let b  = lt x y in
  let t = (shiftl_40 b +. x) -. y in
  b, t

inline_for_extraction noextract
val sub_mod_264:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h z)
    (ensures fun h0 _ h1 -> modifies (loc z) h0 h1)
let sub_mod_264 z x y =
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
  let t0 = (shiftl_56 b +. x0) -. y0 in
  let y1 = y1 +. b in
  let b  = lt x1 y1 in
  let t1 = (shiftl_56 b +. x1) -. y1 in
  let y2 = y2 +. b in
  let b  = lt x2 y2 in
  let t2 = (shiftl_56 b +. x2) -. y2 in
  let y3 = y3 +. b in
  let b  = lt x3 y3 in
  let t3 = (shiftl_56 b +. x3) -. y3 in
  let y4 = y4 +. b in
  let b  = lt x4 y4 in
  let t4 = (shiftl_40 b +. x4) -. y4 in
  Hacl.Bignum25519.make_u64_5 z t0 t1 t2 t3 t4

inline_for_extraction noextract
val subm_conditional:
    z:qelemB
  -> x:qelemB ->
  Stack unit
    (requires fun h -> live h x /\ live h z /\ disjoint x z)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)
let subm_conditional z x =
  let h' = ST.get () in
  push_frame();
  let tmp = create 5ul (u64 0) in
  let h0 = ST.get () in
  let x0 = x.(0ul) in
  let x1 = x.(1ul) in
  let x2 = x.(2ul) in
  let x3 = x.(3ul) in
  let x4 = x.(4ul) in
  Hacl.Bignum25519.make_u64_5 tmp x0 x1 x2 x3 x4;

  let y0 = u64 0x12631a5cf5d3ed in
  let y1 = u64 0xf9dea2f79cd658 in
  let y2 = u64 0x000000000014de in
  let y3 = u64 0x00000000000000 in
  let y4 = u64 0x00000010000000 in
  let b  = lt x0 y0 in
  let t0 = (shiftl_56 b +. x0) -. y0 in
  let y1 = y1 +. b in
  let b  = lt x1 y1 in
  let t1 = (shiftl_56 b +. x1) -. y1 in
  let y2 = y2 +. b in
  let b  = lt x2 y2 in
  let t2 = (shiftl_56 b +. x2) -. y2 in
  let y3 = y3 +. b in
  let b  = lt x3 y3 in
  let t3 = (shiftl_56 b +. x3) -. y3 in
  let y4 = y4 +. b in
  let b  = lt x4 y4 in
  let t4 = (shiftl_56 b +. x4) -. y4 in
  Hacl.Bignum25519.make_u64_5 z t0 t1 t2 t3 t4;
  choose z tmp z b;
  pop_frame()

inline_for_extraction noextract
val split_56: x:uint128 -> uint128 & uint64
let split_56 x =
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  carry, t

inline_for_extraction noextract
val mod_40: x:uint128 -> uint64
let mod_40 x =
  let x' = to_u64 x in
  let x'' = x' &. u64 0xffffffffff in
  x''

inline_for_extraction noextract
val low_mul_5:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h -> live h z /\ live h x /\ live h y)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)
let low_mul_5 z x y =
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
  let xy00 = mul64_wide x0 y0 in
  let xy01 = mul64_wide x0 y1 in
  let xy02 = mul64_wide x0 y2 in
  let xy03 = mul64_wide x0 y3 in
  let xy04 = mul64_wide x0 y4 in
  let xy10 = mul64_wide x1 y0 in
  let xy11 = mul64_wide x1 y1 in
  let xy12 = mul64_wide x1 y2 in
  let xy13 = mul64_wide x1 y3 in
  let xy20 = mul64_wide x2 y0 in
  let xy21 = mul64_wide x2 y1 in
  let xy22 = mul64_wide x2 y2 in
  let xy30 = mul64_wide x3 y0 in
  let xy31 = mul64_wide x3 y1 in
  let xy40 = mul64_wide x4 y0 in
  let x    = xy00 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let t0  = t in
  let x = xy01 +. xy10 +. carry in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let t1 = t in
  let x = xy02 +. xy11 +. xy20 +. carry in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let t2 = t in
  let x = xy03 +. xy12 +. xy21 +. xy30 +. carry in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let t3 = t in
  let t4 = mod_40 (xy04 +. xy13 +. xy22 +. xy31 +. xy40 +. carry) in
  Hacl.Bignum25519.make_u64_5 z t0 t1 t2 t3 t4

inline_for_extraction noextract
val mul_5:
    z:lbuffer uint128 9ul
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h -> live h z /\ live h x /\ live h y)
    (ensures fun h0 _ h1 -> modifies (loc z) h0 h1)
let mul_5 z x y =
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
  let xy00 = mul64_wide x0 y0 in
  let xy01 = mul64_wide x0 y1 in
  let xy02 = mul64_wide x0 y2 in
  let xy03 = mul64_wide x0 y3 in
  let xy04 = mul64_wide x0 y4 in
  let xy10 = mul64_wide x1 y0 in
  let xy11 = mul64_wide x1 y1 in
  let xy12 = mul64_wide x1 y2 in
  let xy13 = mul64_wide x1 y3 in
  let xy14 = mul64_wide x1 y4 in
  let xy20 = mul64_wide x2 y0 in
  let xy21 = mul64_wide x2 y1 in
  let xy22 = mul64_wide x2 y2 in
  let xy23 = mul64_wide x2 y3 in
  let xy24 = mul64_wide x2 y4 in
  let xy30 = mul64_wide x3 y0 in
  let xy31 = mul64_wide x3 y1 in
  let xy32 = mul64_wide x3 y2 in
  let xy33 = mul64_wide x3 y3 in
  let xy34 = mul64_wide x3 y4 in
  let xy40 = mul64_wide x4 y0 in
  let xy41 = mul64_wide x4 y1 in
  let xy42 = mul64_wide x4 y2 in
  let xy43 = mul64_wide x4 y3 in
  let xy44 = mul64_wide x4 y4 in
  let z0 = xy00 in
  let z1 = xy01 +. xy10 in
  let z2 = xy02 +. xy11 +. xy20 in
  let z3 = xy03 +. xy12 +. xy21 +. xy30 in
  let z4 = xy04 +. xy13 +. xy22 +. xy31 +. xy40 in
  let z5 =         xy14 +. xy23 +. xy32 +. xy41 in
  let z6 =                 xy24 +. xy33 +. xy42 in
  let z7 =                         xy34 +. xy43 in
  let z8 =                                 xy44 in
  Hacl.Bignum25519.make_u128_9 z z0 z1 z2 z3 z4 z5 z6 z7 z8

inline_for_extraction noextract
val carry_step:
  x:uint128 -> y:uint128 -> uint64 & uint128
let carry_step x y =
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  t, y +. carry

inline_for_extraction noextract
val carry:
  t:lbuffer uint64 10ul
  -> z:lbuffer uint128 9ul ->
  Stack unit
    (requires fun h -> live h z /\ live h t)
    (ensures  fun h0 _ h1 -> modifies (loc t) h0 h1)
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
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x0 = t in let z1' = y +. carry in

  let x = z1' in let y = z2 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x1 = t in let z2' = y +. carry in

  let x = z2' in let y = z3 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x2 = t in let z3' = y +. carry in

  let x = z3' in let y = z4 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x3 = t in let z4' = y +. carry in

  let x = z4' in let y = z5 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x4 = t in let z5' = y +. carry in

  let x = z5' in let y = z6 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x5 = t in let z6' = y +. carry in

  let x = z6' in let y = z7 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x6 = t in let z7' = y +. carry in

  let x = z7' in let y = z8 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x7 = t in let z8' = y +. carry in

  let x = z8' in let y = u128 0 in
  let carry = x >>. 56ul in
  let t     = to_u64 x &. u64 0xffffffffffffff in
  let x8 = t in let z9' = y +. carry in
  let x9 = to_u64 z9' in
  Hacl.Bignum25519.make_u64_10 out x0 x1 x2 x3 x4 x5 x6 x7 x8 x9

inline_for_extraction noextract
val mod_264:
    r:qelemB
  -> t:lbuffer uint64 10ul ->
  Stack unit
    (requires fun h -> live h r /\ live h t)
    (ensures  fun h0 _ h1 ->  modifies (loc r) h0 h1)
let mod_264 r t =
  let x0 = t.(0ul) in
  let x1 = t.(1ul) in
  let x2 = t.(2ul) in
  let x3 = t.(3ul) in
  let x4 = t.(4ul) in
  let x4' = x4 &. u64 0xffffffffff in
  Hacl.Bignum25519.make_u64_5 r x0 x1 x2 x3 x4'

inline_for_extraction noextract
val div_2_24_step: x:uint64 -> y:uint64 -> uint64
let div_2_24_step x y =
  let y' = (y &. u64 0xffffff) <<. 32ul in
  let x' = x >>. 24ul in
  let z = y' |. x' in
  z

inline_for_extraction noextract
val div_2_40_step: x:uint64 -> y:uint64 -> uint64
let div_2_40_step x y =
  let y' = (y &. u64 0xffffffffff) <<. 16ul in
  let x' = x >>. 40ul in
  let z = y' |. x' in
  z

inline_for_extraction noextract
val div_248:
    q:qelemB
  -> t:lbuffer uint64 10ul ->
  Stack unit
    (requires fun h -> live h q /\ live h t)
    (ensures  fun h0 _ h1 -> modifies (loc q) h0 h1)
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
  let z0 = div_2_24_step x4 x5 in
  let z1 = div_2_24_step x5 x6 in
  let z2 = div_2_24_step x6 x7 in
  let z3 = div_2_24_step x7 x8 in
  let z4 = div_2_24_step x8 x9 in
  Hacl.Bignum25519.make_u64_5 out z0 z1 z2 z3 z4

inline_for_extraction noextract
val div_264:
    q:qelemB
  -> t:lbuffer uint64 10ul ->
  Stack unit
    (requires fun h -> live h q /\ live h t)
    (ensures  fun h0 _ h1 -> modifies (loc q) h0 h1)
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
  let z0 = div_2_40_step x4 x5 in
  let z1 = div_2_40_step x5 x6 in
  let z2 = div_2_40_step x6 x7 in
  let z3 = div_2_40_step x7 x8 in
  let z4 = div_2_40_step x8 x9 in
  Hacl.Bignum25519.make_u64_5 out z0 z1 z2 z3 z4

inline_for_extraction noextract
val barrett_reduction__1:
    qmu:lbuffer uint128 9ul
  -> t:lbuffer uint64 10ul
  -> mu:qelemB
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h t /\ live h qmu /\ live h mu /\ live h tmp /\
      disjoint tmp mu /\ disjoint tmp qmu)
    (ensures fun h0 _ h1 ->  modifies (loc qmu |+| loc tmp) h0 h1)
let barrett_reduction__1 qmu t mu tmp =
  let q   = sub tmp 0ul 5ul in
  let qmu'  = sub tmp 10ul 10ul in
  let qmu_264 = sub tmp 20ul 5ul in
  div_248 q t;
  mul_5 qmu q mu;
  carry qmu' qmu;
  div_264 qmu_264 qmu'

inline_for_extraction noextract
val barrett_reduction__2:
    t:lbuffer uint64 10ul
  -> m:qelemB
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h t /\ live h m /\ live h tmp /\
      disjoint tmp m /\ disjoint tmp t)
    (ensures fun h0 _ h1 -> modifies (loc tmp) h0 h1)
let barrett_reduction__2 t m tmp =
  let qmul = sub tmp 0ul 5ul in
  let r    = sub tmp 5ul 5ul in
  let qmu_264 = sub tmp 20ul 5ul in
  let s    = sub tmp 25ul 5ul in
  mod_264 r t;
  low_mul_5 qmul qmu_264 m;
  sub_mod_264 s r qmul

inline_for_extraction noextract
val barrett_reduction__:
    z:qelemB
  -> t:lbuffer uint64 10ul
  -> m:qelemB
  -> mu:qelemB
  -> tmp:lbuffer uint64 30ul ->
  Stack unit
    (requires fun h ->
      live h z /\ live h t /\ live h m /\ live h mu /\ live h tmp /\
      disjoint tmp t /\ disjoint tmp mu /\ disjoint tmp m /\ disjoint tmp z)
    (ensures fun h0 _ h1 -> modifies (loc z |+| loc tmp) h0 h1)
let barrett_reduction__ z t m mu tmp =
  let s   = sub tmp 25ul 5ul in
  push_frame();
  let qmu = create 9ul (u128 0) in
  let h0 = ST.get () in
  barrett_reduction__1 qmu t mu tmp;
  let h1 = ST.get () in
  assert (modifies (loc qmu |+| loc tmp) h0 h1);
  barrett_reduction__2 t m tmp;
  let h2 = ST.get () in
  assert (modifies (loc tmp) h1 h2);
  assert (modifies (loc qmu |+| loc tmp) h0 h2);
  subm_conditional z s;
  let h3 = ST.get () in
  assert (modifies (loc z) h2 h3);
  assert (modifies (loc qmu |+| loc tmp |+| loc z) h0 h3);
  pop_frame()

inline_for_extraction noextract
val barrett_reduction_:
    z:qelemB
  -> t:lbuffer uint64 10ul ->
  Stack unit
    (requires fun h -> live h z /\ live h t)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)
let barrett_reduction_ z t =
  push_frame();
  let tmp = create 40ul (u64 0) in
  let m   = sub tmp 0ul 5ul in
  let mu  = sub tmp 5ul 5ul in
  let tmp = sub tmp 10ul 30ul in
  make_m m;
  make_mu mu;
  barrett_reduction__ z t m mu tmp;
  pop_frame()

let barrett_reduction z t =
  barrett_reduction_ z t

#reset-options "--max_fuel 0"

let mul_modq out x y =
  push_frame();
  let z' = create 10ul (u64 0) in
  let z  = create 9ul (u128 0) in
  mul_5 z x y;
  carry z' z;
  barrett_reduction_ out z';
  pop_frame()

inline_for_extraction noextract
val add_modq_:
    z:qelemB
  -> x:qelemB
  -> y:qelemB ->
  Stack unit
    (requires fun h -> live h z /\ live h x /\ live h y)
    (ensures  fun h0 _ h1 -> modifies (loc z) h0 h1)
let add_modq_ out x y =
  push_frame();
  let tmp = create 5ul (u64 0) in
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
  let z0 = x0 +. y0 in
  let z1 = x1 +. y1 in
  let z2 = x2 +. y2 in
  let z3 = x3 +. y3 in
  let z4 = x4 +. y4 in
  let x = z0  in let y = z1 in
  let carry =x >>. 56ul in
  let t     = x &. u64 0xffffffffffffff in
  let x0 = t in let z1' = y +. carry in

  let x = z1' in let y = z2 in
  let carry = x >>. 56ul in
  let t     = x &. u64 0xffffffffffffff in
  let x1 = t in let z2' = y +. carry in

  let x = z2' in let y = z3 in
  let carry = x >>. 56ul in
  let t     = x &. u64 0xffffffffffffff in
  let x2 = t in let z3' = y +. carry in

  let x = z3' in let y = z4 in
  let carry = x >>. 56ul in
  let t     = x &. u64 0xffffffffffffff in
  let x3 = t in let x4 = y +. carry in
  Hacl.Bignum25519.make_u64_5 tmp x0 x1 x2 x3 x4;
  subm_conditional out tmp;
  pop_frame()

let add_modq out x y = add_modq_ out x y
