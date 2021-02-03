module Hacl.Impl.ScalarMultiplication.Radix4

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Spec.P256
open Spec.P256.Lemmas
open Spec.P256.Definitions

open Spec.P256.MontgomeryMultiplication
open Hacl.Impl.P256.MontgomeryMultiplication

open Hacl.Impl.P256.LowLevel
open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.PointDouble

open FStar.Mul
open  FStar.Math.Lemmas

open Hacl.Impl.P256.Q.PrimitivesMasking


(* prime = 2**256 - 2**224 + 2**192 + 2**96 -1

def norm(p):    
    x, y, z = p
    z2i = power_mod(z * z, -1, prime)
    z3i = power_mod(z * z * z, -1, prime)
    return ((x * z2i) % prime, (y * z3i) % prime, 1)

def toD(x):
    return x * power_mod (2 ** 256, 1, prime) % prime

def fromD(x):
    return x * power_mod (2 ** 256, prime - 2, prime) % prime

def toFakeAffine(p):
    x, y = p 
    multiplier = power_mod (2 ** 256, prime - 2, prime) 
    x = x * multiplier * multiplier % prime
    y = y * multiplier * multiplier * multiplier % prime
    return (x, y)

p256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
a256 = p256 - 3
b256 = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
qq = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
FF = GF(p256)

EC = EllipticCurve([FF(a256), FF(b256)])

EC.set_order(qq)

G = EC(FF(gx), FF(gy))

def printf(p):
    x, y = p 
    for i in range(4):
        print("u64 " + str(hex((Integer(x) >> (i * 64)) % 2 ** 64)) + "; ")
    for i in range(4):
        print("u64 " + str (hex((Integer(y) >> (i * 64)) % 2 ** 64)) + "; ")
    

for i in range(16):
    pxD = i * G.xy()[0]
    pyD = i * G.xy()[1]
    printf (toFakeAffine((to D (pxD), toD (pyD))))

 *)


#set-options " --z3rlimit 400"


inline_for_extraction noextract
let points_radix_16_list : x:list uint64 {List.Tot.length x == 128} =
  let open FStar.Mul in 
  [@inline_let]
  let x = [ 
    u64 0x0; u64 0x0; u64 0x0; u64 0x0; 
   u64 0x0; u64 0x0; u64 0x0; u64 0x0; 

    u64 0x1fb38ab1388ad777; u64 0x1dfee06615fa309d; u64 0xfcac986c3afea4a7; u64 0xdf65c2da29fb821a; 
    u64 0xeff44e23f63f8f6d; u64 0xaa02cd3ed4b681a4; u64 0xdd5fda3363818af8; u64 0xfc53bc2629fbf0b3; 

    u64 0x12631d721b91beea; u64 0x5f73f2d3a11a09f8; u64 0xac41f54484d5fcd8; u64 0x86578e5c56025df4; 
    u64 0x577c956b15ed6b5a; u64 0xb59c5f77982d848; u64 0xb7c5e2c190fcdcc2; u64 0x7d64d13ef1c91ffd; 

    u64 0xd40c2d6273f9d9f1; u64 0x4dc6f628063ef17c; u64 0x498e81df7ab17aa5; u64 0xabb2a5026f17173c; 
    u64 0x4a3d7527f6739ef3; u64 0xd941003268184c91; u64 0xd2d458b8d401508b; u64 0xb7437ab810ac5451; 

    u64 0x5256d9bdab491252; u64 0x972d326eb1084c12; u64 0xc3e96455e2ec3bfa; u64 0xb75c723b549a10ff; 
    u64 0x9d9185f9f8a18961; u64 0x2200a07b8589ba82; u64 0x637b9d96fd4e9f5e; u64 0xce75bfb2575e6cfa; 

    u64 0x7dd4477db8b77c7d; u64 0x80818a776e5503b0; u64 0x6fc7d58fb59581d; u64 0xd899fb87efe43022; 
    u64 0x23b9912111694135; u64 0x7e5de7bac33fa1c8; u64 0xb3b83722a70e7d43; u64 0xf06cfecbfb9bb38f; 

    u64 0xaa39277dfa93656; u64 0x3dabb6cce67c5201; u64 0x473ffb8bf1f94677; u64 0xb9f0b93637453e56; 
    u64 0x8fce12ec20958fb2; u64 0xcc16d74ff7786061; u64 0x3678438a8235d096; u64 0xe39ea044f06b43f6; 

    u64 0xbb40bdb5775c9950; u64 0xd244a74cdc703cdd; u64 0x83dc1b8a6105dd53; u64 0x38d9d50d49ef0437; 
    u64 0x58be44eba6096472; u64 0x960afaec386fa5c5; u64 0x1440032e000134b9; u64 0x601e721454d6ba96; 

    u64 0x79ec42228671b9b6; u64 0xfdc00dc48df9e25c; u64 0x44500833d71d2e77; u64 0x2bda4c3c0bc103d5; 
    u64 0x51528408aa925d53; u64 0xefcb55b9c2f3a37d; u64 0x9f28f6bb9846c915; u64 0xe1547ce1d8340e55; 

    u64 0x97e310c1995b3ed2; u64 0xed861937196256e6; u64 0x1c6762abff2c65f2; u64 0x268345e0978fcedd; 
    u64 0x35ca2e572b784881; u64 0x28ac888da0acd1b7; u64 0x305640dc06a41baf; u64 0x997c6fd2cb671bfb; 

    u64 0xf40d9eaf4a31e15a; u64 0x8991dd7d54cfe03a; u64 0x4889a3463a8deb0c; u64 0x4cbf48092cd0a1fa; 
    u64 0xc6965c4fbe18fb8c; u64 0x1d499d0cb216fa84; u64 0x8d5fe52c705dd3eb; u64 0x812b268f84313b34; 

    u64 0x313b58808261591a; u64 0xc2c322508f53d933; u64 0xa49ef3f95094ed1b; u64 0x13e326786e98c63; 
    u64 0x34be8167cd460429; u64 0x698a328099a6b31; u64 0xb9be3ba51b0c922d; u64 0xe59cca03f7674ed; 
    
    u64 0x4fbf7e505d3aca7c; u64 0x2f4f8ba62020715; u64 0x840502262ac1ec42; u64 0xb8e0532775197de7; 
    u64 0x9142a358cf4e9b4b; u64 0xc86a3c567e5d8626; u64 0xd4051282b4a7992a; u64 0xe7573c5999e3974e;
    
    u64 0xd814a606da7bd76b; u64 0x15604730f38cb788; u64 0xbd195f868fbdd6c4; u64 0xdb96f5b00a51d3f7; 
    u64 0xe1385c8a9b507fea; u64 0x878e27813ee7310; u64 0x6d7d8b12aea7e096; u64 0x54978ad11e2f5cca; 
    
    u64 0x49fffd6c3c4d07d4; u64 0x703638f71fab7a5d; u64 0xbed6e367fcc73960; u64 0x215e161835a61d75; 
    u64 0xe52288a5e87a660b; u64 0xf1d127ee3c802cb5; u64 0xccde3c6aafc46044; u64 0xdc11c08ef14cff32; 

    u64 0x29216f9ceca46668; u64 0x22e584a3b2891c5e; u64 0xe6deecd7810f6d87; u64 0x6aff4b94a55659a3; 
   u64 0x12b59bb6d2e9f876; u64 0x27ed01943aa02eab; u64 0x8d6d420841f57075; u64 0xe7b47285ef60a461;   
  ] in 
  
    assert_norm(List.Tot.length x == 128);
    x


val lemma_points_precomputed: unit -> 
  Lemma 
    (ensures (
      let l0 = v (List.Tot.index points_radix_16_list 0) in 
      let l1 = v (List.Tot.index points_radix_16_list 1) in 
      let l2 = v (List.Tot.index points_radix_16_list 2) in
      let l3 = v (List.Tot.index points_radix_16_list 3) in

      let l4 = v (List.Tot.index points_radix_16_list 4) in
      let l5 = v (List.Tot.index points_radix_16_list 5) in
      let l6 = v (List.Tot.index points_radix_16_list 6) in
      let l7 = v (List.Tot.index points_radix_16_list 7) in

      let p0x = l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 in 

      let x = 0 in 
      let multiplier = modp_inv2_pow (pow2 256) in 
      fromDomain_ p0x == fromDomain_ (x * multiplier)



     ))


let lemma_points_precomputed () = 
  admit();
  let x = 0 in 

  let l0 = v (List.Tot.index points_radix_16_list 0) in 
  let l1 = v (List.Tot.index points_radix_16_list 1) in 
  let l2 = v (List.Tot.index points_radix_16_list 2) in
  let l3 = v (List.Tot.index points_radix_16_list 3) in

  let p0x = l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 in 
  let multiplier = modp_inv2 (pow2 256) in 
  let p0xD = p0x * multiplier in 

  lemmaFromDomain (x * multiplier);
  small_mod 0 (pow2 256);
  admit()


val lemma_points_precomputed1: unit -> 
  Lemma 
    (ensures (
      let l0 = v (List.Tot.index points_radix_16_list 8) in 
      let l1 = v (List.Tot.index points_radix_16_list 9) in 
      let l2 = v (List.Tot.index points_radix_16_list 10) in
      let l3 = v (List.Tot.index points_radix_16_list 11) in

      let l4 = v (List.Tot.index points_radix_16_list 12) in
      let l5 = v (List.Tot.index points_radix_16_list 13) in
      let l6 = v (List.Tot.index points_radix_16_list 14) in
      let l7 = v (List.Tot.index points_radix_16_list 15) in

      let p0X = l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 in 
      let p0Y = l4 + l5 * pow2 64 + l6 * pow2 128 + l7 * pow2 192 in 
  
      let pointAsAffineX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 in 
      let pointAsAffineY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 in 
      let pointAsAffineZ = 1 in 

      let multiplier = modp_inv2 (pow2 256) in 
      let pointOriginalX = (toDomain_ pointAsAffineX) * multiplier * multiplier % prime in 
      let pointOriginalY = (toDomain_ pointAsAffineY) * multiplier * multiplier * multiplier % prime in 

      let normedX, normedY, normedZ = _norm (fromDomain_ pointOriginalX, fromDomain_ pointOriginalY, fromDomain_ 1) in 

      p0X == pointOriginalX /\ p0Y == pointOriginalY (* /\ 

      pointAsAffineX == normedX /\ pointAsAffineY == normedY /\ pointAsAffineZ == normedZ*)



     ))


let lemma_points_precomputed1 () = 
  let l0 = v (List.Tot.index points_radix_16_list 8) in 
  let l1 = v (List.Tot.index points_radix_16_list 9) in 
  let l2 = v (List.Tot.index points_radix_16_list 10) in
  let l3 = v (List.Tot.index points_radix_16_list 11) in

  let l4 = v (List.Tot.index points_radix_16_list 12) in
  let l5 = v (List.Tot.index points_radix_16_list 13) in
  let l6 = v (List.Tot.index points_radix_16_list 14) in
  let l7 = v (List.Tot.index points_radix_16_list 15) in

  let p0X = l0 + l1 * pow2 64 + l2 * pow2 128 + l3 * pow2 192 in 
  let p0Y = l4 + l5 * pow2 64 + l6 * pow2 128 + l7 * pow2 192 in 
  
  let pointAsAffineX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 in 
  let pointAsAffineY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 in 
  let pointAsAffineZ = 1 in 

  let multiplier = modp_inv2 (pow2 256) in 
  let pointOriginalX = (toDomain_ pointAsAffineX) * multiplier * multiplier % prime in 
  let pointOriginalY = (toDomain_ pointAsAffineY) * multiplier * multiplier * multiplier % prime in 

  let normedX, normedY, normedZ = _norm (fromDomain_ pointOriginalX, fromDomain_ pointOriginalY, fromDomain_ 1) in 

  lemmaToDomain pointAsAffineX;
  lemmaToDomain pointAsAffineY;
  
  assert_norm(p0X == 0xdf65c2da29fb821afcac986c3afea4a71dfee06615fa309d1fb38ab1388ad777);
  assert_norm(p0Y == 0xfc53bc2629fbf0b3dd5fda3363818af8aa02cd3ed4b681a4eff44e23f63f8f6d);
  assert_norm((pointAsAffineX * pow2 256) % prime256 * multiplier * multiplier % prime == 0xdf65c2da29fb821afcac986c3afea4a71dfee06615fa309d1fb38ab1388ad777);
  assert_norm((pointAsAffineY * pow2 256) % prime256 * multiplier * multiplier * multiplier % prime == 0xfc53bc2629fbf0b3dd5fda3363818af8aa02cd3ed4b681a4eff44e23f63f8f6d)



inline_for_extraction
let points_radix_16 : x: glbuffer uint64 128ul {witnessed #uint64 #(size 128) x (Lib.Sequence.of_list points_radix_16_list) /\ recallable x} =
    createL_global points_radix_16_list



(* The function takes 4 bits per call, scalar[4 * i : 4 * i + 4] *)

[@ CInline]
inline_for_extraction noextract  
val getScalar: #buf_type: buftype -> scalar: lbuffer_t buf_type uint8 (size 32) -> i: size_t {v i < 64} -> 
  Stack uint32 
    (requires fun h -> live h scalar)
    (ensures fun h0 _ h1 -> True)

let getScalar #a scalar i = 
  let open Hacl.Impl.P256.Q.PrimitivesMasking in 
    let h0 = ST.get() in 
  
  let half = shift_right i 1ul in 
    shift_right_lemma i 1ul;
  let word = to_u32 (index scalar half) in 

  assert(uint_v half == uint_v i / 2);
  assert(uint_v word == uint_v (Lib.Sequence.index (as_seq h0 scalar) (uint_v i / 2)));

  let bitShift : size_t = logand i (size 1) in 
    logand_mask i (size 1) 1; 

  assert(v bitShift == v i % 2);

  let bitShiftAsPrivate = size_to_uint32 bitShift in 

  assert(v bitShiftAsPrivate = v i % 2);

  let mask : uint32 = cmovznz01 (u32 0xf0) (u32 0x0f) bitShiftAsPrivate in  
    assert(if v i % 2 = 0 then v mask == 0xf0 else v mask = 0x0f);
  let shiftMask = cmovznz01 (size 0x4) (size 0x0) bitShift in
    assert(if v i % 2 = 0 then v shiftMask = 4 else v shiftMask = 0);

  let result : uint32 = logand word mask in 
(*     assert(if v i % 2 = 0 then v result == v (logand word mask)
      else 
	v result == v (logand 
    
    
    
    ); *)
  let result : uint32 = shift_right result shiftMask in 
 
  result


[@ CInline]
inline_for_extraction noextract  
val montgomery_ladder_step_radix_precomputed: 
  p: point -> tempBuffer: lbuffer uint64 (size 88) -> 
  scalar:  lbuffer uint8 (size 32)-> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> True)


let montgomery_ladder_step_radix_precomputed p tempBuffer scalar i =  
  let bits: uint32 = getScalar scalar (i) in 

  let pointToAdd = create (size 8) (u64 0) in 

  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
  (fun k -> 
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      (* eq_mask_lemma d (to_u64 k);  *)
	
      let lut_cmb_x = Hacl.Impl.P256.Q.Comparision.global_to_comparable (sub points_radix_16 (k *! 8) (size 4)) in 
      let lut_cmb_y = Hacl.Impl.P256.Q.Comparision.global_to_comparable (sub points_radix_16 (k *! 8 +! (size 4)) (size 4)) in 

      copy_conditional (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask); 


 (*  let pointToAdd = sub points_radix_16 (bits *. size 8) (size 8) in *)
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  
  Hacl.Impl.P256.MixedPointAdd.point_add_mixed p pointToAdd p tempBuffer





[@ CInline]
inline_for_extraction noextract  
val montgomery_ladder_step_radix: 
  p: point -> tempBuffer: lbuffer uint64 (size 88) -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  scalar:  lbuffer uint8 (size 32) -> 
  i:size_t{v i < 256} -> 
  Stack unit
  (requires fun h -> live h p /\live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p;loc tempBuffer; loc scalar])
  (ensures fun h0 _ h1 -> True)



let montgomery_ladder_step_radix p tempBuffer precomputedTable scalar i =  
  let bits = getScalar scalar i in 

  let pointToAdd = create (size 12) (u64 0) in 

  let invK h (k: nat) = True in 
  Lib.Loops.for 0ul 16ul invK
  (fun k -> 
      let mask = eq_mask (to_u64 bits) (to_u64 k) in 
      (* eq_mask_lemma d (to_u64 k);  *)
	
      let lut_cmb_x = sub precomputedTable (k *! 12) (size 4) in 
      let lut_cmb_y = sub precomputedTable (k *! 12 +! (size 4)) (size 4) in
      let lut_cmb_z = sub precomputedTable (k *! 12 +! (size 8)) (size 4) in 

      copy_conditional (sub pointToAdd (size 0) (size 4)) lut_cmb_x mask;
      copy_conditional (sub pointToAdd (size 4) (size 4)) lut_cmb_y mask;
      copy_conditional (sub pointToAdd (size 8) (size 4)) lut_cmb_z mask
      
      
      ); 
      
  
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;
  point_double p p tempBuffer;

  point_add pointToAdd p p tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2_precomputed: #buf_type: buftype -> p: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2_precomputed #a p scalar tempBuffer =  
 let h0 = ST.get() in 




  [@inline_let]
  let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

  [@inline_let] 
  let acc (h:mem) : GTot (point_nat_prime) = (fromDomainPoint(point_prime_to_coordinates (as_seq h p)))  in 

  [@inline_let]
  let inv h (i: nat {i <= 64}) = True in 

 
  let bits: uint32 = getScalar scalar 0 in 
  let pointToStart = sub points_radix_16 (bits *. size 8) (size 8) in 
  let pointToStart = const_to_lbuffer pointToStart in 

  copy (sub p (size 0) (size 8)) pointToStart;

  upd p (size 8) (u64 1);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0);


  for 1ul 64ul inv 
    (fun i -> let h2 = ST.get() in
      montgomery_ladder_step_radix_precomputed p tempBuffer scalar i
    )



[@ CInline]
val generatePrecomputedTable: b: lbuffer uint64 (size 192) -> publicKey: point ->
  tempBuffer: lbuffer uint64 (size 88) -> Stack unit  
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let generatePrecomputedTable b publicKey tempBuffer = 
  let point0 = sub b (size 0) (size 12) in 
  let point1 = sub b (size 12) (size 12) in 
  let point2 = sub b (size 24) (size 12) in 
  let point3 = sub b (size 36) (size 12) in 
  let point4 = sub b (size 48) (size 12) in 
  let point5 = sub b (size 60) (size 12) in 
  let point6 = sub b (size 72) (size 12) in 
  let point7 = sub b (size 84) (size 12) in 
  let point8 = sub b (size 96) (size 12) in 
  let point9 = sub b (size 108) (size 12) in 
  let point10 = sub b (size 120) (size 12) in 
  let point11 = sub b (size 132) (size 12) in 
  let point12 = sub b (size 144) (size 12) in 
  let point13 = sub b (size 156) (size 12) in 
  let point14 = sub b (size 168) (size 12) in 
  let point15 = sub b (size 180) (size 12) in 

  uploadZeroPoint point0;
  copy_point publicKey point1;
  point_double publicKey point2 tempBuffer;
  point_add point2 point1 point3 tempBuffer;
  point_double point2 point4 tempBuffer;
  point_add point4 point1 point5 tempBuffer;
  point_double point3 point6 tempBuffer;
  point_add point6 point1 point7 tempBuffer;
  point_double point4 point8 tempBuffer;
  point_add point8 point1 point9 tempBuffer;
  point_double point5 point10 tempBuffer;
  point_add point10 point1 point11 tempBuffer;
  point_double point6 point12 tempBuffer;
  point_add point12 point1 point13 tempBuffer;
  point_double point7 point14 tempBuffer;
  point_add point14 point1 point15 tempBuffer



inline_for_extraction noextract
val montgomery_ladder_2: #buf_type: buftype -> p: point -> 
  scalar: lbuffer_t buf_type uint8 (size 32) -> 
  tempBuffer:  lbuffer uint64 (size 88)  -> 
  precomputedTable: lbuffer uint64 (size 192) ->
  Stack unit
  (requires fun h -> True )
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc tempBuffer) h0 h1)

let montgomery_ladder_2 #a p scalar tempBuffer precomputedTable =  
 let h0 = ST.get() in 
   push_frame();

     [@inline_let]
     let spec_ml h0 = _ml_step (as_seq h0 scalar) in 

     [@inline_let] 
     let acc (h:mem) : GTot (point_nat_prime) = (fromDomainPoint(point_prime_to_coordinates (as_seq h p)))  in 

     [@inline_let]
     let inv h (i: nat {i <= 64}) = True in 


  let bits: uint32 = getScalar scalar 0 in 
  let pointToStart = sub precomputedTable  (bits *. size 12) (size 12) in 

  copy (sub p (size 0) (size 12)) pointToStart;
  
     for 1ul 64ul inv 
       (fun i -> let h2 = ST.get() in
	 montgomery_ladder_step_radix p tempBuffer precomputedTable scalar i
       );
   pop_frame()

