module Hacl.Impl.P256.Core 

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Spec.P256
open Spec.P256.Definitions
open Spec.P256.Lemmas

open Hacl.Impl.P256.LowLevel 
open Hacl.Impl.P256.MontgomeryMultiplication
open Hacl.Impl.SolinasReduction

open FStar.Tactics 
open FStar.Tactics.Canon

open Hacl.Impl.P256.Math
open FStar.Math.Lemmas

open Hacl.Impl.P256.Q.PrimitivesMasking

open Hacl.Impl.ScalarMultiplication.Ladder
open Hacl.Impl.ScalarMultiplication.Radix4
open Hacl.Impl.ScalarMultiplication.RWNAF


open Spec.P256.MontgomeryMultiplication
open FStar.Mul



#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0" 
let toDomain value result = 
  push_frame();
    let multBuffer = create (size 8) (u64 0) in 
    shift_256_impl value multBuffer;
    solinas_reduction_impl multBuffer result;
  pop_frame()  


let fromDomain f result = 
  montgomery_multiplication_buffer_by_one f result  

let pointToDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 
    
    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    toDomain p_x r_x;
    toDomain p_y r_y;

    upd result (size 8) (u64 1);
    upd result (size 9) (u64 18446744069414584320);
    upd result (size 10) (u64 18446744073709551615);
    upd result (size 11) (u64 4294967294)
    

let pointFromDomain p result = 
    let p_x = sub p (size 0) (size 4) in 
    let p_y = sub p (size 4) (size 4) in 
    let p_z = sub p (size 8) (size 4) in 

    let r_x = sub result (size 0) (size 4) in 
    let r_y = sub result (size 4) (size 4) in 
    let r_z = sub result (size 8) (size 4) in 

    fromDomain p_x r_x;
    fromDomain p_y r_y;
    fromDomain p_z r_z



(* https://crypto.stackexchange.com/questions/43869/point-at-infinity-and-error-handling*)
val lemma_pointAtInfInDomain: x: nat -> y: nat -> z: nat {z < prime256} -> 
  Lemma (isPointAtInfinity (x, y, z) == isPointAtInfinity ((fromDomain_ x), (fromDomain_ y), (fromDomain_ z)))

let lemma_pointAtInfInDomain x y z =
  assert (if isPointAtInfinity (x, y, z) then z == 0 else z <> 0);
  assert_norm (modp_inv2 (pow2 256) % prime256 <> 0);
  lemmaFromDomain z;
  assert (fromDomain_ z == (z * modp_inv2 (pow2 256) % prime256));
  assert_norm (0 * modp_inv2 (pow2 256) % prime256 == 0);
  lemma_multiplication_not_mod_prime z;
  assert (if z = 0 then z * modp_inv2 (pow2 256) % prime256 == 0
                   else fromDomain_ z <> 0)


let isPointAtInfinityPrivate p =  
  let h0 = ST.get() in
  let z0 = index p (size 8) in 
  let z1 = index p (size 9) in 
  let z2 = index p (size 10) in 
  let z3 = index p (size 11) in 
  let z0_zero = eq_mask z0 (u64 0) in 
  let z1_zero = eq_mask z1 (u64 0) in 
  let z2_zero = eq_mask z2 (u64 0) in 
  let z3_zero = eq_mask z3 (u64 0) in 
     eq_mask_lemma z0 (u64 0);
     eq_mask_lemma z1 (u64 0);
     eq_mask_lemma z2 (u64 0);
     eq_mask_lemma z3 (u64 0);   
  let r = logand(logand z0_zero z1_zero) (logand z2_zero z3_zero) in 
    lemma_pointAtInfInDomain (as_nat h0 (gsub p (size 0) (size 4))) (as_nat h0 (gsub p (size 4) (size 4))) (as_nat h0 (gsub p (size 8) (size 4)));
  r


val lemma_norm_as_specification: xD: nat{xD < prime256} -> yD: nat{yD < prime256} -> 
  zD: nat {zD < prime256} -> 
  x3 : nat {x3 == xD * (pow (zD * zD) (prime - 2) % prime) % prime}-> 
  y3 : nat {y3 == yD * (pow (zD * zD * zD) (prime -2) % prime) % prime} -> 
  z3: nat {if isPointAtInfinity(xD, yD, zD) then z3 == 0 else z3 == 1} -> 
  Lemma (
  let (xN, yN, zN) = _norm (xD, yD, zD) in 
  x3 == xN /\ y3 == yN /\ z3 == zN)


let lemma_norm_as_specification xD yD zD x3 y3 z3 = 
  power_distributivity (zD * zD * zD) (prime - 2) prime;
  power_distributivity (zD * zD) (prime -2) prime



inline_for_extraction noextract
val normalisation_update: z2x: felem -> z3y: felem ->p: point ->  resultPoint: point -> Stack unit 
  (requires fun h -> live h z2x /\ live h z3y /\ live h resultPoint /\ live h p /\ 
    as_nat h z2x < prime256 /\ as_nat h z3y < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime256 /\
    disjoint z2x z3y /\ disjoint z2x resultPoint /\ disjoint z3y resultPoint)
  (ensures fun h0 _ h1 -> modifies (loc resultPoint) h0 h1 /\
    (
      let x0 = as_nat h0 (gsub p (size 0) (size 4)) in 
      let y0 = as_nat h0 (gsub p (size 4) (size 4)) in 
      let z0 = as_nat h0 (gsub p (size 8) (size 4)) in 

      let x1 = as_nat h1 (gsub resultPoint (size 0) (size 4)) in 
      let y1 = as_nat h1 (gsub resultPoint (size 4) (size 4)) in 
      let z1 = as_nat h1 (gsub resultPoint (size 8) (size 4)) in 

      x1 == fromDomain_(as_nat h0 z2x) /\ y1 == fromDomain_(as_nat h0 z3y)  /\ 
      (
  if Spec.P256.isPointAtInfinity (fromDomain_ x0, fromDomain_ y0, fromDomain_ z0) then  z1 == 0 else z1 == 1
      ))
  )


let normalisation_update z2x z3y p resultPoint = 
  push_frame(); 
    let zeroBuffer = create (size 4) (u64 0) in 
    
  let resultX = sub resultPoint (size 0) (size 4) in 
  let resultY = sub resultPoint (size 4) (size 4) in 
  let resultZ = sub resultPoint (size 8) (size 4) in 
    let h0 = ST.get() in 
  let bit = isPointAtInfinityPrivate p in
  fromDomain z2x resultX;
  fromDomain z3y resultY;
  uploadOneImpl resultZ;
    let h1 = ST.get() in 
  copy_conditional resultZ zeroBuffer bit;
    let h2 = ST.get() in 
  pop_frame()
  

let norm p resultPoint tempBuffer = 
  let xf = sub p (size 0) (size 4) in 
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 32) in 

    let h0 = ST.get() in 
  montgomery_square_buffer zf z2f; 
    let h1 = ST.get() in 
  montgomery_multiplication_buffer z2f zf z3f;
    let h2 = ST.get() in 
      lemma_mod_mul_distr_l (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (fromDomain_ (as_nat h0 zf)) prime256;
      assert (as_nat h1 z2f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % prime256));
      assert (as_nat h2 z3f = toDomain_ (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) % prime256));

  exponent z2f z2f tempBuffer20;
    let h3 = ST.get() in 
      assert(as_nat h3 z2f = toDomain_ (pow (fromDomain_ (as_nat h2 z2f)) (prime256 - 2) % prime256));
  exponent z3f z3f tempBuffer20;
    let h4 = ST.get() in 
      assert(as_nat h4 z3f = toDomain_ (pow (fromDomain_ (as_nat h3 z3f)) (prime256 - 2) % prime256));
     
  montgomery_multiplication_buffer xf z2f z2f;
  montgomery_multiplication_buffer yf z3f z3f;
  normalisation_update z2f z3f p resultPoint; 

    let h3 = ST.get() in 
    lemmaEraseToDomainFromDomain (fromDomain_ (as_nat h0 zf)); 
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime;
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime;

    lemma_norm_as_specification (fromDomain_ (point_x_as_nat h0 p)) (fromDomain_ (point_y_as_nat h0 p)) (fromDomain_ (point_z_as_nat h0 p)) (point_x_as_nat h3 resultPoint) (point_y_as_nat h3 resultPoint) (point_z_as_nat h3 resultPoint);

    assert(
       let zD = fromDomain_(point_z_as_nat h0 p) in 
       let xD = fromDomain_(point_x_as_nat h0 p) in 
       let yD = fromDomain_(point_y_as_nat h0 p) in 
       let (xN, yN, zN) = _norm (xD, yD, zD) in 
       point_x_as_nat h3 resultPoint == xN /\ point_y_as_nat h3 resultPoint == yN /\ point_z_as_nat h3 resultPoint == zN)


let normX p result tempBuffer = 
  let xf = sub p (size 0) (size 4) in 
  let yf = sub p (size 4) (size 4) in 
  let zf = sub p (size 8) (size 4) in 

  
  let z2f = sub tempBuffer (size 4) (size 4) in 
  let z3f = sub tempBuffer (size 8) (size 4) in
  let tempBuffer20 = sub tempBuffer (size 12) (size 20) in 

    let h0 = ST.get() in 
  montgomery_square_buffer zf z2f; 
  exponent z2f z2f tempBuffer20;
  montgomery_multiplication_buffer z2f xf z2f;
  fromDomain z2f result;
  assert_norm (prime >= 2);
    power_distributivity (fromDomain_ (as_nat h0 zf) * fromDomain_ (as_nat h0 zf)) (prime -2) prime





inline_for_extraction noextract
val zero_buffer: p: point -> 
  Stack unit
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 ->     
      modifies (loc p) h0 h1 /\
      (
  let k = Lib.Sequence.create 12 (u64 0) in 
  as_nat h1 (gsub p (size 0) (size 4)) == 0 /\ 
  as_nat h1 (gsub p (size 4) (size 4)) == 0 /\
  as_nat h1 (gsub p (size 8) (size 4)) == 0 
    )
  )

let zero_buffer p = 
  upd p (size 0) (u64 0);
  upd p (size 1) (u64 0);
  upd p (size 2) (u64 0);
  upd p (size 3) (u64 0);
  upd p (size 4) (u64 0);
  upd p (size 5) (u64 0);
  upd p (size 6) (u64 0);
  upd p (size 7) (u64 0);
  upd p (size 8) (u64 0);
  upd p (size 9) (u64 0);
  upd p (size 10) (u64 0);
  upd p (size 11) (u64 0)


val lemma_point_to_domain: h0: mem -> h1: mem ->  p: point -> result: point ->  Lemma
   (requires (point_x_as_nat h0 p < prime /\ point_y_as_nat h0 p < prime /\ point_z_as_nat h0 p < prime /\
       point_x_as_nat h1 result == toDomain_ (point_x_as_nat h0 p) /\
       point_y_as_nat h1 result == toDomain_ (point_y_as_nat h0 p) /\
       point_z_as_nat h1 result == toDomain_ (point_z_as_nat h0 p) 
     )
   )
   (ensures (fromDomainPoint(point_prime_to_coordinates (as_seq h1 result)) == point_prime_to_coordinates (as_seq h0 p)))

let lemma_point_to_domain h0 h1 p result = 
  let (x, y, z) = point_prime_to_coordinates (as_seq h1 result) in ()


val lemma_pif_to_domain: h: mem ->  p: point -> Lemma
  (requires (point_x_as_nat h p == 0 /\ point_y_as_nat h p == 0 /\ point_z_as_nat h p == 0))
  (ensures (fromDomainPoint (point_prime_to_coordinates (as_seq h p)) == point_prime_to_coordinates (as_seq h p)))

let lemma_pif_to_domain h p = 
  let (x, y, z) = point_prime_to_coordinates (as_seq h p) in 
  let (x3, y3, z3) = fromDomainPoint (x, y, z) in 
  lemmaFromDomain x;
  lemmaFromDomain y;
  lemmaFromDomain z;
  lemma_multiplication_not_mod_prime x; 
  lemma_multiplication_not_mod_prime y;
  lemma_multiplication_not_mod_prime z


val lemma_coord: h3: mem -> q: point -> Lemma (
   let (r0, r1, r2) = fromDomainPoint(point_prime_to_coordinates (as_seq h3 q)) in 
  let xD = fromDomain_ (point_x_as_nat h3 q) in 
  let yD = fromDomain_ (point_y_as_nat h3 q) in 
  let zD = fromDomain_ (point_z_as_nat h3 q) in 
    r0 == xD /\ r1 == yD /\ r2 == zD) 

let lemma_coord h3 q = ()


inline_for_extraction
val scalarMultiplication_t: #t:buftype ->
  m: montgomery_ladder_mode ->

   p: point -> result: point -> 
  scalar: lbuffer_t t uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) ->
  Stack unit
    (requires fun h -> 
      live h p /\ live h result /\ live h scalar /\ live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc tempBuffer; loc scalar; loc result] /\
    as_nat h (gsub p (size 0) (size 4)) < prime /\ 
    as_nat h (gsub p (size 4) (size 4)) < prime /\
    as_nat h (gsub p (size 8) (size 4)) < prime
    )
  (ensures fun h0 _ h1 -> 
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\ 
    
    as_nat h1 (gsub result (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub result (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub result (size 8) (size 4)) < prime256 /\
    
    modifies (loc p |+| loc result |+| loc tempBuffer) h0 h1 /\
    (
      let x3, y3, z3 = point_x_as_nat h1 result, point_y_as_nat h1 result, point_z_as_nat h1 result in 
      let (xN, yN, zN) = scalar_multiplication (as_seq h0 scalar) (point_prime_to_coordinates (as_seq h0 p)) in 
      x3 == xN /\ y3 == yN /\ z3 == zN 
  )
) 


let scalarMultiplication_t #t m p result scalar tempBuffer  = 
(*
    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  zero_buffer q;
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 
  montgomery_ladder q result scalar buff;
    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
  norm q result buff; 
    lemma_coord h3 q *)



    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  (* zero_buffer q; *)
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 

    begin
  match m with 
  |Ladder ->
      montgomery_ladder q result scalar buff
  |_ ->
     let bufferPrecomputed = create (size 192) (u64 0) in 
     generatePrecomputedTable bufferPrecomputed result buff;
     montgomery_ladder_2 q scalar buff bufferPrecomputed
  end;

    let h3 = ST.get() in 
    lemma_point_to_domain h0 h2 p result;
    lemma_pif_to_domain h2 q;
  norm q result buff; 
    lemma_coord h3 q





let scalarMultiplicationL = scalarMultiplication_t #MUT

let scalarMultiplicationI = scalarMultiplication_t #IMMUT
let scalarMultiplicationC = scalarMultiplication_t #CONST

let scalarMultiplication #buf_type m p result scalar tempBuffer = 
  match buf_type with 
  |MUT -> scalarMultiplicationL m p result scalar tempBuffer 
  |IMMUT -> scalarMultiplicationI m p result scalar tempBuffer
  |CONST -> scalarMultiplicationC m p result scalar tempBuffer


inline_for_extraction noextract
val uploadBasePoint: p: point -> Stack unit 
  (requires fun h -> live h p)
  (ensures fun h0 _ h1 -> modifies (loc p) h0 h1 /\ 
    as_nat h1 (gsub p (size 0) (size 4)) < prime256 /\ 
    as_nat h1 (gsub p (size 4) (size 4)) < prime256 /\
    as_nat h1 (gsub p (size 8) (size 4)) < prime256 /\
      (
  let x1 = as_nat h1 (gsub p (size 0) (size 4)) in 
  let y1 = as_nat h1 (gsub p (size 4) (size 4)) in 
  let z1 = as_nat h1 (gsub p (size 8) (size 4)) in 

  let bpX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 in 
  let bpY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 in 

  fromDomain_ x1 == bpX /\ fromDomain_ y1 == bpY /\ fromDomain_ z1 ==  1
    )
)

let uploadBasePoint p = 
    let h0 = ST.get() in 
  upd p (size 0) (u64 8784043285714375740);
  upd p (size 1) (u64 8483257759279461889);
  upd p (size 2) (u64 8789745728267363600);
  upd p (size 3) (u64 1770019616739251654);
  assert_norm (8784043285714375740 + pow2 64 * 8483257759279461889 + pow2 64 * pow2 64 * 8789745728267363600 + pow2 64 * pow2 64 * pow2 64 * 1770019616739251654 < prime256); 
    assert_norm (8784043285714375740 + pow2 64 * 8483257759279461889 + pow2 64 * pow2 64 * 8789745728267363600 + pow2 64 * pow2 64 * pow2 64 * 1770019616739251654 = 11110593207902424140321080247206512405358633331993495164878354046817554469948); 
  assert_norm(0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 == fromDomain_ 11110593207902424140321080247206512405358633331993495164878354046817554469948);

  upd p (size 4) (u64 15992936863339206154);
  upd p (size 5) (u64 10037038012062884956);
  upd p (size 6) (u64 15197544864945402661);
  upd p (size 7) (u64 9615747158586711429);
  assert_norm(15992936863339206154 + pow2 64 * 10037038012062884956 + pow2 64 * pow2 64 * 15197544864945402661 + pow2 64 * pow2 64 * pow2 64 * 9615747158586711429 < prime256);
  assert_norm (15992936863339206154 + pow2 64 * 10037038012062884956 + pow2 64 * pow2 64 * 15197544864945402661 + pow2 64 * pow2 64 * pow2 64 * 9615747158586711429 = 60359023176204190920225817201443260813112970217682417638161152432929735267850);
  assert_norm (0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 == fromDomain_ 60359023176204190920225817201443260813112970217682417638161152432929735267850);
  
  
  upd p (size 8) (u64 1);
  upd p (size 9) (u64 18446744069414584320);
  upd p (size 10) (u64 18446744073709551615);
  upd p (size 11) (u64 4294967294);
  assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 < prime256);
  assert_norm (1 = fromDomain_ 26959946660873538059280334323183841250350249843923952699046031785985);
  assert_norm (1 + pow2 64 * 18446744069414584320 + pow2 64 * pow2 64 * 18446744073709551615 + pow2 64 * pow2 64 * pow2 64 * 4294967294 = 26959946660873538059280334323183841250350249843923952699046031785985) 


let scalarMultiplicationWithoutNorm m p result scalar tempBuffer = 
    let h0 = ST.get() in 
  let q = sub tempBuffer (size 0) (size 12) in 
  let buff = sub tempBuffer (size 12) (size 88) in 
  pointToDomain p result;
    let h2 = ST.get() in 

    begin
  match m with 
  |Ladder ->
      montgomery_ladder q result scalar buff
  |_ ->
     let bufferPrecomputed = create (size 192) (u64 0) in 
     generatePrecomputedTable bufferPrecomputed result buff;
     montgomery_ladder_2 q scalar buff bufferPrecomputed
  end;

  copy_point q result 



let secretToPublic m result scalar tempBuffer =
  let buff = sub tempBuffer (size 12) (size 88) in
  begin
  match m with 
  |Ladder -> 
    let basePoint = sub tempBuffer (size 0) (size 12) in 
      uploadBasePoint basePoint;
    montgomery_ladder result basePoint scalar buff
  |Radix4 ->
    montgomery_ladder_2_precomputed result scalar buff
  |Comb -> 
    Hacl.Impl.ScalarMultiplication.RWNAF.scalar_multiplication_cmb result scalar buff
  end; 
    let h1 = ST.get() in 
    lemma_pif_to_domain h1 basePoint;

  norm result result buff



let secretToPublicWithoutNorm m result scalar tempBuffer = 
  let buff = sub tempBuffer (size 12) (size 88) in
  begin
  match m with 
  |Ladder -> 
    let basePoint = create (size 12) (u64 0) in 
      uploadBasePoint basePoint;
      admit();
    montgomery_ladder result basePoint scalar buff;
    admit()
    (* ;copy_point basePoint result *)
  |Radix4 ->
    admit();
    montgomery_ladder_2_precomputed result scalar buff
  |_ -> 
    admit();
    Hacl.Impl.ScalarMultiplication.RWNAF.scalar_multiplication_cmb result scalar buff
  end; 
    admit();
    let h1 = ST.get() in 
    lemma_pif_to_domain h1 basePoint
