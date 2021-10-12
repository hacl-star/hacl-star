module Hacl.Impl.EC.MontgomeryLadder

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Spec.ECC
open Spec.ECC.Curves

open Hacl.Impl.EC.PointAdd
open Hacl.Impl.P.PointAdd.Aux
open Hacl.Impl.EC.PointDouble

open Lib.Loops

open Hacl.EC.Lemmas

open FStar.Mul
open Hacl.Spec.MontgomeryMultiplication
open Hacl.Impl.EC.Masking.ScalarAccess


#set-options " --z3rlimit 200"

inline_for_extraction noextract
val swap: #c: curve ->  p: point_seq c -> q: point_seq c -> 
  Tot (r: tuple2 (point_seq c) (point_seq c) {let pNew, qNew = r in pNew == q /\ qNew == p})

let swap p q = (q, p)


val conditional_swap: #c: curve -> i: uint64 -> p: point_seq c -> q: point_seq c -> 
  Tot (r: tuple2 (point_seq c) (point_seq c) {
    let pNew, qNew = r in 
    if uint_v i = 0 then pNew == p /\ qNew == q
    else let p1, q1 = swap p q in p1 == pNew /\ q1 == qNew})

let conditional_swap i p q = 
  if uint_v i = 0 then (p, q) else (q, p)


val lemma_PointEqualR: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
  ((~ (pointEqual p q)) <==> ~ (pointEqual q p))

let lemma_PointEqualR #c p q = ()

val lemma_point_as_nat: #c: curve -> h: mem -> h1: mem 
  -> p: point c {point_eval c h p} 
  -> q: point c -> Lemma
  (as_seq h p == as_seq h1 q ==> point_as_nat c h p == point_as_nat c h1 q)

let lemma_point_as_nat #c h h1 p q = 
  let len = getCoordinateLenU64 c in 
  
  let pX = gsub p (size 0) len in 
  let pY = gsub p len len in 
  let pZ = gsub p (size 2 *! len) len in 
  
  let qX = gsub q (size 0) len in 
  let qY = gsub q len len in 
  let qZ = gsub q (size 2 *! len) len in 

  lemma_equal_lseq_equal_nat (as_seq h pX) (as_seq h1 qX);
  lemma_equal_lseq_equal_nat (as_seq h pY) (as_seq h1 qY);
  lemma_equal_lseq_equal_nat (as_seq h pZ) (as_seq h1 qZ)


inline_for_extraction noextract
val cswap: #c: curve -> bit:uint64{v bit <= 1} -> p:point c -> q:point c-> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ eq_or_disjoint p q /\ point_eval c h p /\ point_eval c h q /\
    ~ (pointEqual #c
      (let pX, pY, pZ = point_as_nat c h p in fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ) 
      (let qX, qY, qZ = point_as_nat c h q in fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ)))
  (ensures  fun h0 _ h1 -> modifies (loc p |+| loc q) h0 h1 /\
    point_eval c h1 p /\ point_eval c h1 q /\ (
    v bit == 0 ==> point_as_nat c h1 p == point_as_nat c h0 p /\ point_as_nat c h1 q == point_as_nat c h0 q) /\ (
    v bit == 1 ==> point_as_nat c h1 p == point_as_nat c h0 q /\ point_as_nat c h1 q == point_as_nat c h0 p) /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 p)) (fromDomainPoint #c #DH (point_as_nat c h1 q))))

let cswap #c bit p1 p2 =
  let open Lib.Sequence in 
  let h0 = ST.get () in
  let mask = u64 0 -. bit in
  
  let len = getCoordinateLenU64 c *! size 3 in 

  [@ inline_let]
  let inv h1 (i:nat{i <= uint_v (getCoordinateLenU64 c) * 3}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < uint_v (getCoordinateLenU64 c) * 3}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in
 
  Lib.Loops.for 0ul len inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2);

  if v bit = 1 then begin
    lemma_point_as_nat #c h0 h1 p1 p2;
    lemma_point_as_nat #c h0 h1 p2 p1
    end
  else begin
    lemma_point_as_nat #c h0 h1 p1 p1;
    lemma_point_as_nat #c h0 h1 p2 p2
  end


val pointAddAsAdd: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
    (requires (~ (pointEqual p q)))
    (ensures (pointAdd p q == _point_add p q))

let pointAddAsAdd #c p q = ()

val pointAddAsDouble: #c: curve -> p: point_nat_prime #c -> q: point_nat_prime #c -> Lemma
  (requires (True))
  (ensures (pointAdd p p == _point_double_nist p))

let pointAddAsDouble #c p q = ()


inline_for_extraction
val point_add_as_spec: #c: curve -> p: point c -> q: point c -> result: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> 
  Stack unit (requires fun h -> 
    live h p /\ live h q /\ live h result /\ live h tempBuffer /\ 
    eq_or_disjoint q result /\ disjoint p q /\ disjoint p tempBuffer /\ 
    disjoint q tempBuffer /\ disjoint p result /\ disjoint result tempBuffer /\  
    point_eval c h p /\ point_eval c h q /\ 
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (fromDomainPoint #c #DH (point_as_nat c h q))))
  (ensures fun h0 _ h1 -> 
    modifies (loc tempBuffer |+| loc result) h0 h1 /\ point_eval c h1 result /\ point_eval c h1 p /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
    fromDomainPoint #c #DH (point_as_nat c h1 result) == pointAdd #c pD qD /\ 
    point_as_nat c h0 p == point_as_nat c h1 p))


let point_add_as_spec #c p q result tempBuffer = 
    let h0 = ST.get() in 
  point_add #c p q result tempBuffer;
    let h1 = ST.get() in 
  pointAddAsAdd #c 
    (let pX, pY, pZ = point_as_nat c h0 p in fromDomain #c pX, fromDomain #c pY, fromDomain #c pZ)
    (let qX, qY, qZ = point_as_nat c h0 q in fromDomain #c qX, fromDomain #c qY, fromDomain #c qZ);
  lemma_coord_eval c h0 h1 p
  

inline_for_extraction
val montgomery_ladder_step1: #c : curve -> p: point c -> q: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) -> Stack unit
  (requires fun h ->  live h p /\ live h q /\ live h tempBuffer /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer] /\
    point_eval c h p /\ point_eval c h q /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (fromDomainPoint #c #DH (point_as_nat c h q))))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 p /\ point_eval c h1 q /\ (
    let ml1p, ml1q = _ml_step1 #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 q)) in 
    ml1p == fromDomainPoint #c #DH (point_as_nat c h1 p) /\ ml1q == fromDomainPoint #c #DH (point_as_nat c h1 q) /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 p)) (fromDomainPoint #c #DH (point_as_nat c h1 q)))))


let montgomery_ladder_step1 #c p q tempBuffer = 
  let h0 = ST.get() in
  point_add_as_spec p q q tempBuffer;
    let h1 = ST.get() in 
  point_double p p tempBuffer; 
    let h2 = ST.get() in 
  lemma_coord_eval c h1 h2 q;
  pointAddAsDouble #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 p));
  curve_point_equality #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 q))


inline_for_extraction
val _montgomery_ladder_step: #c: curve -> #buf_type: buftype
  -> p: point c -> q: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> bit: uint64 {v bit <= 1} ->
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\ point_eval c h p /\ point_eval c h q  /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer] /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (fromDomainPoint #c #DH (point_as_nat c h q))))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 p /\ point_eval c h1 q /\ (
    let pM1, qM1 = _ml_step1 #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 q)) in
    let pM0, qM0 = _ml_step0 #c (fromDomainPoint #c #DH (point_as_nat c h0 p)) (fromDomainPoint #c #DH (point_as_nat c h0 q)) in
    
    (~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 p)) (fromDomainPoint #c #DH (point_as_nat c h1 q)))) /\ (
    if v bit = 0 then 
      fromDomainPoint #c #DH (point_as_nat c h1 p) == pM1 /\
      fromDomainPoint #c #DH (point_as_nat c h1 q) == qM1 
    else 
      fromDomainPoint #c #DH (point_as_nat c h1 p) == pM0 /\
      fromDomainPoint #c #DH (point_as_nat c h1 q) == qM0)))


let _montgomery_ladder_step #c #buf_type r0 r1 tempBuffer bit = 
  cswap bit r0 r1; 
  montgomery_ladder_step1 r0 r1 tempBuffer;
  cswap bit r0 r1
    

inline_for_extraction
val montgomery_ladder_step: #c: curve -> #buf_type: buftype
  -> p: point c -> q: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) 
  -> i:size_t {v i < v (getScalarLen c)} -> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h tempBuffer /\ live h scalar /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    point_eval c h p /\ point_eval c h q /\
    ~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h p)) (fromDomainPoint #c #DH (point_as_nat c h q))))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\ 
    point_eval c h1 p /\ point_eval c h1 q /\
    (~ (pointEqual #c (fromDomainPoint #c #DH (point_as_nat c h1 p)) (fromDomainPoint #c #DH (point_as_nat c h1 q)))) /\ (
    let pM, qM = _ml_step #c (as_seq h0 scalar) (v i) (
      fromDomainPoint #c #DH (point_as_nat c h0 p), fromDomainPoint #c #DH (point_as_nat c h0 q)) in    
    fromDomainPoint #c #DH (point_as_nat c h1 p) == pM /\ fromDomainPoint #c #DH (point_as_nat c h1 q) == qM))

let montgomery_ladder_step #c #buf_type r0 r1 tempBuffer scalar i = 
  let bit0 = getScalarLen c -! 1ul -! i in 
  let bit = getScalarBit_leftEndian scalar bit0 in 
  _montgomery_ladder_step #c #buf_type r0 r1 tempBuffer bit
  

val mlStepAsPointAdd: #c: curve 
  -> p0: point_nat_prime #c 
  -> pk: nat
  -> p: point_nat_prime #c {pointEqual p (point_mult #c pk p0)}  
  -> qk: nat 
  -> q: point_nat_prime #c {pointEqual q (point_mult #c qk p0)} 
  -> s: scalar_bytes #c 
  -> i: nat {i < v (getScalarLen c)} ->
  Lemma 
  (requires pk == scalar_as_nat_ s i /\ qk = scalar_as_nat_ s i + 1)
  (ensures (
    let bit = ith_bit s (v (getScalarLen c) - 1 - i) in
    let p_i, q_i = _ml_step s i (p, q) in 
    pointEqual p_i (point_mult (scalar_as_nat_ s (i + 1)) p0) /\
    pointEqual q_i (point_mult (scalar_as_nat_ s (i + 1) + 1) p0)))


let mlStepAsPointAdd #c p0 pk p qk q s i = 
  mlStep1AsPointAdd #c p0 pk p qk q; 
  mlStep0AsPointAdd #c p0 pk p qk q;
  scalar_as_nat_def #c s (i + 1);

  let bit = ith_bit s (v (getScalarLen c) - 1 - i) in
  let p_i, q_i = _ml_step s i (p, q) in 

  assert(scalar_as_nat_ s (i + 1) == 2 * scalar_as_nat_ s i + v bit);

  assert(pk + qk = scalar_as_nat_ s (i + 1) - v bit + 1);
  assert(qk + qk = scalar_as_nat_ s (i + 1) - v bit + 2);
  assert(v bit = 1 ==> 2 * qk == scalar_as_nat_ s (i + 1) + 1);

  assert(  
     if v bit = 0 then 
      pointEqual p_i (point_mult (scalar_as_nat_ s (i + 1)) p0) /\ pointEqual q_i (point_mult (scalar_as_nat_ s (i + 1) + 1) p0)
    else 
      pointEqual p_i (point_mult #c (scalar_as_nat_ s (i + 1)) p0) /\ pointEqual q_i (point_mult #c (scalar_as_nat_ s (i + 1) + 1) p0))


inline_for_extraction noextract
val montgomery_ladder_: #c: curve -> #buf_type: buftype -> p: point c -> q: point c ->
  scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)  -> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h scalar /\  live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    point_eval c h p /\ point_eval c h q /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h q) in 
    pointEqual #c pD (point_mult #c 0 qD) /\ ~ (pointEqual #c pD qD)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\
    point_eval c h1 p /\ point_eval c h1 q /\ ( 
    let p0D = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let q0D = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (p0D, q0D) in 
    (r0, r1) == (pD, qD)  /\
    pointEqual pD (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) q0D)))


let montgomery_ladder_ #c #a p q scalar tempBuffer =  
  let h0 = ST.get() in 

  [@inline_let]
  let len = getCoordinateLenU64 c in 
  let cycleLoop = getScalarLen c in 

  [@inline_let]
  let spec_ml h0 = _ml_step #c (as_seq h0 scalar) in 

  [@inline_let]
  let inv h (i: nat {i <= v (getScalarLen c)}) = 
    point_eval c h p /\ point_eval c h q /\ modifies3 p q tempBuffer h0 h /\ point_eval c h0 p /\ point_eval c h0 q /\ (
    let p0D = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let q0D = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h q) in

    let r0, r1 = Lib.LoopCombinators.repeati i (spec_ml h0) (p0D, q0D) in 
    r0 == pD /\ r1 == qD /\

    pointEqual qD (point_mult #c (scalar_as_nat_ #c (as_seq h0 scalar) i + 1) q0D) /\
    pointEqual pD (point_mult #c (scalar_as_nat_ #c (as_seq h0 scalar) i) q0D) /\ 
    ~ (pointEqual #c pD qD)) in 

   Lib.LoopCombinators.eq_repeati0 (v (getScalarLen c)) (spec_ml h0) 
     (fromDomainPoint #c #DH (point_as_nat c h0 p), fromDomainPoint #c #DH (point_as_nat c h0 q));

  point_mult_0_lemma #c (fromDomainPoint #c #DH (point_as_nat c h0 q)); 
  for 0ul cycleLoop inv (fun i -> 
    let h2 = ST.get() in 
      montgomery_ladder_step p q tempBuffer scalar i; 
	let h3 = ST.get() in 
	
      Lib.LoopCombinators.unfold_repeati (v (getScalarLen c)) (spec_ml h0)
	(fromDomainPoint #c #DH (point_as_nat c h0 p),  fromDomainPoint #c #DH (point_as_nat c h0 q)) (v i);

      mlStepAsPointAdd (fromDomainPoint #c #DH (point_as_nat c h0 q)) 
      (scalar_as_nat_ #c (as_seq h0 scalar) (v i)) (fromDomainPoint #c #DH (point_as_nat c h2 p)) 
      (scalar_as_nat_ #c (as_seq h0 scalar) (v i) + 1) (fromDomainPoint #c #DH (point_as_nat c h2 q)) (as_seq h0 scalar) (v i)
  )

[@CInline]
let montgomery_ladderP256L = montgomery_ladder_ #P256 #MUT
[@CInline]
let montgomery_ladderP256I = montgomery_ladder_ #P256 #IMMUT
[@CInline]
let montgomery_ladderP256C = montgomery_ladder_ #P256 #CONST

[@CInline]
let montgomery_ladderP384L = montgomery_ladder_ #P384 #MUT
[@CInline]
let montgomery_ladderP384I = montgomery_ladder_ #P384 #IMMUT
[@CInline]
let montgomery_ladderP384C = montgomery_ladder_ #P384 #CONST


inline_for_extraction noextract
val montgomery_ladder: #c: curve -> #buf_type: buftype -> p: point c -> q: point c ->
  scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c) -> 
  tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c)  -> 
  Stack unit
  (requires fun h -> live h p /\ live h q /\ live h scalar /\  live h tempBuffer /\
    LowStar.Monotonic.Buffer.all_disjoint [loc p; loc q; loc tempBuffer; loc scalar] /\
    point_eval c h p /\ point_eval c h q /\ (
    let pD = fromDomainPoint #c #DH (point_as_nat c h p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h q) in 
    pointEqual #c pD (point_mult #c 0 qD) /\ ~ (pointEqual #c pD qD)))
  (ensures fun h0 _ h1 -> modifies (loc p |+| loc q |+| loc tempBuffer) h0 h1 /\
    point_eval c h1 p /\ point_eval c h1 q /\ ( 
    let p0D = fromDomainPoint #c #DH (point_as_nat c h0 p) in 
    let q0D = fromDomainPoint #c #DH (point_as_nat c h0 q) in 
    let pD = fromDomainPoint #c #DH (point_as_nat c h1 p) in 
    let qD = fromDomainPoint #c #DH (point_as_nat c h1 q) in 
    let r0, r1 = montgomery_ladder_spec_left (as_seq h0 scalar) (p0D, q0D) in 
    (r0, r1) == (pD, qD)  /\
    pointEqual pD (point_mult #c (scalar_as_nat #c (as_seq h0 scalar)) q0D)))


let montgomery_ladder #c #b p q scalar tempBuffer = 
  match c with 
    |P256 -> begin
      match b with 
      |MUT -> montgomery_ladderP256L p q scalar tempBuffer
      |IMMUT -> montgomery_ladderP256I p q scalar tempBuffer
      |CONST -> montgomery_ladderP256C p q scalar tempBuffer end
    |P384 -> begin
      match b with  
      |MUT -> montgomery_ladderP384L p q scalar tempBuffer
      |IMMUT -> montgomery_ladderP384I p q scalar tempBuffer
      |CONST -> montgomery_ladderP384C p q scalar tempBuffer end
(*     |Default -> begin
      match b with 
      |MUT -> montgomery_ladderGenL p q scalar tempBuffer
      |IMMUT -> montgomery_ladderGenI p q scalar tempBuffer
      |CONST -> montgomery_ladderGenC p q scalar tempBuffer end
  
 *)
