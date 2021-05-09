module Spec.WNAF

open FStar.Mul

open Lib.ByteSequence
open Lib.IntTypes
open Lib.Sequence

open Lib.LoopCombinators 

open Spec.ECC.Curves
open Spec.ECC

open FStar.Math.Lib

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"


(* if (d mod 2w) >= 2w−1
       return (d mod 2w) − 2w
   else
       return d mod 2w
*)

type nat_windowed (w: nat) = a: nat {a < pow2 w /\ (a == 0 \/ a % 2 == 1)}


val mod_win: di: nat {di % 2 == 1} -> w: pos -> tuple2 
  (* sign is negative only when we need to use the point negation *)
  (sign: bool {let dModWindow = di % pow2 w in sign == false <==> dModWindow >= pow2 (w - 1)})
  (diR: nat_windowed w {diR <= di /\ (
    let dModWindow = di % pow2 w in 
    diR == (if dModWindow >= pow2 (w - 1) then abs (dModWindow - pow2 w) else dModWindow))})


let mod_win di w = 
  let di_mod_2w = di % (pow2 w) in 
  FStar.Math.Lemmas.pow2_modulo_modulo_lemma_1 di 1 w;
  if di_mod_2w >= pow2 (w - 1) then 
    begin
      let sign = di_mod_2w >= pow2 w in
      if sign = false then begin
	FStar.Math.Lemmas.pow2_plus 1 (w - 1);
	false, (pow2 w - di_mod_2w) end
      else
	true, di_mod_2w - (pow2 w)
    end
  else
    true, di_mod_2w 
   



(*  i ← 0
   while (d > 0) do
       if (d mod 2) = 1 then 
           di ← d mods 2w
           d ← d − di
       else
           di = 0
       d ← d/2
       i ← i + 1
   return (di−1, di-2, …, d0)
*)


val scalar_to_wnaf_step: #c: curve -> d: nat -> w: pos -> i: nat {i < v (getScalarLenBytes c)} 
  -> Tot (tuple2 (tuple2 
  (sign: bool {let dModWindow = d % pow2 w in sign == false <==> (d % 2 == 1 /\ dModWindow >= pow2 (w - 1))})
  (dR: nat_windowed w {dR = (
    if d % 2 = 0 then 0 else 
    let dModWindow = d % pow2 w in 
    (if dModWindow >= pow2 (w - 1) then abs (dModWindow - pow2 w) else dModWindow))}))
  (dU: nat))
      
let scalar_to_wnaf_step #c d window i = 
  if d % 2 = 0 then (true, 0), (arithmetic_shift_right d 1) else 
  let sign, di = mod_win d window in 
  let dUp: nat = d - di in 
  let dNew: nat = arithmetic_shift_right dUp 1 in 
  ((sign, di), dNew)


val scalar_to_wnaf_step_l: #c: curve -> window: pos 
  -> index: nat {index < v (getScalarLenBytes c)}
  -> i: tuple2 (lseq (tuple2 bool (nat_windowed window)) (v (getScalarLenBytes c))) nat 
  -> tuple2 (lseq (tuple2 bool (nat_windowed window)) (v (getScalarLenBytes c))) nat

let scalar_to_wnaf_step_l #c window index i = 
  let (l, d) = i in 
  let di, dNew = scalar_to_wnaf_step #c d window index in 
  upd l index di, dNew


val scalar_to_wnaf: #c: curve -> s: scalar_bytes #c -> window: pos -> Tot (lseq (tuple2 bool (nat_windowed window)) (v (getScalarLen c)))

let scalar_to_wnaf #c s w =  
  let d: nat = scalar_as_nat #c s in 
  let l = Lib.Sequence.create (v (getScalarLen c)) (false, 0) in  
  let result, _ = Lib.LoopCombinators.repeati (v (getScalarLen c)) (scalar_to_wnaf_step_l #c w) (l, d) in 
  result


(*
   Q ← 0
   for j ← i − 1 downto 0 do
       Q ← point_double(Q)
       if (dj != 0)
           Q ← point_add(Q, djG)
   return Q
*)

assume val precomputePoints: #c: curve -> window: pos {pow2 window < pow2 32} -> lseq (point_nat_prime #c) (pow2 window) 



val pointNegation: #c: curve ->  p: point_nat_prime #c -> point_nat_prime #c

let pointNegation #c p = 
  let (x, y, z) = p in 
  x, ((0 - y) % getPrime c), z


val getPointPrecomputed: #c: curve -> window: pos {pow2 window < pow2 32} 
  -> l: lseq (point_nat_prime #c) (pow2 window) -> i: nat {i < pow2 window} -> point_nat_prime #c 

let getPointPrecomputed #c window l i = 
  Lib.Sequence.index l i


val wnaf_point_multiplication_step: #c: curve -> window: pos {pow2 window < pow2 32} 
  -> s: lseq (tuple2 bool (nat_windowed window)) (v (getScalarLenBytes c)) 
  -> precomputedPoints:lseq (point_nat_prime #c) (pow2 window) 
  -> i: nat {i <= v (getScalarLen c)} 
  -> q: point_nat_prime #c ->
  Tot (point_nat_prime #c)

let wnaf_point_multiplication_step #c window s precomputePoints i q =  
  let q = pointAdd q q in 
  let sign, di = Lib.Sequence.index s i in 
  if di = 0 then q else
    let point = getPointPrecomputed window precomputePoints di in 
    let r = if sign = false then pointNegation point else point in 
    pointAdd q r


assume val wnaf_as_nat: #c: curve -> w: pos ->  s: lseq (tuple2 bool (nat_windowed w)) (v (getScalarLen c)) -> Tot nat


val wnaf_point_multiplication: #c: curve -> window: pos {pow2 window < pow2 32} -> s: scalar_bytes #c ->
  i: point_nat_prime #c ->
  Tot (o: point_nat_prime #c {pointEqual o (point_mult (scalar_as_nat #c s) i)})


let wnaf_point_multiplication #c window s i = 
  let precomputedPoints = precomputePoints #c window in 
  let scalar_wnaf = scalar_to_wnaf s window in 

  let pred index (r: point_nat_prime #c) : Type0 = pointEqual r (point_mult (wnaf_as_nat #c window scalar_wnaf) i) in 
admit();
  Lib.LoopCombinators.repeati_inductive' (v (getScalarLen c)) pred (wnaf_point_multiplication_step window scalar_wnaf precomputedPoints) i
