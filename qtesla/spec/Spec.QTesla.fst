module Spec.QTesla

open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.RawIntTypes

open Spec.SHA3
open Spec.QTesla.Params

module Loops = Lib.LoopCombinators
module Seq = Lib.Sequence
module FSeq = FStar.Seq

#reset-options "--z3rlimit 80 --max_fuel 0 --max_ifuel 1"

// TODO: this disappeared from Lib.ByteSequence.fsti and I don't know why.
inline_for_extraction
let to_lbytes (b:bytes{Seq.length b > 0 /\ Seq.length b < max_size_t}) : lbytes (Seq.length b) =
  Seq.to_lseq #uint8 b

(** qTesla often uses [pos] as a variable name, so we define a transparent synonym *)
unfold let positive = pos

(** Set this parameter to be the machine word size in bits. *)
unfold let params_w = 64

(** 
* Computes ceil(log2 n) using the equation
* ceil(log2 n) = floor(log2 (2 * n - 1)
*)
private let rec floor_log2 (n:pos) : nat =
  if n = 1 then 0
  else 1 + floor_log2 (n / 2)

val log2: pos -> nat
let log2 n = floor_log2 (2 * n - 1)

(** Computes ceil(a / b) *)
val ceil_div: nat -> pos -> nat
let ceil_div a b = if a % b = 0 then a / b else 1 + a / b

val bytelen: nat -> nat 
let bytelen n = if n = 0 then 1 else ceil_div (log2 (n + 1)) 8

(** ceil(log_2 q) *)
unfold let computed_ceil_log_q = normalize_term (log2 params_q)

(** 
* ceil((log_2 q) / 8)
* Uses the equation ceil(a / b) = ceil(ceil(a) / b) 
*)
unfold let computed_b = normalize_term (ceil_div (log2 params_q) 8)

(** ceil(((log_2 B) + 1) / 8) *)
unfold let computed_ySampler_b = normalize_term (ceil_div (log2 params_B + 1) 8)
  
(** ceil(log_2 B) + 1 *)
unfold let computed_ySampler_modulus = normalize_term (log2 params_B + 1)

/// Polynomial ring

let field_t = x:int{-params_q < x /\ x < params_q}

// Single polynomial in \mathcal{R}_q/<x^n+1>
let poly_t = Seq.lseq field_t params_n

// Set of k polynomials in \mathcal{R}/(x^n+1)
let polys_t = Seq.lseq poly_t params_k 

let qtesla_sk = poly_t & polys_t & (lbytes params_kappa) & (lbytes params_kappa)
let qtesla_pk = (lbytes params_kappa) & polys_t
let qtesla_sig = poly_t & (lbytes params_kappa)

val to_lseq: #a:Type0 -> s:Seq.seq a{Seq.length s <= max_size_t} -> l:Seq.lseq a (Seq.length s){l == s}
let to_lseq #a s = s

let create_poly : poly_t = to_lseq (Seq.create params_n 0)
let create_polys : polys_t = to_lseq (Seq.create params_k create_poly)

(* These functions operate in Z_q/<x^n+1> where q is params_q and n is params_n *)

(* A lot of this polynomial ring math taken from the Kyber spec *)

(* a + b (mod q); a, b \in Z_q *)
val fadd: field_t -> field_t -> field_t
let fadd a b = (a + b) % params_q

(* a - b (mod q); a, b \in Z_q *)
val fsub: field_t -> field_t -> field_t
let fsub a b = (params_q + a - b) % params_q

(* a * b (mod q); a, b \in Z_q *)
val fmul: field_t -> field_t -> field_t
let fmul a b = (a * b) % params_q

(* a ^ b (mod q); a, b \in Z_q *)
val fexp: field_t -> n:nat -> Tot field_t (decreases n)
let rec fexp e n =
  if n = 0 then 1
  else if n = 1 then e
  else
    if n % 2 = 0 then (e `fmul` e) `fexp` (n / 2)
    else e `fmul` ((e `fmul` e) `fexp` ((n-1)/2))

let ( ** ) = fmul
let ( ++ ) = fadd
let ( -- ) = fsub
let ( ^^ ) = fexp

val map2_step: 
    poly_t 
  -> (field_t -> field_t -> field_t) 
  -> poly_t 
  -> poly_t 
  -> i:size_nat{i <= params_n} 
  -> Tot poly_t (decreases (params_n - i))
let rec map2_step res f x y i =
  if i = Seq.length x
  then res
  else let res = Seq.upd res i (f (Seq.index x i) (Seq.index y i)) in
       map2_step res f x y (i + 1)

val map2: (field_t -> field_t -> field_t) -> poly_t -> poly_t -> poly_t
let map2 f x y =
  let res = create_poly in
  map2_step res f x y 0

(* a + b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_add: poly_t -> poly_t -> poly_t
let poly_add a b = map2 fadd a b

(* a - b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_sub: poly_t -> poly_t -> poly_t
let poly_sub a b = map2 fsub a b

(* a o b (mod q) [pointwise coefficient multiplication]; a, b \in \mathcal{R}_q/<x^n+1> *)
val poly_pointwise_mul: poly_t -> poly_t -> poly_t
let poly_pointwise_mul a b = map2 fmul a b

val ntt: poly_t -> poly_t
let ntt p =
  let np = p in
  Loops.repeati params_k (fun i (np:poly_t) ->
		 Seq.upd np i (Loops.repeati params_k (fun j x -> x ++ ((computed_phi ^^ j) ** (Seq.index p j) ** (computed_omega ^^ (i * j)))) 0)) np

val inv_ntt: poly_t -> poly_t
let inv_ntt p =
  let np = p in
  Loops.repeati params_n (fun i (np:poly_t) ->
		 Seq.upd np i (computed_n_inv ** (computed_phi_inv ^^ i) ** Loops.repeati params_n (fun j x -> x ++ ((Seq.index p j) ** (computed_omega_inv ^^ (i * j)))) 0)) np

(* a * b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
(* qTESLA specific assumption: a is always in NTT form, and b is always in standard form. Use poly_mul for two polynomials in standard form. *)
val poly_ntt_mul: poly_t -> poly_t -> poly_t
let poly_ntt_mul a b =
  inv_ntt (a `poly_pointwise_mul` (ntt b))

(* a * b (mod q); a, b \in \mathcal{R}_q/<x^n+1> *)
(* a, b in standard form *)
val poly_mul: poly_t -> poly_t -> poly_t
let poly_mul a b =
  inv_ntt ((ntt a) `poly_pointwise_mul` (ntt b))
  
/// End of polynomial ring math

val sum: list int -> Tot int
let rec sum l =
  match l with
  | [] -> 0
  | hd :: tl -> hd + sum tl

val sort_lseq: #a:eqtype -> #n:size_nat -> (f:FStar.Seq.tot_ord a) -> (s:Seq.lseq a n) -> s':Seq.lseq a n{FSeq.sorted f s' /\ FSeq.permutation a s s'}
let sort_lseq #a #n f s = 
  let fs:FSeq.lseq a n = s in
  FSeq.sort_lseq #a #n f fs

val sort_coefficients: p:poly_t -> poly_t
let sort_coefficients p = sort_lseq (<=) p
  
val poly_max_sum_helper: sorted:poly_t -> h:nat{h < Seq.length sorted} -> int
let rec poly_max_sum_helper sorted h =
  let res = Seq.index sorted h in
    if h = 0
    then res
    else res + poly_max_sum_helper sorted (h - 1)

val poly_max_sum: p:poly_t -> h:nat{h < Seq.length p} -> int
let poly_max_sum p h =
  let sorted = sort_coefficients p in
  FSeq.perm_len sorted p;
  poly_max_sum_helper sorted h
  
// Sum the h largest coefficients of s, and return true if bounded by L_s
val checkS: poly_t -> bool
let checkS s = poly_max_sum s params_h <= params_Ls

// Sum the h largest coefficients of e_i, and return true if bounded by L_e
val checkE: poly_t -> bool
let checkE e = poly_max_sum e params_h <= params_Le

// Given an input pre-seed of \kappa bytes, return a buffer of (\kappa * ((k+3)/8)) bytes extended by the XOF
val prf1: lbytes params_kappa -> lbytes (params_kappa * (params_k+3))
let prf1 preseed = params_prf1 params_kappa preseed (params_kappa * (params_k+3))

val prf2: 
    #mLen:size_nat{mLen < max_size_t - 2 * params_kappa} 
  -> seedY:lbytes params_kappa 
  -> r:lbytes params_kappa 
  -> m:lbytes mLen 
  -> lbytes params_kappa
let prf2 #mLen seedY r m =
  let concatenation = Seq.concat (Seq.concat seedY r) m in
  params_prf2 (Seq.length concatenation) concatenation params_kappa

val genA_getC: 
    cBuf:bytes{Seq.length cBuf < max_size_t} 
  -> cPos:size_nat{(cPos+1) * computed_b <= Seq.length cBuf} 
  -> nat
let genA_getC cBuf cPos = 
  let subbuffer = Seq.slice (to_lbytes cBuf) (cPos * computed_b) ((cPos+1) * computed_b) in
  nat_from_bytes_le subbuffer

val genA_updateA: polys_t -> i:nat{i < params_k * params_n} -> field_t -> polys_t
let genA_updateA a i newVal =
  let polyNum = i / params_n in
  let coefNum = i - params_n * polyNum in
  let ax = Seq.index a polyNum in
  let axy = Seq.upd ax coefNum newVal in
  Seq.upd a polyNum ax

(* We have a strange termination condition with this while loop. If cSHAKE was completely broken, it could theoretically return an array of bytes such that every b-byte subarray interpreted as a natural number was greater than equal to the modulus parameter q. If it kept returning arrays like this, the function could theoretically loop infinitely. Of course this won't happen. It may be possible to prove something like "there is guaranteed to exist at least one element in the output array < q" but without even knowing what is provable about hash functions the F* experts thought this was difficult.

So at their suggestion this code takes a different approach: We define the function to always terminate but with the possibility of failure, and then assume the existence of an "oracle" function that somehow tells us that if we end up calling cSHAKE a certain number of times, we're guaranteed to succeed. This is what the "fuel" parameter in genA_while and the definition of genA_oracle below it are all about. *)

val genA_while: 
    #seedALen:size_nat 
  -> seedA: lbytes seedALen 
  -> cBuf: bytes{Seq.length cBuf < max_size_t /\ Seq.length cBuf >= 2} 
  -> s:nat 
  -> a:polys_t 
  -> pos: size_nat
  -> bPrime:size_nat{bPrime >= 1 /\ params_rateXOF * bPrime = Seq.length cBuf} 
  -> i:nat 
  -> fuel:nat 
  -> Tot (option polys_t) (decreases %[(params_k * params_n - i); fuel])
let rec genA_while #seedALen seedA cBuf s a pos bPrime i fuel =
  assert_norm (0 < computed_b /\ computed_b < 10);
  if fuel = 0 then None 
  else if i < params_k * params_n
  then 
    let s, pos, bPrime, cBuf =
      if pos > ((params_rateXOF * bPrime) / computed_b) - 1 then 
        let s, pos, bPrime = s + 1, 0, 1 in
        let cBuf = params_genA_xof seedALen seedA s (params_rateXOF * bPrime) in
        s, pos, bPrime, cBuf
      else 
        s, pos, bPrime, cBuf 
    in
    let c_pos = genA_getC cBuf pos in
      let a, i, fuel =
        let c_pos_mod = c_pos % (pow2 computed_ceil_log_q) in
	if params_q > c_pos_mod
	then genA_updateA a i c_pos_mod, i + 1, fuel
	else a, i, fuel - 1 
      in
      genA_while #seedALen seedA cBuf s a (pos + 1) bPrime i fuel
  else Some a

assume 
val genA_oracle: 
    #seedALen:size_nat 
  -> seedA: lbytes seedALen 
  -> cBuf: bytes{Seq.length cBuf < max_size_t /\ Seq.length cBuf >= 2} 
  -> s:nat 
  -> a:polys_t 
  -> pos: size_nat{(pos+1) * computed_b < Seq.length cBuf} 
  -> bPrime:size_nat{bPrime >= 1 /\ params_rateXOF * bPrime = Seq.length cBuf} 
  -> i:nat 
  -> Tot (fuel:nat{Some? (genA_while #seedALen seedA cBuf s a pos bPrime i fuel)})
  
val genA: #seedALen:size_nat -> seedA:lbytes seedALen -> polys_t
let genA #seedALen seedA =
  let bPrime = params_bGenA in
  let cBuf = params_genA_xof seedALen seedA 0 (params_rateXOF * bPrime) in
  let i = 0 in
  let pos = 0 in
  let a = create_polys in
  let fuel = genA_oracle seedA cBuf 0 a pos bPrime i in
  let res = genA_while seedA cBuf 0 a pos bPrime i fuel in
  Some?.v res

// Nonce is called "nonce" to avoid confusion; in spec it is S.
// gaussSampler is assumed because it has floating point math we can't
// yet model in F*. random_bytes is assumed because it needs to come from
// an underlying system source.
assume val random_bytes: n: size_nat -> lbytes n

assume val berSampler: r: (lbytes (params_w / 8)) -> t:nat -> bit:nat{bit = 0 \/ bit = 1}

val gaussSampler_doloop3: 
    rand: (lbytes params_kappa) 
  -> nonce: positive
  -> fuel: nat
  -> Tot (option (tuple2 nat positive)) (decreases fuel)
let rec gaussSampler_doloop3 rand nonce fuel =
  assert_norm(bytelen params_xi < max_size_t); // Need to prove this is a size_nat for use with cshake128_frodo.
  if fuel = 0 then None else
  let sample = params_gaussSampler_xof params_kappa rand nonce (bytelen params_xi) in
  let y = nat_from_bytes_le sample in
  let nonce = nonce + 1 in
  if y < params_xi - 1
  then Some (y, nonce)
  else gaussSampler_doloop3 rand nonce (fuel - 1)

assume val gaussSampler_doloop3_oracle:
    rand: (lbytes params_kappa) 
  -> nonce: positive
  -> Tot (fuel:nat{Some? (gaussSampler_doloop3 rand nonce fuel)})

// TODO: need to bound this computation. Why are we guaranteed to hit a
// valid entry in the cdt?
val gaussSampler_doloop10: r: nat -> x:nat{x <= FStar.List.Tot.Base.length cdt_list} -> Tot (res:nat{res < FStar.List.Tot.Base.length cdt_list}) (decreases (FStar.List.Tot.Base.length cdt_list - x))
let rec gaussSampler_doloop10 r x =
  assume(Some? (nth cdt_list x));
  assert_norm(0 < FStar.List.Tot.Base.length cdt_list); // Actually needed.
  if (x >= FStar.List.Tot.Base.length cdt_list) then 0 else
  let y = Some?.v (nth cdt_list x) in
  if r < y
  then x
  else gaussSampler_doloop10 r (x + 1)

val gaussSampler_doloop2: rand: (lbytes params_kappa) -> nonce: positive -> fuel:nat -> Tot (option field_t) (decreases fuel)
let rec gaussSampler_doloop2 rand nonce fuel =
    if fuel = 0 then None else
    let y, nonce = Some?.v (gaussSampler_doloop3 rand nonce (gaussSampler_doloop3_oracle rand nonce)) in
    let sample = params_gaussSampler_xof params_kappa rand nonce (params_w / 8) in
    let r = nat_from_bytes_le sample in
    let nonce = nonce + 1 in
    let x = 0 in
    let x = gaussSampler_doloop10 r x in
    let z:nat = params_xi * x + y in
    assume(z < params_q); // TODO: Patrick tells us this is true.
    let r = params_gaussSampler_xof params_kappa rand nonce (params_w / 8) in
    let nonce = nonce + 1 in
    if (berSampler r (y * (y + 2 * params_xi * x)) = 0)
    then gaussSampler_doloop2 rand nonce (fuel - 1)
    else let b:nat = nat_from_bytes_le (random_bytes 1) in
         if z = 0 && b % 2 = 0
	 then gaussSampler_doloop2 rand nonce (fuel - 1)
	 else if b % 2 = 0
	      then Some z
	      else Some ((-1) * z)
	 
assume val gaussSampler_doloop2_oracle: 
    rand: (lbytes params_kappa) 
  -> nonce: positive 
  -> Tot (fuel:nat{Some? (gaussSampler_doloop2 rand nonce fuel)})

val gaussSampler: rand: (lbytes params_kappa) -> nonce: positive -> Tot field_t
let gaussSampler rand nonce =
    let nonce = nonce * (pow2 8) in
    let fuel = gaussSampler_doloop2_oracle rand nonce in
    Some?.v (gaussSampler_doloop2 rand nonce fuel)

val gaussSampler_poly: rand: (lbytes params_kappa) -> nonce: positive -> Tot poly_t
let gaussSampler_poly rand nonce =
    let p = create_poly in
    Loops.repeati params_n (fun i (p:poly_t) ->
                        Seq.upd p i (gaussSampler rand nonce)) p

// Termination is probabilistic due to the need to get the right sort
// of output from the sampler, and so we use the fuel method again.
val keygen_sample_while: 
    seed: lbytes params_kappa 
  -> nonce: positive 
  -> checkFn: (poly_t -> bool) 
  -> fuel: nat 
  -> Tot (option (tuple2 poly_t positive)) (decreases fuel)
let rec keygen_sample_while seed nonce checkFn fuel =
  if fuel = 0 then None else
  let s = gaussSampler_poly seed nonce in
  if checkFn s then Some (s, nonce)
               else let nonce = nonce + 1 in
	            keygen_sample_while seed nonce checkFn (fuel - 1)

assume val keygen_sample_oracle: 
    seed: lbytes params_kappa
  -> nonce: positive
  -> checkFn: (poly_t -> bool) 
  -> Tot (fuel:nat{Some? (keygen_sample_while seed nonce checkFn fuel)})

let keygen_sampleS_while seedS nonce = 
  Some?.v (keygen_sample_while seedS nonce checkS (keygen_sample_oracle seedS nonce checkS))

let keygen_sampleE_while seedE nonce = 
  Some?.v (keygen_sample_while seedE nonce checkE (keygen_sample_oracle seedE nonce checkE))

val keygen_sampleE_step: 
    seedE:lbytes (params_kappa * params_k) 
  -> nonce:positive 
  -> e:polys_t 
  -> i:size_nat{i <= Seq.length e} 
  -> Tot (tuple2 polys_t positive) (decreases (Seq.length e - i))
let rec keygen_sampleE_step seedE nonce e i =
  if i = Seq.length e then 
    e, nonce
  else 
    let seedEi = Seq.sub seedE (i * params_kappa) params_kappa in
    let ei, nonce = keygen_sampleE_while seedEi nonce in
    let e = Seq.upd e i ei in
    keygen_sampleE_step seedE nonce e (i + 1)

val keygen_sampleE: 
    seedE:(lbytes (params_kappa * params_k)) 
  -> nonce:positive 
  -> tuple2 polys_t positive
let keygen_sampleE seedE nonce = 
  let e = create_polys in
  keygen_sampleE_step seedE nonce e 0

val poly_mod: f:poly_t -> n:nat{2 <= n /\ n <= params_q} -> poly_t
let poly_mod f n =
  Loops.repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = (Seq.index f i) % n in
    Seq.upd f i fi) f

val keygen_computeT_step: 
     a:polys_t 
   -> s:poly_t 
   -> e:polys_t 
   -> t:polys_t 
   -> i:size_nat{i <= Seq.length a} 
   -> Tot polys_t (decreases (Seq.length a - i))
let rec keygen_computeT_step a s e t i =
  if i = Seq.length a then t
  else // Remember, a is always in NTT form; other polys in standard form
    let ti = (((Seq.index a i) `poly_ntt_mul` s) `poly_add` (Seq.index e i)) `poly_mod` params_q in
    let t = Seq.upd t i ti in
    keygen_computeT_step a s e t (i + 1)

val keygen_computeT: a:polys_t -> s:poly_t -> e:polys_t -> polys_t
let keygen_computeT a s e =
  let t = create_polys in
  keygen_computeT_step a s e t 0

val qTesla_keygen: qtesla_sk & qtesla_pk
let qTesla_keygen =
  let preseed = random_bytes params_kappa in
  let seedbuf = prf1 preseed in
  let seedS_begin = 0 in
  let seedS_len = params_kappa in
  let seedS = Seq.sub seedbuf seedS_begin seedS_len in

  let seedE_begin = seedS_begin + seedS_len in
  let seedE_len = params_k * params_kappa in
  let seedE = Seq.sub seedbuf seedE_begin seedE_len in

  let seedA_begin = seedE_begin + seedE_len in
  let seedA_len = params_kappa in
  let seedA = Seq.sub seedbuf seedA_begin seedA_len in

  let seedY_begin = seedA_begin + seedA_len in
  let seedY_len = params_kappa in
  let seedY = Seq.sub seedbuf seedY_begin seedY_len in

  let a = genA seedA in
  let nonce = 1 in
  let s, nonce = keygen_sampleS_while seedS nonce in
  let e, nonce = keygen_sampleE seedE nonce in
  let t = keygen_computeT a s e in
  let sk = (s, e, seedA, seedY) in
  let pk = (seedA, t) in
  sk, pk

val ySampler_while: 
    rand: lbytes params_kappa 
  -> cBuf: bytes{Seq.length cBuf < max_size_t /\ Seq.length cBuf >= 2} 
  -> p: size_nat 
  -> nPrime: size_nat{computed_ySampler_b * nPrime <= max_size_t /\ computed_ySampler_b * nPrime = Seq.length cBuf} 
  -> sPrime: nat 
  -> i: size_nat{i <= params_n} 
  -> y: poly_t 
  -> fuel:nat 
  -> Tot (option poly_t) (decreases %[(params_n - i); fuel])
let rec ySampler_while rand cBuf pos nPrime sPrime i y fuel =
  if fuel = 0 then None else
  let b = computed_ySampler_b in
  if i < params_n
  then let sPrime, pos, nPrime, cBuf =
    if pos >= nPrime 
    then let sPrime, pos, nPrime = sPrime + 1, 0, params_rateXOF / b in
         let cBuf = params_ysampler_xof (Seq.length rand) rand sPrime params_rateXOF in
         sPrime, pos, nPrime, cBuf
    else sPrime, pos, nPrime, cBuf in
    let yi = (nat_from_bytes_le (Seq.slice (to_lbytes cBuf) (pos * b) ((pos + 1) * b))) % (pow2 computed_ySampler_modulus) - params_B in
    assert(yi < pow2 computed_ySampler_modulus);
    assert_norm(pow2 computed_ySampler_modulus < params_q);
    assert(yi < params_q);
    let y = Seq.upd y i yi in
    let i, fuel = if yi <> params_B + 1 then i+1, fuel else i, fuel-1 in
    let pos = pos + 1 in
    ySampler_while rand cBuf pos nPrime sPrime i y fuel
  else Some y

assume 
val ySampler_oracle: 
    rand: lbytes params_kappa 
  -> cBuf: bytes{Seq.length cBuf < max_size_t /\ Seq.length cBuf >= 2} 
  -> pos: size_nat 
  -> nPrime: size_nat{computed_ySampler_b * nPrime <= max_size_t /\ computed_ySampler_b * nPrime = Seq.length cBuf} 
  -> sPrime: nat 
  -> i: size_nat{i <= params_n} 
  -> y: poly_t 
  -> Tot (fuel:nat{Some? (ySampler_while rand cBuf pos nPrime sPrime i y fuel)})

val ySampler: rand: (lbytes params_kappa) -> nonce: positive -> poly_t
let ySampler rand nonce =
  let b = computed_ySampler_b in
  let y = create_poly in
  let pos, nPrime, sPrime = 0, params_n, nonce * 256 in
  let cBuf = params_ysampler_xof (Seq.length rand) rand sPrime (b * nPrime) in
  let i = 0 in
  let fuel = ySampler_oracle rand cBuf pos nPrime sPrime i y in
  Some?.v (ySampler_while rand cBuf pos nPrime sPrime i y fuel)

val hashH: 
    #mlen: size_nat{params_k * params_n + mlen <= max_size_t} 
  -> v: polys_t 
  -> mdig: lbytes mlen{mlen = 64} // 64 is hard-coded in the spec as the output of G provided here.
  -> lbytes params_kappa
let hashH #mlen v mdig =
  let w = Seq.create (params_k * params_n + 64) (u8 0) in
  let w = Loops.repeati params_k
    (fun i w -> Loops.repeati params_n
      (fun j w -> let vij:field_t = (Seq.index (Seq.index v i) j) in
               assert_norm(vij % (pow2 params_d) >= 0);
	       assert_norm(vij % (pow2 params_d) < pow2 params_d);
	       assert_norm(pow2 params_d < params_q);
	       let val_:field_t = vij % (pow2 params_d) in
	       let val_:field_t = assert_norm(val_ - (pow2 params_d) > -params_q);
				     if val_ > (pow2 (params_d - 1))
				     then val_ - (pow2 params_d)
				     else val_ in
               let wiInt = (vij - val_) / (pow2 params_d) in
	       (* TODO: Patrick tells us the above math guarantees wiInt is < 2^8. We should prove this properly. Assume it for now. *)
	       assume (0 <= wiInt /\ wiInt < maxint U8);
	       let wi = u8 wiInt in
	       Seq.upd w (i * params_n + j) wi // w.[i * params_n + j] <- wi
      ) w
    ) w in
  let w = Loops.repeati mlen
    (fun i w -> Seq.upd w (params_k * params_n + i) (Seq.index mdig i)) w in
  let cPrime = params_hashH_shake (Seq.length w) w params_kappa in
  cPrime

let signlist_elt = x:int{x = -1 \/ x == 1}
let signlist_t = Seq.lseq signlist_elt params_h

val enc_while_getR: #rLen:size_nat -> rBuf:lbytes rLen -> i:nat{i < rLen} -> x:nat{x < 256}
let enc_while_getR #rLen rBuf i =
  let byte = Seq.slice rBuf i (i+1) in
  nat_from_bytes_le byte

(* pos_list and sign_list aren't returned by this function in the spec, although they are used in the implementation. We compute them here for consistency but only return c. *)
val enc_while: 
    cPrime:lbytes params_kappa
  -> rBuf:lbytes params_rateXOF
  -> pos_list: Seq.lseq int params_h
  -> sign_list: signlist_t 
  -> cnt: size_nat 
  -> c: poly_t 
  -> s: nat
  -> i: size_nat 
  -> fuel: nat 
  -> Tot (option poly_t) (decreases %[(params_h - i); fuel])
let rec enc_while cPrime rBuf pos_list sign_list cnt c s i fuel =
  if fuel = 0 then None else
  if i < params_h then 
    let cnt, s, rBuf =
    if cnt > (params_rateXOF - 3)
    then let s, cnt = s + 1, 0 in // TODO: add_mod ok?
	 let rBuf = params_enc_xof params_kappa cPrime s params_rateXOF in
	 cnt, s, rBuf
    else cnt, s, rBuf in
  let pos = ((enc_while_getR rBuf cnt) * 256 + (enc_while_getR rBuf (cnt+1))) % params_n in
  let c, i, fuel, pos_list, sign_list = 
    if Seq.index c pos = 0 
    then let cpos:signlist_elt = if (enc_while_getR rBuf cnt + 2) % 2 = 1 then -1 else 1 in
         let c:poly_t = Seq.upd c pos cpos in 
	 let pos_list = Seq.upd pos_list i pos in
	 let sign_list = Seq.upd sign_list i (Seq.index c pos) in
	 let i = i + 1 in
	 c, i, fuel, pos_list, sign_list
    else c, i, fuel - 1, pos_list, sign_list in
  let cnt = cnt + 3 in
  enc_while cPrime rBuf pos_list sign_list cnt c s i fuel
  else Some c

assume 
val enc_oracle: 
    cPrime: (lbytes params_kappa) 
  -> rBuf: (lbytes params_rateXOF) 
  -> pos_list: (Seq.lseq int params_h) 
  -> sign_list: signlist_t 
  -> cnt: size_nat{cnt < params_rateXOF - 2} 
  -> c: poly_t 
  -> s: nat 
  -> i: size_nat 
  -> Tot (fuel: nat{Some? (enc_while cPrime rBuf pos_list sign_list cnt c s i fuel)})

val enc: lbytes params_kappa -> poly_t
let enc cPrime =
  let s = 0 in
  let cnt = 0 in
  let rBuf = params_enc_xof params_kappa cPrime s params_rateXOF in
  let i = 0 in
  let c:poly_t = create_poly in
  let pos_list: Seq.lseq int params_h = Seq.create params_h 0 in
  let sign_list: signlist_t = Seq.create params_h 1 in 
  let fuel = enc_oracle cPrime rBuf pos_list sign_list cnt c s i in
  let res = enc_while cPrime rBuf pos_list sign_list cnt c s i fuel in
  Some?.v res

val mod_pm: int -> n:nat{n >= 2} -> Tot (x:int{x >= -(n/2) /\ x <= n/2})
let mod_pm a n =
  let res = a % n in
  if res <= n/2 
  then res 
  else res - n

let intL n =
  assert_norm(pow2 params_d >= 2);
  mod_pm n (pow2 params_d)
  
// mod_pm: R_q x Z -> R_q
val poly_mod_pm: poly_t -> n:nat{n >= 2 /\ n <= params_q} -> poly_t
let poly_mod_pm f n =
  Loops.repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = (Seq.index f i) `mod_pm` n in
    Seq.upd f i fi) f

let fnL f = 
  // These facts about 2^d need to be explicitly proven to satisfy the precondition on poly_mod_pm.
  assert_norm(pow2 params_d >= 2);
  assert_norm(pow2 params_d <= params_q);
  poly_mod_pm f (pow2 params_d)

#reset-options "--z3rlimit 100 --max_fuel 0"

// [*]_M: Z -> Z
val intM: c: int -> field_t
let intM c = 
  admit(); // TODO (kkane): Temporary to get the Makefile working
  assert_norm(pow2 params_d >= 2);
  let res = ((c `mod_pm` params_q) - (c `mod_pm` (pow2 params_d))) / (pow2 params_d) in
  res

// [*]_M: R_q -> R_q
val fnM: f: poly_t -> Tot poly_t
let fnM f =
  Loops.repeati (Seq.length f)
  (fun i (f:poly_t) ->
    let fi = intM (Seq.index f i) in
    Seq.upd f i fi) f

// [*]_M applied to a set of polynomials f_1, ..., f_k
val polysM: p: polys_t -> Tot polys_t
let polysM p =
  Loops.repeati (Seq.length p)
  (fun i (p:polys_t) ->
    let pi = fnM (Seq.index p i) in
    Seq.upd p i pi) p

// Returns true if the polynomial is rejected. Used in signing.
val test_rejection: z:poly_t -> Tot bool
let test_rejection z =
  let (res:bool) = false in
  Loops.repeati params_n
  (fun i res -> res || ((abs (Seq.index z i)) > (params_B - params_Ls))) res

// Returns true if the polynomial is rejected. Used in verification.
val test_z: z:poly_t -> Tot bool
let test_z z =
  let (res:bool) = false in
  Loops.repeati params_n
  (fun i res -> res || 
             ((Seq.index z i) < -(params_B - params_Ls)) ||
	     ((Seq.index z i) > (params_B - params_Ls))) res

// For some reason, if I open FStar.Math.Lib to get max, it breaks the
// definition of cshake128_frodo above. So I've just copied it here since
// it's simple
let max x y = if x >= y then x else y

val lInfiniteNorm: p:poly_t -> Tot field_t
let lInfiniteNorm p =
  let maxVal:field_t = (abs (Seq.index p 0)) in
  Loops.repeati (params_n - 1)
  (fun i (maxVal:field_t) -> max maxVal (abs (Seq.index p (i+1)))) maxVal
 
val test_w: w:polys_t -> Tot bool
let test_w w =
  let (res:bool) = false in
  Loops.repeati params_k
  (fun i res -> res || 
    (lInfiniteNorm (fnL (Seq.index w i))) >= ((pow2 (params_d - 1)) - params_Le) ||
    (lInfiniteNorm (Seq.index w i)) >= (params_q / 2) - params_Le) res

val hashG: #mlen: size_nat -> m: lbytes mlen -> Tot (lbytes 64)
let hashG #mlen m = params_hashG mlen m 64
    
val qtesla_sign_step4: #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sk: qtesla_sk -> r: (lbytes params_kappa) -> rand: (lbytes params_kappa) -> counter:positive -> fuel:nat -> Tot (option qtesla_sig) (decreases fuel)
let rec qtesla_sign_step4 #mLen m sk r rand counter fuel =
  if fuel = 0 then None else
  let s, e, seedA, seedY = sk in
  let y = ySampler rand counter in
  let a = genA seedA in
  let v:polys_t = Seq.create params_k (Seq.create params_n 0) in
  let v = Loops.repeati params_k 
    (fun i (v:polys_t) -> 
      let vi:poly_t = ((Seq.index a i) `poly_ntt_mul` y) `poly_mod_pm` params_q in
      Seq.upd v i vi) v in
  let cPrime = hashH (polysM v) (hashG m) in
  let c = enc cPrime in
  let z = y `poly_add` (s `poly_mul` c) in
  if test_rejection z
  then qtesla_sign_step4 m sk r rand (counter + 1) (fuel - 1)
  else let w:polys_t = create_polys in
       let w:polys_t = Loops.repeati params_k 
       (fun i (w:polys_t) -> 
	 let (wi:poly_t) = ((Seq.index v i) `poly_sub` ((Seq.index e i) `poly_mul` c)) `poly_mod_pm` params_q in
	 Seq.upd w i wi) w in
       if test_w w
       then qtesla_sign_step4 m sk r rand (counter + 1) (fuel - 1)
       else Some (z, cPrime)

assume 
val qtesla_sign_oracle: 
    #mLen: size_nat{params_k * params_n + mLen <= max_size_t} 
  -> m: (lbytes mLen) 
  -> sk: qtesla_sk 
  -> r: (lbytes params_kappa) 
  -> rand: (lbytes params_kappa) 
  -> counter:positive 
  -> Tot (fuel:nat{Some? (qtesla_sign_step4 #mLen m sk r rand counter fuel)})

val qtesla_sign: #mLen: size_nat{params_k * params_n + mLen <= max_size_t} -> m: (lbytes mLen) -> sk: qtesla_sk -> Tot qtesla_sig
let qtesla_sign #mLen m sk =
  let s, e, seedA, seedY = sk in
  let counter = 1 in
  let r = random_bytes params_kappa in
  let rand = prf2 seedY r (hashG m) in
  let fuel = qtesla_sign_oracle m sk r rand counter in
  let res = qtesla_sign_step4 m sk r rand counter fuel in
  Some?.v res

let compare (#len:size_nat) (test_expected:lbytes len) (test_result:lbytes len) =
  lbytes_eq test_expected test_result

val qtesla_verify: 
    #mLen: size_nat{params_k * params_n + mLen <= max_size_t} 
  -> m: (lbytes mLen) 
  -> sig: qtesla_sig 
  -> pk: qtesla_pk 
  -> bool
let qtesla_verify #mLen m sig pk =
  let z, cPrime = sig in
  let seedA, t = pk in
  let c = enc cPrime in
  let a = genA seedA in
  let w = create_polys in
  let w = Loops.repeati params_k
    (fun i (w:polys_t) -> 
      let ai = Seq.index a i in
      let ti = Seq.index t i in
      let wi = ((ai `poly_ntt_mul` z) `poly_sub` (ti `poly_mul` c)) `poly_mod_pm` params_q in
      Seq.upd w i wi) w in
  if test_rejection z || not (compare cPrime (hashH (polysM w) (hashG m)))
  then false
  else true
