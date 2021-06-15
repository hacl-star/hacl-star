module Hacl.Impl.EC.ScalarMultiplication.WNAF

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Hacl.Impl.EC.MontgomeryLadder
open Spec.ECC.Curves
open Spec.ECC
  


inline_for_extraction noextract
let dradix_wnaf = (u64 64)

inline_for_extraction noextract
let radix = (u64 5)

inline_for_extraction noextract
let dradix = size (pow2 (v radix))

open FStar.Mul
#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0" 

noextract
let lenPrecompWnaf: size_t = size (pow2 (v radix - 1))


let post_precomp_wnaf #c (b: Lib.Sequence.lseq uint64 (v (getPointLenU64 c) * v lenPrecompWnaf)) (generator : point_seq c) = 
  let len = v (getPointLenU64 c) in
  let generator = point_seq_as_nat c generator in 
  forall (i: nat {i >= 0 && i < v lenPrecompWnaf}). 
    let index = 2 * i + 1 in 
    let pointZero = point_seq_as_nat c (Lib.Sequence.sub b (i * len) len) in 
    pointEqual pointZero (point_mult #c index generator) 


val uploadOne: #c: curve -> gen: point c -> b: lbuffer uint64 (getPointLenU64 c *. lenPrecompWnaf) -> Stack unit 
  (requires fun h -> live h gen /\ live h b /\ disjoint gen b /\ point_eval c h gen)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ (
    let pointZero = gsub b (size 0) (getPointLenU64 c) in 
    let gen = point_as_nat c h0 gen in 
    point_eval c h1 pointZero /\ (
    pointEqual (point_as_nat c h1 pointZero) (point_mult #c 1 gen))))

let uploadOne #c gen b = 
  assume (v (getPointLenU64 c) <= v (getPointLenU64 c *. dradix >>. 1ul));
  let zeroP = sub b (size 0) (getPointLenU64 c) in 
  copy zeroP gen 
  

val generatePrecomputedTableWNAF: #c: curve 
  -> generator: point c
  -> b: lbuffer uint64 (getPointLenU64 c *. lenPrecompWnaf) -> 
  Stack unit  
  (requires fun h -> live h generator /\ live h b /\ disjoint generator b)
  (ensures fun h0 _ h1 -> modifies (loc b) h0 h1 /\ post_precomp_wnaf #c (as_seq h1 b) (as_seq h0 generator))


let generatePrecomputedTableWNAF #c generator b = admit()


val subborrow_u64: x:uint64 -> y:uint64 -> r:lbuffer uint64 (size 1) ->
  Stack uint64
  (requires fun h -> live h r)
  (ensures  fun h0 c h1 -> modifies1 r h0 h1 /\ (let r = Seq.index (as_seq h1 r) 0 in v r - v c * pow2 64 == v x - v y))

let subborrow_u64 x y r = 
  admit();
  let x1 = to_u128 x -. to_u128 y in 
  let x2 = logand x1 (u128 0xffffffffffffffff) in 
  let x3 = shift_right x1 (size 64) in
  upd r (size 0) (to_u64 x2);
  (u64 0) -. (to_u64 x3)


open Lib.RawIntTypes


assume val mod2w: d: uint8 -> Tot uint8


val scalar_wnaf_step: #c: curve -> window: lbuffer uint8 (size 1) 
  -> out: lbuffer uint8 (getScalarLen c +! 1ul) -> i: size_t {v i < v (getScalarLen c +! 1ul)} ->
  Stack unit 
    (requires fun h -> live h window)
    (ensures fun h0 _ h1 -> True)

let scalar_wnaf_step #c window out i = 
  let window = index window (size 0) in 
  let windowMod2 = u8_to_UInt8 (logand window 1uy) in
  let windowMod2Zero = FStar.UInt8.eq windowMod2 (FStar.UInt8 .(0uy)) in 
  let d = if windowMod2Zero then 0ul else mod2w window in 
  upd out i d
  




val scalar_wnaf: #c: curve
  -> out: lbuffer uint8 (getScalarLen c +! 1ul) 
  -> scalar: scalar_t #MUT #c 
  -> Stack unit 
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let scalar_wnaf #c out scalar = 
  let windowStart = index scalar (getScalarLenBytes c -! 1ul) in 
  ()
