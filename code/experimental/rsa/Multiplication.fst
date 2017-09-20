module Multiplication

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast

module U32 = FStar.UInt32
module U64 = FStar.UInt64

type bignum = buffer FStar.UInt64.t

val mult64: x:U64.t -> y:U64.t -> Tot (U64.t * U64.t)
#set-options "--z3rlimit 300"
let mult64 x y =
    let a = U64.(x >>^ 32ul) in
    assert(U64.v a < pow2 32);
    let b = uint64_to_uint32 x in let b = uint32_to_uint64 b in
    assert(U64.v b < pow2 32);
    let c = U64.(y >>^ 32ul) in
    assert(U64.v c < pow2 32);
    let d = uint64_to_uint32 x in let d = uint32_to_uint64 d in
    assert(U64.v d < pow2 32);

    let ac = U64.(a *^ c) in
    let bc = U64.(b *^ c) in
    let ad = U64.(a *^ d) in
    let bd = U64.(b *^ d) in

    let t1 = U64.(bd >>^ 32ul) in
    //assert(U64.v t1 < pow2 32);
    let t2 = uint64_to_uint32 bc in let t2 = uint32_to_uint64 t2 in
    //assert(U64.v t2 < pow2 32);
    let t3 = uint64_to_uint32 ad in let t3 = uint32_to_uint64 t3 in 
    //assert(U64.v t3 < pow2 32);
    let mid = U64.(t1 +%^ t2 +%^ t3) in

    let t1 = U64.(bc >>^ 32ul) in
    //assert(U64.v t1 < pow2 32);
    let t2 = U64.(mid >>^ 32ul) in
    //assert(U64.v t2 < pow2 32);
    
    let upper64 = U64.(ac +%^ t1 +%^ t2) in
    let t3 = uint64_to_uint32 bd in let t3 = uint32_to_uint64 t3 in
    //assert(U64.v t3 < pow2 32); 
    let lower64 = U64.((mid <<^ 32ul) |^ t3) in
    (upper64, lower64)

val add64: x:U64.t -> y:U64.t -> Tot (U64.t * U64.t)
let add64 x y =
    let res = U64.(x +%^ y) in
    let carry = if U64.(res <^ x) then 1uL else 0uL in
    (carry, res)

val mult_inner_loop:
    aLen:U32.t ->
    a:bignum{U32.v aLen = length a} ->
    b:bignum ->
    i:U32.t{U32.v i < length b} -> 
    j:U32.t{U32.v j <= U32.v aLen} ->
    carry:U64.t -> 
    res:bignum{U32.v i + U32.v j < length res /\ length res = U32.v aLen + length b} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\ 
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let rec mult_inner_loop aLen a b i j carry res =
    if U32.(j <^ aLen) then
       (let (carry1, s1) = mult64 a.(j) b.(i) in
        let (carry2, s2) = add64 res.(U32.(i +^ j)) s1 in
        let (carry3, s3) = add64 s2 carry in
        let carry = U64.(carry1 +%^ carry2 +%^ carry3) in
        res.(U32.(i +^ j)) <- s3;
        mult_inner_loop aLen a b i U32.(j +^ 1ul) carry res)
    else res.(U32.(i +^ aLen)) <- carry

val mult_outer_loop:
    aLen:U32.t -> bLen:U32.t ->
    a:bignum{U32.v aLen = length a} -> 
    b:bignum{U32.v bLen = length b} ->
    i:U32.t{U32.(i <=^ bLen)} -> 
    res:bignum{U32.v aLen + U32.v bLen = length res} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let rec mult_outer_loop aLen bLen a b i res =
    if U32.(i <^ bLen) then
       (mult_inner_loop aLen a b i 0ul 0uL res;
        mult_outer_loop aLen bLen a b U32.(i +^ 1ul) res)
    else ()

(* res = a * b *)
val mult:
    aLen:U32.t -> bLen:U32.t ->
    a:bignum{U32.v aLen = length a} -> 
    b:bignum{U32.v bLen = length b} ->
    res:bignum{U32.v aLen + U32.v bLen = length res} -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
let mult aLen bLen a b res =
    mult_outer_loop aLen bLen a b 0ul res

(* TODO: res = a * a *)
val sqr:
    aLen:U32.t -> a:bignum{U32.v aLen = length a} ->
    res:bignum{length res = U32.v aLen + U32.v aLen} -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 res /\ modifies_1 res h0 h1))
let sqr aLen a res =
    mult aLen aLen a a res