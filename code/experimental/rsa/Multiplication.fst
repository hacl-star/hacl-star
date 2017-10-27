module Multiplication

open FStar.HyperStack.All
open FStar.Buffer
open FStar.Int.Cast
open Lib

module U32 = FStar.UInt32
module U64 = FStar.UInt64
open U32

val mult64: x:U64.t -> y:U64.t -> Tot (U64.t * U64.t)
let mult64 x y =
    let a = U64.(x >>^ 32ul) in
    let b = uint64_to_uint32 x in let b = uint32_to_uint64 b in
    let c = U64.(y >>^ 32ul) in
    let d = uint64_to_uint32 y in let d = uint32_to_uint64 d in

    let ac = U64.(a *%^ c) in
    let bc = U64.(b *%^ c) in
    let ad = U64.(a *%^ d) in
    let bd = U64.(b *%^ d) in

    let t1 = U64.(bd >>^ 32ul) in
    let t2 = uint64_to_uint32 bc in let t2 = uint32_to_uint64 t2 in
    let t3 = uint64_to_uint32 ad in let t3 = uint32_to_uint64 t3 in 
    let mid = U64.(t1 +%^ t2 +%^ t3) in

    let t1 = U64.(bc >>^ 32ul) in
    let t2 = U64.(ad >>^ 32ul) in
    let t3 = U64.(mid >>^ 32ul) in

    let upper64 = U64.(ac +%^ t1 +%^ t2 +%^ t3) in
    let t4 = uint64_to_uint32 bd in let t4 = uint32_to_uint64 t4 in
    let lower64 = U64.((mid <<^ 32ul) |^ t4) in
    (upper64, lower64)

val add64: x:U64.t -> y:U64.t -> Tot (U64.t * U64.t)
let add64 x y =
    let res = U64.(x +%^ y) in
    let carry = if U64.(res <^ x) then 1uL else 0uL in
    (carry, res)

val mult_by_limb_addj:
    aLen:bnlen -> a:lbignum aLen ->
    l:U64.t -> i:U32.t{v i <= v aLen} -> j:U32.t ->
    resLen:U32.t{v aLen + v j < v resLen} ->
    carry:U64.t -> res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))

#reset-options "--z3rlimit 150 --max_fuel 2"

let rec mult_by_limb_addj aLen a l i j resLen carry res =
    if U32.(i <^ aLen) then begin
        let (carry1, res_ij) = mult64 a.(i) l in
        let (carry2, res_ij) = add64 res_ij carry in
        let (carry3, res_ij) = add64 res_ij res.(i +^ j) in
        let carry' = U64.(carry1 +%^ carry2 +%^ carry3) in
        res.(i +^ j) <- res_ij;
        mult_by_limb_addj aLen a l (i +^ 1ul) j resLen carry' res end
    else
        res.(i +^ j) <- carry

val mult_loop:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    j:U32.t{U32.v j <= U32.v bLen} ->
    resLen:U32.t{v resLen = v aLen + v bLen} -> res:lbignum resLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))

#reset-options

let rec mult_loop aLen a bLen b j resLen res =
    if U32.(j <^ bLen) then begin
        mult_by_limb_addj aLen a b.(j) 0ul j resLen 0uL res;
        mult_loop aLen a bLen b (j +^ 1ul) resLen res
        end

(* res = a * b *)
val mult:
    aLen:bnlen -> a:lbignum aLen ->
    bLen:bnlen -> b:lbignum bLen ->
    res:lbignum U32.(aLen +^ bLen) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h0 res /\
        live h1 a /\ live h1 b /\ live h1 res /\ modifies_1 res h0 h1))
        
let mult aLen a bLen b res =
    mult_loop aLen a bLen b 0ul (aLen +^ bLen) res

(* TODO: res = a * a *)
val sqr:
    aLen:bnlen -> a:lbignum aLen ->
    res:lbignum U32.(aLen +^ aLen) -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 res /\ 
        live h1 a /\ live h1 res /\ modifies_1 res h0 h1))
        
let sqr aLen a res =
    mult aLen a aLen a res