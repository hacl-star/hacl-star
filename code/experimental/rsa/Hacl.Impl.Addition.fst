module Hacl.Impl.Addition

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib

module Buffer = Spec.Lib.IntBuf


val addcarry_u64: 
    carry:uint64 -> a:uint64 -> b:uint64 -> Tot (tuple2 uint64 uint64)
[@"c_inline"]    
let addcarry_u64 carry a b =
    let t1 = add_mod #U64 a carry in
    let carry = if (lt_u64 t1 carry) then u64 1 else u64 0 in
    let res = add_mod #U64 t1 b in
    let carry = if (lt_u64 res t1) then add #U64 carry (u64 1) else carry in
    (carry, res)
  
val subborrow_u64:
    carry:uint64 -> a:uint64 -> b:uint64 -> Tot (tuple2 uint64 uint64)
    [@"c_inline"]
let subborrow_u64 carry a b =
    let res = sub_mod #U64 (sub_mod #U64 a b) carry in
    let carry =
        if (eq_u64 carry (u64 1)) then
           (if (le_u64 a b) then u64 1 else u64 0)
        else
           (if (lt_u64 a b) then u64 1 else u64 0) in
    (carry, res)

val bval:
    #bLen:size_nat -> cbLen:size_t{v cbLen == bLen} ->
    b:lbignum bLen -> i:size_t -> Stack uint64
    (requires (fun h -> live h b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
    [@"c_inline"]
let bval #bLen cbLen b i =
    if (i <. cbLen) then b.(i) else u64 0
    
val bn_sub_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} -> carry:uint64 ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_sub_ #aLen #bLen caLen a cbLen b i carry res =
    if (i <. caLen) then begin
       let t1 = a.(i) in
       let t2 = bval cbLen b i in
       let (carry, res_i) = subborrow_u64 carry t1 t2 in
       res.(i) <- res_i;
       bn_sub_ #aLen #bLen caLen a cbLen b (size_incr i) carry res
    end

(* a must be greater than b *)
(* ADD: isMore aLen bLen a b *)
(* res = a - b *)
val bn_sub:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_sub #aLen #bLen caLen a cbLen b res =
    bn_sub_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res

val bn_add_:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
    i:size_t{v i <= aLen} -> carry:uint64 ->
    res:lbignum aLen -> Stack uint64
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_add_ #aLen #bLen caLen a cbLen b i carry res =
    if (i <. caLen) then begin
       let t1 = a.(i) in
       let t2 = bval cbLen b i in
       let (carry, res_i) = addcarry_u64 carry t1 t2 in
       res.(i) <- res_i;
       bn_add_ #aLen #bLen caLen a cbLen b (size_incr i) carry res end
    else carry

val bn_add:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_add #aLen #bLen caLen a cbLen b res =
    let _ = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res in ()

val bn_add_carry:
    #aLen:size_nat -> #bLen:size_nat ->
    caLen:size_t{v caLen == aLen /\ aLen + 1 < max_size_t} -> a:lbignum aLen ->
    cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
    res:lbignum (aLen + 1) -> Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_add_carry #aLen #bLen caLen a cbLen b res =
    let res' = Buffer.sub #uint64 #(aLen + 1) #aLen res (size 0) caLen in
    let carry = bn_add_ #aLen #bLen caLen a cbLen b (size 0) (u64 0) res' in
    res.(caLen) <- carry

val bn_sub_u64_:
    #aLen:size_nat -> aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen -> carry:uint64 -> i:size_t ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let rec bn_sub_u64_ #aLen aaLen a carry i res =
    if (i <. aaLen) then begin
       let t1 = a.(i) in
       let res_i = sub_mod #U64 t1 carry in
       res.(i) <- res_i;
       let carry = if (lt_u64 t1 carry) then u64 1 else u64 0 in
       bn_sub_u64_ #aLen aaLen a carry (size_incr i) res
    end
    
val bn_sub_u64:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen ->
    b:uint64 ->
    res:lbignum aLen -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    [@"c_inline"]
let bn_sub_u64 #aLen aaLen a b res = bn_sub_u64_ #aLen aaLen a b (size 0) res
