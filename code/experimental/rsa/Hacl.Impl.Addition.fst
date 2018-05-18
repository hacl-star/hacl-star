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

val bn_sub_:
  #aLen:size_nat -> #bLen:size_nat ->
  caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
  cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
  carry:lbignum 1 -> res:lbignum aLen -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h res /\ live h carry))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_sub_ #aLen #bLen caLen a cbLen b carry res =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 #uint64 #uint64 #1 #aLen caLen carry res
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval cbLen b i in
    let (c, res_i) = subborrow_u64 carry.(size 0) t1 t2 in
    carry.(size 0) <- c;
    res.(i) <- res_i
  )

val bn_sub:
  #aLen:size_nat -> #bLen:size_nat ->
  caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
  cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
  res:lbignum aLen -> Stack uint64
  (requires (fun h -> live h a /\ live h b /\ live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_sub #aLen #bLen caLen a cbLen b res =
  alloc #uint64 #uint64 #1 (size 1) (u64 0) [BufItem a; BufItem b] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun carry ->
    bn_sub_ #aLen #bLen caLen a cbLen b carry res;
    carry.(size 0)
  )

val bn_add_:
  #aLen:size_nat -> #bLen:size_nat ->
  caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
  cbLen:size_t{v cbLen == bLen} -> b:lbignum bLen ->
  carry:lbignum 1 -> res:lbignum aLen -> Stack unit
  (requires (fun h -> live h a /\ live h b /\ live h res /\ live h carry))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 carry res h0 h1))
  [@ "substitute"]
let bn_add_ #aLen #bLen caLen a cbLen b carry res =
  let h0 = FStar.HyperStack.ST.get() in
  loop2_simple #h0 #uint64 #uint64 #1 #aLen caLen carry res
  (fun i ->
    let t1 = a.(i) in
    let t2 = bval cbLen b i in
    let (c, res_i) = addcarry_u64 carry.(size 0) t1 t2 in
    carry.(size 0) <- c;
    res.(i) <- res_i
  )

val bn_add:
  #aLen:size_nat -> #bLen:size_nat ->
  caLen:size_t{v caLen == aLen} -> a:lbignum aLen ->
  cbLen:size_t{v cbLen == bLen /\ bLen <= aLen} -> b:lbignum bLen ->
  res:lbignum aLen -> Stack uint64
  (requires (fun h -> live h a /\ live h b /\ live h res))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  [@"c_inline"]
let bn_add #aLen #bLen caLen a cbLen b res =
  alloc #uint64 #uint64 #1 (size 1) (u64 0) [BufItem a; BufItem b] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun carry ->
    bn_add_ #aLen #bLen caLen a cbLen b carry res;
    carry.(size 0)
  )
