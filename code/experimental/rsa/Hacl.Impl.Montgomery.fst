module Hacl.Impl.Montgomery

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Convert
open Hacl.Impl.Addition
open Hacl.Impl.Comparison
open Hacl.Impl.Multiplication
open Hacl.Impl.Shift

module Buffer = Spec.Lib.IntBuf

val bn_pow2_mod_n_:
    #rLen:size_nat ->
    crLen:size_t{v crLen == rLen} -> a:lbignum rLen ->
    i:size_t -> p:size_t ->
    r:lbignum rLen -> Stack unit
    (requires (fun h -> live h a /\ live h r /\ disjoint r a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 r h0 h1))
	
let rec bn_pow2_mod_n_ #rLen clen a i p r =
    if (i <. p) then begin
        bn_lshift1 #rLen clen r r;
        (if not (bn_is_less #rLen clen r a) then
            bn_sub clen r clen a r);
        bn_pow2_mod_n_ clen a (size_incr i) p r
    end

// res = 2 ^^ p % a
val bn_pow2_mod_n:
    #rLen:size_nat ->
    aBits:size_t ->
    crLen:size_t{v crLen == rLen /\ v aBits / 64 < rLen} -> a:lbignum rLen ->
    p:size_t{v p > v aBits} ->
    r:lbignum rLen -> Stack unit
    (requires (fun h -> live h a /\ live h r /\ disjoint r a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 r h0 h1))

let bn_pow2_mod_n #rLen aBits rLen a p r =
    bn_set_bit rLen r aBits;
    bn_sub rLen r rLen a r; // r = r - a
    bn_pow2_mod_n_ rLen a aBits p r

val mont_inverse_:
    #rLen:size_nat -> #stLen:size_nat ->
    crLen:size_t{v crLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    n:lbignum rLen ->
    exp_2:size_t{1 < v exp_2 /\ rLen == v exp_2 / 64 + 1} ->
    i:size_t{v i <= v exp_2 + 1 /\ v exp_2 + 1 < max_size_t} ->
    cstLen:size_t{v cstLen == stLen /\ stLen = 6 * rLen} -> st:lbignum stLen -> Stack unit
    (requires (fun h -> live h n /\ live h st /\ disjoint st n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 2"

let rec mont_inverse_ #rLen #stLen crLen n exp_2 i cstLen st =
    let cr2Len = add #SIZE crLen crLen in
    let pow2_i1 = Buffer.sub #uint64 #stLen #rLen st (size 0) crLen in
    let pow2_i = Buffer.sub #uint64 #stLen #rLen st crLen crLen in
    let nnInv = Buffer.sub #uint64 #stLen #(v cr2Len) st cr2Len cr2Len in
    let nnInv_mod = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 4) crLen) crLen in
    let nInv = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 5) crLen) crLen in
    disjoint_sub_lemma1 st n cr2Len cr2Len;
    
    if (i <=. exp_2) then begin
       bn_lshift1 crLen pow2_i1 pow2_i1;
       bn_lshift1 crLen pow2_i1 pow2_i;
       fill cr2Len nnInv (u64 0);
       bn_mul crLen n crLen nInv nnInv; //nnInv = n * nInv

       assert (rLen - v i / 64 - 1 >= 0);
       bn_mod_pow2_n cr2Len nnInv i crLen nnInv_mod; // nnInv_mod = nnInv % pow2_i
       (if (bn_is_less crLen pow2_i1 nnInv_mod) then
	   bn_add crLen nInv crLen pow2_i1 nInv);
       mont_inverse_ crLen n exp_2 (size_incr i) cstLen st
    end
	  
val mont_inverse:
    #rLen:size_nat ->
    crLen:size_t{v crLen == rLen /\ 0 < rLen /\ rLen * 6 < max_size_t} ->
    n:lbignum rLen ->
    exp_2:size_t{1 < v exp_2 /\ v exp_2 + 1 < max_size_t /\ rLen == v exp_2 / 64 + 1} ->
    nInv:lbignum rLen -> Stack unit
    (requires (fun h -> live h n /\ live h nInv /\ disjoint n nInv))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 nInv h0 h1))

let mont_inverse #rLen crLen n exp_2 nInv =
  let stLen = mul #SIZE crLen (size 6) in
  alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem n] [BufItem nInv]
  (fun h0 _ h1 -> True)
  (fun st ->
    let pow2_i1 = Buffer.sub #uint64 #(v stLen) #rLen st (size 0) crLen in
    let nInv_t = Buffer.sub #uint64 #(v stLen) #rLen st (mul #SIZE (size 5) crLen) crLen in
    pow2_i1.(size 0) <- u64 1;
    nInv_t.(size 0) <- u64 1;
    mont_inverse_ crLen n exp_2 (size 2) stLen st;
    copy crLen nInv_t nInv
  )

val mont_reduction:
    #rLen:size_nat -> #cLen:size_nat ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->    
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) -> st:lbignum (3 * rLen) ->
    st_kara:lbignum (4 * v pow2_i) ->
    ccLen:size_t{v ccLen == cLen /\ cLen = rLen + rLen} -> c:lbignum cLen ->
    res:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h c /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let mont_reduction #rLen #cLen pow2_i iLen exp_r rrLen st_mont st st_kara ccLen c res =
    let r2Len = add #SIZE rrLen rrLen in
    let stLen = mul #SIZE (size 3) rrLen in
    fill stLen st (u64 0);
    let tmp1 = Buffer.sub #uint64 #(v stLen) #(v r2Len) st (size 0) r2Len in
    let m = Buffer.sub #uint64 #(v stLen) #rLen st r2Len rrLen in
      
    let r = Buffer.sub #uint64 #(v stLen) #rLen st_mont (size 0) rrLen in
    let n = Buffer.sub #uint64 #(v stLen) #rLen st_mont rrLen rrLen in
    let nInv = Buffer.sub #uint64 #(v stLen) #rLen st_mont r2Len rrLen in

    let c1 = Buffer.sub #uint64 #cLen #rLen c (size 0) rrLen in
    //bn_mul rrLen c1 rrLen nInv tmp1; // tmp1 = c1 * nInv
    karatsuba #rLen pow2_i iLen rrLen c1 nInv st_kara tmp1; // tmp1 = c1 * nInv
    bn_mod_pow2_n r2Len tmp1 exp_r rrLen m; // m = tmp1 % r
    bn_sub rrLen r rrLen m m; // m = r - m
    fill r2Len tmp1 (u64 0);
    //bn_mul rrLen m rrLen n tmp1; // tmp1 = m * n
    karatsuba #rLen pow2_i iLen rrLen m n st_kara tmp1; // tmp1 = m * n
    bn_add r2Len tmp1 ccLen c tmp1; // tmp1 = c + tmp1
    bn_rshift r2Len tmp1 exp_r tmp1; // tmp1 = tmp1 / r

    let tmp1_ = Buffer.sub #uint64 #(v r2Len) #rLen tmp1 (size 0) rrLen in
    copy rrLen tmp1_ res

val to_mont:
    #rLen:size_nat ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) -> st:lbignum (5 * rLen) ->
    st_kara:lbignum (4 * v pow2_i) ->
    r2:lbignum rLen -> a:lbignum rLen ->
    aM:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h r2 /\ live h a /\ live h aM))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 aM h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let to_mont #rLen pow2_i iLen exp_r rrLen st_mont st st_kara r2 a aM =
    let cLen = add #SIZE rrLen rrLen in
    let stLen = mul #SIZE (size 3) rrLen in
    let c = Buffer.sub #uint64 #(5 * rLen) #(v cLen) st (size 0) cLen in
    let st = Buffer.sub #uint64 #(5 * rLen) #(3 * rLen) st cLen stLen in
    fill cLen c (u64 0);
    //bn_mul rrLen a rrLen r2 c; // c = a * r2
    karatsuba #rLen pow2_i iLen rrLen a r2 st_kara c; // c = a * r2 
    mont_reduction pow2_i iLen exp_r rrLen st_mont st st_kara cLen c aM //aM = c % n
    
    
val from_mont:
    #rLen:size_nat ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) -> st:lbignum (3 * rLen) ->
    st_kara:lbignum (4 * v pow2_i) ->
    aM:lbignum rLen -> a:lbignum rLen -> Stack unit
    (requires (fun h ->  live h st_mont /\ live h aM /\ live h a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 a h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let from_mont #rLen pow2_i iLen exp_r rrLen st_mont st st_kara aM a =
    let r2Len = add #SIZE rrLen rrLen in
    let stLen = mul #SIZE (size 3) rrLen in
    fill stLen st (u64 0);
    
    let tmp = Buffer.sub #uint64 #(v stLen) #(v r2Len) st (size 0) r2Len in
    let m = Buffer.sub #uint64 #(v stLen) #rLen st r2Len rrLen in

    let r = Buffer.sub #uint64 #(v stLen) #rLen st_mont (size 0) rrLen in
    let n = Buffer.sub #uint64 #(v stLen) #rLen st_mont rrLen rrLen in
    let nInv = Buffer.sub #uint64 #(v stLen) #rLen st_mont r2Len rrLen in
      
    disjoint_sub_lemma1 st aM (size 0) r2Len;
    //bn_mul rrLen aM rrLen nInv tmp; // tmp = aM * nInv
    karatsuba #rLen pow2_i iLen rrLen aM nInv st_kara tmp; // tmp = aM * nInv 
    bn_mod_pow2_n r2Len tmp exp_r rrLen m; // m = tmp % r
    bn_sub rrLen r rrLen m m; // m = r - m
    fill r2Len tmp (u64 0);
    //bn_mul rrLen m rrLen n tmp; //tmp = m * n
    karatsuba #rLen pow2_i iLen rrLen m n st_kara tmp; // tmp = m * n    
    bn_add r2Len tmp rrLen aM tmp; //tmp = aM + tmp
    bn_rshift r2Len tmp exp_r tmp; //tmp = tmp / r
      
    let tmp_ = Buffer.sub #uint64 #(v r2Len) #rLen tmp (size 0) rrLen in
    copy rrLen tmp_ a
