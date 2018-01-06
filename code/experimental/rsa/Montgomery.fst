module Montgomery

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Lib
open Convert
open Addition
open Comparison
open Multiplication
open Shift

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
    crLen:size_t{v crLen == rLen /\ 0 < rLen /\ rLen + rLen < max_size_t} ->
    n:lbignum rLen -> exp_2:size_t{v exp_2 > 1} -> i:size_t ->
    cstLen:size_t{v cstLen == stLen /\ stLen = 6 * rLen} -> st:lbignum stLen -> Stack unit
    (requires (fun h -> live h n /\ live h st /\ disjoint st n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 2"

let rec mont_inverse_ #rLen #stLen crLen n exp_2 i cstLen st =
    let cr2Len = add_mod #SIZE crLen crLen in
    let pow2_i1 = Buffer.sub #uint64 #stLen #rLen st (size 0) crLen in
    let pow2_i = Buffer.sub #uint64 #stLen #rLen st crLen crLen in
    let nnInv = Buffer.sub #uint64 #stLen #(rLen + rLen) st cr2Len cr2Len in
    let nnInv_mod = Buffer.sub #uint64 #stLen #rLen st (mul_mod #SIZE (size 4) crLen) crLen in
    let nInv = Buffer.sub #uint64 #stLen #rLen st (mul_mod #SIZE (size 5) crLen) crLen in
    disjoint_sub_lemma1 st n cr2Len cr2Len;
    if (i <. exp_2) then begin
       bn_lshift1 crLen pow2_i1 pow2_i1;
       bn_lshift1 crLen pow2_i1 pow2_i;
       fill cr2Len nnInv (u64 0);
       bn_mul crLen n crLen nInv nnInv; //nnInv = n * nInv
       assume (rLen - v i / 64 - 1 > 0);
       bn_mod_pow2_n cr2Len nnInv i crLen nnInv_mod; // nnInv_mod = nnInv % pow2_i
       (if (bn_is_less crLen pow2_i1 nnInv_mod) then
	   bn_add crLen nInv crLen pow2_i1 nInv);
       mont_inverse_ crLen n exp_2 (size_incr i) cstLen st
    end
	  
val mont_inverse:
    #rLen:size_nat ->
    crLen:size_t{v crLen == rLen /\ 0 < rLen /\ rLen * 6 < max_size_t} -> n:lbignum rLen ->
    exp_2:size_t{0 < v exp_2 /\ v exp_2 + 1 < max_size_t} ->
    nInv:lbignum rLen -> Stack unit
    (requires (fun h -> live h n /\ live h nInv /\ disjoint n nInv))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 nInv h0 h1))

let mont_inverse #rLen crLen n exp_2 nInv =
  let stLen:size_t = mul_mod #SIZE crLen (size 6) in 
  alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem n] [BufItem nInv]
  (fun h0 _ h1 -> True)
  (fun st ->
    let pow2_i1 = Buffer.sub #uint64 #(v stLen) #rLen st (size 0) crLen in
    let nInv_t = Buffer.sub #uint64 #(v stLen) #rLen st (mul_mod #SIZE (size 5) crLen) crLen in
    pow2_i1.(size 0) <- u64 1;
    nInv_t.(size 0) <- u64 1;
    mont_inverse_ crLen n (size_incr exp_2) (size 2) stLen st;
    copy crLen nInv_t nInv
  )

val mont_reduction:
    #rLen:size_nat -> #cLen:size_nat ->
    exp_r:size_t{v exp_r > 0} ->
    rrLen:size_t{v rrLen == rLen /\ 3 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    ccLen:size_t{v ccLen == cLen /\ cLen = rLen + rLen /\ cLen + 4 * rLen < max_size_t} -> c:lbignum cLen ->
    res:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h c /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let mont_reduction #rLen #cLen exp_r rrLen st_mont ccLen c res =
    let crLen:size_t = add_mod #SIZE ccLen rrLen in
    let r2Len:size_t = add_mod #SIZE rrLen rrLen in
    let stLen:size_t = add_mod #SIZE (add_mod #SIZE crLen r2Len) rrLen in

    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem st_mont; BufItem c] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun st ->
      let tmp = Buffer.sub #uint64 #(v stLen) #(v crLen) st (size 0) crLen in
      let tmp1 = Buffer.sub #uint64 #(v stLen) #(v r2Len) st crLen r2Len in
      let m = Buffer.sub #uint64 #(v stLen) #rLen st (add_mod #SIZE crLen r2Len) rrLen in

      let stMLen:size_t = mul_mod #SIZE (size 3) rrLen in
      let r = Buffer.sub #uint64 #(v stMLen) #rLen st_mont (size 0) rrLen in
      let n = Buffer.sub #uint64 #(v stMLen) #rLen st_mont rrLen rrLen in
      let nInv = Buffer.sub #uint64 #(v stMLen) #rLen st_mont r2Len rrLen in

      assume (disjoint tmp c /\ disjoint tmp nInv);
      bn_mul ccLen c rrLen nInv tmp; // tmp = c * nInv
      assume (rLen - v exp_r / 64 - 1 > 0);
      bn_mod_pow2_n crLen tmp exp_r rrLen m; // m = tmp % r
      bn_sub rrLen r rrLen m m; // m = r - m
      assume (disjoint tmp1 m /\ disjoint tmp1 n);
      bn_mul rrLen m rrLen n tmp1; // tmp1 = m * n
      bn_add r2Len tmp1 ccLen c tmp1; // tmp1 = c + tmp1
      assume (v r2Len - v exp_r / 64 - 1 > 0);
      bn_rshift r2Len tmp1 exp_r tmp1; // tmp1 = tmp1 / r

      let tmp1_ = Buffer.sub #uint64 #(v r2Len) #rLen tmp1 (size 0) rrLen in
      copy rrLen tmp1_ res
    )


val to_mont:
    #rLen:size_nat ->
    exp_r:size_t{v exp_r > 0} ->
    rrLen:size_t{v rrLen == rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    r2:lbignum rLen -> a:lbignum rLen ->
    aM:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h r2 /\ live h a /\ live h aM))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 aM h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let to_mont #rLen exp_r rrLen st_mont r2 a aM =
    let cLen:size_t = add_mod #SIZE rrLen rrLen in
    alloc #uint64 #unit #(v cLen) cLen (u64 0) [BufItem st_mont; BufItem r2; BufItem a] [BufItem aM]
    (fun h0 _ h1 -> True)
    (fun c ->
       bn_mul rrLen a rrLen r2 c; // c = a * r2
       mont_reduction exp_r rrLen st_mont cLen c aM //aM = c % n
    )
    
    
val from_mont:
    #rLen:size_nat ->
    exp_r:size_t{v exp_r > 0} ->
    rrLen:size_t{v rrLen == rLen /\ 3 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    aM:lbignum rLen -> a:lbignum rLen -> Stack unit
    (requires (fun h ->  live h st_mont /\ live h aM /\ live h a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 a h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let from_mont #rLen exp_r rrLen st_mont aM a =
    let r2Len:size_t = add_mod #SIZE rrLen rrLen in
    let stLen:size_t = add_mod #SIZE r2Len rrLen in
    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem st_mont; BufItem aM] [BufItem a]
    (fun h0 _ h1 -> True)
    (fun st ->
      let tmp = Buffer.sub #uint64 #(v stLen) #(v r2Len) st (size 0) r2Len in
      let m = Buffer.sub #uint64 #(v stLen) #rLen st r2Len rrLen in

      let stMLen:size_t = mul_mod #SIZE (size 3) rrLen in
      let r = Buffer.sub #uint64 #(v stMLen) #rLen st_mont (size 0) rrLen in
      let n = Buffer.sub #uint64 #(v stMLen) #rLen st_mont rrLen rrLen in
      let nInv = Buffer.sub #uint64 #(v stMLen) #rLen st_mont r2Len rrLen in
      assume (disjoint tmp nInv /\ disjoint tmp aM);
      bn_mul rrLen aM rrLen nInv tmp; // tmp = aM * nInv
      assume (rLen < v r2Len /\ rLen - v exp_r / 64 - 1 > 0);
      bn_mod_pow2_n r2Len tmp exp_r rrLen m; // m = tmp % r
      bn_sub rrLen r rrLen m m; // m = r - m
      fill r2Len tmp (u64 0);
      assume (disjoint tmp n /\ disjoint tmp m);
      bn_mul rrLen m rrLen n tmp; //tmp = m * n
      bn_add r2Len tmp rrLen aM tmp; //tmp = aM + tmp
      assume (v r2Len - v exp_r / 64 - 1 > 0);
      bn_rshift r2Len tmp exp_r tmp; //tmp = tmp / r
      
      let tmp_ = Buffer.sub #uint64 #(v r2Len) #rLen tmp (size 0) rrLen in
      copy rrLen tmp_ a
    )
    
