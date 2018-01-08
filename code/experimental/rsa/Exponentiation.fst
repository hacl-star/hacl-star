module Exponentiation

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Lib
open Convert
open Montgomery
open Multiplication

module Buffer = Spec.Lib.IntBuf

val mul_mod_mont:
    #rLen:size_nat ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    aM:lbignum rLen -> bM:lbignum rLen ->
    resM:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h aM /\ live h bM /\ live h resM))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 resM h0 h1))

let mul_mod_mont #rLen exp_r rrLen st_mont aM bM resM =
    let cLen = add #SIZE rrLen rrLen in
    
    alloc #uint64 #unit #(v cLen) cLen (u64 0) [BufItem st_mont; BufItem aM; BufItem bM] [BufItem resM]
    (fun h0 _ h1 -> True)
    (fun c ->
       bn_mul rrLen aM rrLen bM c; // c = a * b
       mont_reduction exp_r rrLen st_mont cLen c resM // resM = c % n
    )
   
val mod_exp_:
    #rLen:size_nat -> #bLen:size_nat ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    st_exp:lbignum (2 * rLen) ->
    bBits:size_t{0 < v bBits} ->
    bbLen:size_t{v bbLen == bLen /\ bLen = v (bits_to_bn bBits) /\ v bBits / 64 <= bLen} ->
    b:lbignum bLen ->
    count:size_t{v count <= v bBits} -> Stack unit
    (requires (fun h -> live h st_mont /\ live h st_exp /\ live h b))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st_exp h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 "

let rec mod_exp_ #rLen #bLen exp_r rrLen st_mont st_exp bBits bbLen b count =
    let aM = Buffer.sub #uint64 #(rLen + rLen) #rLen st_exp (size 0) rrLen in
    let accM = Buffer.sub #uint64 #(rLen + rLen) #rLen st_exp rrLen rrLen in
    
    if (count <. bBits) then begin
        (if (bn_is_bit_set bbLen b count) then begin
            mul_mod_mont exp_r rrLen st_mont aM accM accM end); //acc = (acc * a) % n
        mul_mod_mont exp_r rrLen st_mont aM aM aM; //a = (a * a) % n
	mod_exp_ exp_r rrLen st_mont st_exp bBits bbLen b (size_incr count)
    end

val mod_exp_mont:
    #rLen:size_nat -> #stLen:size_nat ->
    bBits:size_t{0 < v bBits} -> b:lbignum (v (bits_to_bn bBits)) ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 9 * rLen < max_size_t} ->
    sstLen:size_t{v sstLen == stLen /\ stLen = 9 * rLen} -> st:lbignum stLen -> Stack unit
    (requires (fun h -> live h b /\ live h st /\ disjoint st b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"

let mod_exp_mont #rLen #stLen bBits b exp_r rrLen sstLen st =
    let bLen = bits_to_bn bBits in
    assert (v bBits / 64 <= v bLen);
    
    let r = Buffer.sub #uint64 #stLen #rLen st (size 0) rrLen in
    let n1 = Buffer.sub #uint64 #stLen #rLen st rrLen rrLen in
    let nInv = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 2) rrLen) rrLen in
    let r2 = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 3) rrLen) rrLen in
    
    let a1 = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 4) rrLen) rrLen in
    let acc = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 5) rrLen) rrLen in
    let aM = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 6) rrLen) rrLen in
    let accM = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 7) rrLen) rrLen in
    let res1 = Buffer.sub #uint64 #stLen #rLen st (mul #SIZE (size 8) rrLen) rrLen in
    
    let st_mont = Buffer.sub #uint64 #stLen #(3 * rLen) st (size 0) (mul #SIZE (size 3) rrLen) in
    let st_exp = Buffer.sub #uint64 #stLen #(2 * rLen) st (mul #SIZE (size 6) rrLen) (mul #SIZE (size 2) rrLen) in

    to_mont exp_r rrLen st_mont r2 a1 aM;
    to_mont exp_r rrLen st_mont r2 acc accM;

    mod_exp_ exp_r rrLen st_mont st_exp bBits bLen b (size 0);

    from_mont exp_r rrLen st_mont accM res1
    
// res = a ^^ b mod n
val mod_exp:
    #nLen:size_nat ->
    modBits:size_t{0 < v modBits /\ 2 * v modBits + 4 < max_size_t} ->
    nnLen:size_t{v nnLen == nLen /\ 0 < nLen /\ nLen = v (bits_to_bn modBits) /\ 
		 9 * v (bits_to_bn (add #SIZE modBits (size 2))) < max_size_t} ->
    n:lbignum nLen -> a:lbignum nLen ->
    bBits:size_t{0 < v bBits} -> b:lbignum (v (bits_to_bn bBits)) ->
    res:lbignum nLen -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"

let mod_exp #nLen modBits nnLen n a bBits b res =
    let exp_r = add #SIZE modBits (size 2) in
    let rBits = add #SIZE modBits (size 3) in
    let rLen = bits_to_bn rBits in
    assert (v rLen = (v rBits - 1) / 64 + 1);
    assert (nLen = (v modBits - 1) / 64 + 1);
    assert (9 * v rLen < max_size_t);
    assert (nLen <= v rLen);
    assert (v exp_r / 64 < v rLen);
    assert (v modBits / 64 < v rLen);
    
    let stLen = mul #SIZE (size 9) rLen in
    let stMLen = mul #SIZE (size 3) rLen in
    let exp2 = add #SIZE exp_r exp_r in
    
    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem n; BufItem a; BufItem b] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun st ->
      let r = Buffer.sub #uint64 #(v stLen) #(v rLen) st (size 0) rLen in
      let n1 = Buffer.sub #uint64 #(v stLen) #(v rLen) st rLen rLen in
      let nInv = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 2) rLen) rLen in
      let r2 = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 3) rLen) rLen in
      let a1 = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 4) rLen) rLen in
      let acc = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 5) rLen) rLen in
      //let aM = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 6) rLen) rLen in
      //let accM = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 7) rLen) rLen in
      let res1 = Buffer.sub #uint64 #(v stLen) #(v rLen) st (mul #SIZE (size 8) rLen) rLen in
      //let st_mont = Buffer.sub #uint64 #(v stLen) #(3 * v rLen) st (size 0) (mul #SIZE (size 3) rLen) in
      //let st_exp = Buffer.sub #uint64 #(v stLen) #(2 * v rLen) st (mul #SIZE (size 6) rLen) (mul #SIZE (size 2) rLen) in
      
      let n1_ = Buffer.sub #uint64 #(v rLen) #nLen n1 (size 0) nnLen in
      let a1_ = Buffer.sub #uint64 #(v rLen) #nLen a1 (size 0) nnLen in
      let res1_ = Buffer.sub #uint64 #(v rLen) #nLen res1 (size 0) nnLen in
      
      copy nnLen n n1_;
      copy nnLen a a1_;
      acc.(size 0) <- u64 1;
      bn_set_bit rLen r exp_r; // r = pow2 (2 + modBits)
      bn_pow2_mod_n modBits rLen n1 exp2 r2; // r2 = r * r % n
      mont_inverse rLen n1 exp_r nInv; // n * nInv = 1 (mod r)
      mod_exp_mont #(v rLen) #(v stLen) bBits b exp_r rLen stLen st;
      
      copy nnLen res1_ res
    )
