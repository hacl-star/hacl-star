module Hacl.Impl.Exponentiation

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Convert
open Hacl.Impl.Montgomery
open Hacl.Impl.Multiplication

module Buffer = Spec.Lib.IntBuf

val mul_mod_mont:
    #rLen:size_nat ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    st_m:lbignum (3 * rLen) ->
    st_kara:lbignum (2 * rLen + 4 * v pow2_i) ->
    aM:lbignum rLen -> bM:lbignum rLen -> resM:lbignum rLen -> Stack unit
    (requires (fun h -> live h st_mont /\ live h aM /\ live h bM /\ live h resM /\ live h st_kara))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1))

let mul_mod_mont #rLen pow2_i iLen exp_r rrLen st_mont st_m st_kara aM bM resM =
    let cLen = add #SIZE rrLen rrLen in
    let stKLen = mul #SIZE (size 4) pow2_i in
    let stLen = add #SIZE cLen stKLen in
    
    let c = Buffer.sub #uint64 #(v stLen) #(v cLen) st_kara (size 0) cLen in
    let st_k = Buffer.sub #uint64 #(v stLen) #(v stKLen) st_kara cLen stKLen in
    //fill cLen c (u64 0);
    //bn_mul rrLen aM rrLen bM c;
    karatsuba pow2_i iLen rrLen aM bM st_k c; // c = a * b
    mont_reduction pow2_i iLen exp_r rrLen st_mont st_m st_k cLen c resM // resM = c % n
   
val mod_exp_:
    #rLen:size_nat -> #bLen:size_nat ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 6 * rLen < max_size_t} ->
    st_mont:lbignum (3 * rLen) ->
    st_exp:lbignum (2 * rLen) ->
    st_m:lbignum (3 * rLen) ->
    st_kara:lbignum (2 * rLen + 4 * v pow2_i) ->
    bBits:size_t{0 < v bBits} ->
    bbLen:size_t{v bbLen == bLen /\ bLen = v (bits_to_bn bBits) /\ v bBits / 64 <= bLen} ->
    b:lbignum bLen ->
    count:size_t{v count <= v bBits} -> Stack unit
    (requires (fun h -> live h st_mont /\ live h st_exp /\ live h b /\ live h st_kara))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1))

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 "

let rec mod_exp_ #rLen #bLen pow2_i iLen exp_r rrLen st_mont st_exp st_m st_kara bBits bbLen b count =
    let aM = Buffer.sub #uint64 #(rLen + rLen) #rLen st_exp (size 0) rrLen in
    let accM = Buffer.sub #uint64 #(rLen + rLen) #rLen st_exp rrLen rrLen in
    
    if (count <. bBits) then begin
        (if (bn_is_bit_set bbLen b count) then begin
            mul_mod_mont pow2_i iLen exp_r rrLen st_mont st_m st_kara aM accM accM end); //acc = (acc * a) % n
        mul_mod_mont pow2_i iLen exp_r rrLen st_mont st_m st_kara aM aM aM; //a = (a * a) % n
	mod_exp_ pow2_i iLen exp_r rrLen st_mont st_exp st_m st_kara bBits bbLen b (size_incr count)
    end

val mod_exp_mont:
    #rLen:size_nat -> #stLen:size_nat ->
    pow2_i:size_t{rLen + rLen + 4 * v pow2_i < max_size_t /\ rLen < v pow2_i} -> iLen:size_t ->
    bBits:size_t{0 < v bBits} -> b:lbignum (v (bits_to_bn bBits)) ->
    exp_r:size_t{0 < v exp_r /\ rLen = v exp_r / 64 + 1} ->
    rrLen:size_t{v rrLen == rLen /\ 0 < rLen /\ 9 * rLen < max_size_t} ->
    sstLen:size_t{v sstLen == stLen} -> st:lbignum stLen -> Stack unit
    (requires (fun h -> live h b /\ live h st /\ disjoint st b))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

#reset-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0"

let mod_exp_mont #rLen #stLen pow2_i iLen bBits b exp_r rrLen sstLen st =
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
    
    let stKLen = add #SIZE (mul #SIZE (size 2) rrLen) (mul #SIZE (size 4) pow2_i) in
    let st_kara = Buffer.sub #uint64 #stLen #(v stKLen) st (mul #SIZE (size 9) rrLen) stKLen in

    let stLLen = add #SIZE stKLen (mul #SIZE (size 9) rrLen) in
    let st_t = Buffer.sub #uint64 #stLen #(5 * rLen) st stLLen (mul #SIZE (size 5) rrLen) in
    let st_f = Buffer.sub #uint64 #stLen #(3 * rLen) st stLLen (mul #SIZE (size 3) rrLen) in
    to_mont pow2_i iLen exp_r rrLen st_mont st_t st_kara r2 a1 aM;
    to_mont pow2_i iLen exp_r rrLen st_mont st_t st_kara r2 acc accM;

    mod_exp_ pow2_i iLen exp_r rrLen st_mont st_exp st_f st_kara bBits bLen b (size 0);
    from_mont pow2_i iLen exp_r rrLen st_mont st_f st_kara accM res1
    
// res = a ^^ b mod n
val mod_exp:
    #nLen:size_nat ->
    pow2_i:size_t -> iLen:size_t ->
    modBits:size_t{0 < v modBits /\ 2 * v modBits + 4 < max_size_t} ->
    nnLen:size_t{let rLen = v (bits_to_bn (add #SIZE modBits (size 2))) in
                 v nnLen == nLen /\ 0 < nLen /\ nLen = v (bits_to_bn modBits) /\
		 9 * rLen < max_size_t /\ 2 * rLen + 4 * v pow2_i < max_size_t /\
		 rLen < v pow2_i} ->
    n:lbignum nLen -> a:lbignum nLen ->
    bBits:size_t{0 < v bBits} -> b:lbignum (v (bits_to_bn bBits)) ->
    res:lbignum nLen -> Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
    
#reset-options "--lax"

let mod_exp #nLen pow2_i iLen modBits nnLen n a bBits b res =
    push_frame();
    let exp_r = add #SIZE modBits (size 2) in
    let rBits = add #SIZE modBits (size 3) in
    let rLen = bits_to_bn rBits in
    assert (v rLen = (v rBits - 1) / 64 + 1);
    assert (nLen = (v modBits - 1) / 64 + 1);
    assert (9 * v rLen < max_size_t);
    assert (nLen <= v rLen);
    assert (v exp_r / 64 < v rLen);
    assert (v modBits / 64 < v rLen);

    let stLenKara = add #SIZE (mul #SIZE (size 2) rLen) (mul #SIZE (size 4) pow2_i) in
    let stLen' = mul #SIZE (size 14) rLen in
    let stLen = add #SIZE stLenKara stLen' in
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
      shift_euclidean_mod_inv rLen modBits n1 rBits r nInv; // n * nInv = 1 (mod r)
      mod_exp_mont #(v rLen) #(v stLen) pow2_i iLen bBits b exp_r rLen stLen st;
      
      copy nnLen res1_ res
    );
    pop_frame()
