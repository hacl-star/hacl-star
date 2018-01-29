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

val degree_:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen ->
    i:size_t{v i / 64 < aLen} -> Stack size_t
    (requires (fun h -> live h a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
let rec degree_ #aLen aaLen a i =
    if i =. size 0 then size 0
    else begin
       if (bn_is_bit_set aaLen a i) then i
       else degree_ #aLen aaLen a (size_decr i)
    end

val degree:
    #aLen:size_nat ->
    aaLen:size_t{v aaLen == aLen} ->
    a:lbignum aLen ->
    aBits:size_t{v aBits / 64 < aLen} -> Stack size_t
    (requires (fun h -> live h a))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ h0 == h1))
let degree #aLen aaLen a aBits = degree_ #aLen aaLen a aBits
    
val shift_euclidean_mod_inv_f:
    #rLen:size_nat ->
    rrLen:size_t{v rrLen == rLen} ->
    m:lbignum rLen -> tmp:lbignum rLen ->
    f:size_t -> i:size_t -> tmp1:lbignum (rLen + 1)-> Stack unit
    (requires (fun h -> live h m /\ live h tmp))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 tmp h0 h1))
    
let rec shift_euclidean_mod_inv_f #rLen rrLen m tmp f i tmp1 =
    if (i <. f) then begin
       //bn_add rrLen tmp rrLen tmp tmp; // tmp = tmp + tmp
       //FIXME: bn_add 
       fill (add #SIZE rrLen (size 1)) tmp1 (u64 0);
       bn_mul_u64 rrLen tmp (u64 2) tmp1;
       let tmp1_ = Buffer.sub #uint64 #(rLen + 1) #rLen tmp1 (size 0) rrLen in
       copy rrLen tmp1_ tmp;
       
       (if (bn_is_less rrLen m tmp) then // m < tmp 
           bn_sub rrLen tmp rrLen m tmp); //tmp = tmp - m
       shift_euclidean_mod_inv_f #rLen rrLen m tmp f (size_incr i) tmp1
    end
    
val shift_euclidean_mod_inv_:
    #rLen:size_nat ->
    rrLen:size_t{v rrLen == rLen} ->
    uBits:size_t{v uBits / 64 < rLen} -> ub:lbignum rLen ->
    vBits:size_t{v vBits / 64 < rLen} -> vb:lbignum rLen ->
    r:lbignum rLen -> s:lbignum rLen ->
    m:lbignum rLen -> st_inv:lbignum (3 * rLen + 1) -> res:lbignum rLen -> Stack unit
    (requires (fun h -> live h ub /\ live h vb /\ live h s /\ live h r /\ live h m /\ live h st_inv /\ live h res))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1))
    
let rec shift_euclidean_mod_inv_ #rLen rrLen uBits ub vBits vb r s m st_inv res =
    let stLen = add (mul #SIZE rrLen (size 3)) (size 1) in
    fill stLen st_inv (u64 0);
    let v_shift_f = Buffer.sub #uint64 #(v stLen) #rLen st_inv (size 0) rrLen in
    let tmp = Buffer.sub #uint64 #(v stLen) #rLen st_inv rrLen rrLen in
    let tmp1 = Buffer.sub #uint64 #(v stLen) #(rLen + 1) st_inv (add #SIZE rrLen rrLen) (add #SIZE rrLen (size 1)) in

    let du = degree rrLen ub uBits in
    let dv = degree rrLen vb vBits in
    
    if (dv >. size 0) then begin
       let f = sub #SIZE du dv in
       bn_lshift rrLen vb f v_shift_f; //v_shift_f = v << f
       let f = 
	  if (bn_is_less rrLen ub v_shift_f) then begin // u < v_shift_f
             let f = sub #SIZE f (size 1) in
             fill rrLen v_shift_f (u64 0);
             bn_lshift rrLen vb f v_shift_f; f end
	  else f in
       bn_sub rrLen ub rrLen v_shift_f ub; // u = u - v_shift_f
       copy rrLen s tmp;
       shift_euclidean_mod_inv_f #rLen rrLen m tmp f (size 0) tmp1;
       (if (bn_is_less rrLen r tmp) then begin // r < tmp
            bn_add rrLen r rrLen m r; //r = r + m
            bn_sub rrLen r rrLen tmp r end
        else bn_sub rrLen r rrLen tmp r);
	 
       let du = degree rrLen ub uBits in
       if (bn_is_less rrLen ub vb) then begin
          //swap(u,v); swap(r,s)
          shift_euclidean_mod_inv_ #rLen rrLen dv vb du ub s r m st_inv res end
       else shift_euclidean_mod_inv_ #rLen rrLen du ub dv vb r s m st_inv res end
    else copy rrLen s res
      
val shift_euclidean_mod_inv:
    #rLen:size_nat ->
    rrLen:size_t{v rrLen == rLen} ->
    aBits:size_t{v aBits / 64 < rLen} -> a:lbignum rLen ->
    mBits:size_t{v mBits / 64 < rLen} -> m:lbignum rLen -> 
    res:lbignum rLen -> Stack unit
    (requires (fun h -> live h a /\ live h m))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1))
    
let shift_euclidean_mod_inv #rLen rrLen aBits a mBits m res =
    let stLen = add #SIZE (mul #SIZE (size 7) rrLen) (size 1) in
    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem a; BufItem m] [BufItem res]
    (fun h0 _ h1 -> True)
    (fun st ->
      let ub = Buffer.sub #uint64 #(v stLen) #rLen st (size 0) rrLen in
      let vb = Buffer.sub #uint64 #(v stLen) #rLen st rrLen rrLen in
      let r = Buffer.sub #uint64 #(v stLen) #rLen st (add #SIZE rrLen rrLen) rrLen in
      let s = Buffer.sub #uint64 #(v stLen) #rLen st (mul #SIZE (size 3) rrLen) rrLen in
      let st_inv = Buffer.sub #uint64 #(v stLen) #(3 * rLen + 1) st (mul #SIZE (size 4) rrLen) (add #SIZE (mul #SIZE rrLen (size 3)) (size 1)) in

      copy rrLen m ub;
      copy rrLen a vb;
      s.(size 0) <- u64 1;
      shift_euclidean_mod_inv_ #rLen rrLen mBits ub aBits vb r s m st_inv res
      //copy rrLen s res
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
