module Hacl.Impl.Exponentiation

open FStar.HyperStack.All
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes
open FStar.Mul

open Hacl.Impl.Lib
open Hacl.Impl.Montgomery
open Hacl.Impl.Multiplication

module Buffer = Spec.Lib.IntBuf

val mul_mod_mont:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 -> st_kara:lbignum (2 * nLen + 4 * v pow2_i) ->
  aM:lbignum nLen -> bM:lbignum nLen -> resM:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h aM /\ live h bM /\ live h resM /\ live h n /\ live h st_kara /\
                      disjoint st_kara aM /\ disjoint st_kara bM /\ disjoint st_kara n))
    (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 resM st_kara h0 h1))
  [@"c_inline"]
let mul_mod_mont #nLen #rLen nnLen rrLen pow2_i n nInv_u64 st_kara aM bM resM =
  let cLen = add #SIZE nnLen nnLen in
  let stLen = add #SIZE cLen (mul #SIZE (size 4) pow2_i) in
  let c = Buffer.sub #uint64 #(v stLen) #(v cLen) st_kara (size 0) cLen in
  let tmp = Buffer.sub #uint64 #(v stLen) #(nLen + rLen) st_kara cLen (add #SIZE nnLen rrLen) in  
  
  karatsuba pow2_i nnLen aM bM st_kara; // c = aM * bM
  assume (disjoint tmp n);
  let h0 = FStar.HyperStack.ST.get() in
  mont_reduction nnLen rrLen n nInv_u64 c tmp resM; // resM = c % n
  let h1 = FStar.HyperStack.ST.get() in
  assume (modifies2 resM st_kara h0 h1)
  
val mod_exp_:
  #nLen:size_nat -> #rLen:size_nat{nLen < rLen} ->
  nnLen:size_t{v nnLen == nLen} ->
  rrLen:size_t{v rrLen == rLen /\ nLen + rLen < max_size_t} ->
  pow2_i:size_t{2 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ rLen < 2 * v pow2_i} ->
  n:lbignum nLen -> nInv_u64:uint64 -> st_kara:lbignum (2 * nLen + 4 * v pow2_i) -> st_exp:lbignum (2 * nLen) ->
  bBits:size_t{0 < v bBits} -> bLen:size_t{v bLen = v (bits_to_bn bBits) /\ v bBits / 64 < v bLen} -> b:lbignum (v bLen) ->
  i:size_t{v i <= v bBits} ->
  Stack unit
    (requires (fun h -> live h n /\ live h b /\ live h st_kara /\ live h st_exp /\
                      disjoint st_exp st_kara /\ disjoint st_kara n))    
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies2 st_exp st_kara h0 h1))
  [@"c_inline"]
let rec mod_exp_ #nLen #rLen nnLen rrLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b i =
  let aM = Buffer.sub #uint64 #(nLen + nLen) #nLen st_exp (size 0) nnLen in
  let accM = Buffer.sub #uint64 #(nLen + nLen) #nLen st_exp nnLen nnLen in
  disjoint_sub_lemma1 st_exp st_kara (size 0) nnLen; // disjoint st_kara aM
  disjoint_sub_lemma1 st_exp st_kara nnLen nnLen; // disjoint st_kara accM
  (if (i <. bBits) then begin
    (if (bn_is_bit_set bLen b i) then mul_mod_mont #nLen #rLen nnLen rrLen pow2_i n nInv_u64 st_kara aM accM accM); // acc = (acc * a) % n
    mul_mod_mont #nLen #rLen nnLen rrLen pow2_i n nInv_u64 st_kara aM aM aM; // a = (a * a) % n
    mod_exp_ #nLen #rLen nnLen rrLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b (size_incr i)
  end); admit()
  
// res = a ^^ b mod n
val mod_exp:
  #nLen:size_nat ->
  pow2_i:size_t{6 * nLen + 4 * v pow2_i < max_size_t /\ nLen <= v pow2_i /\ nLen + 1 < 2 * v pow2_i} ->
  modBits:size_t{0 < v modBits} -> nnLen:size_t{v nnLen == nLen /\ nLen = v (bits_to_bn modBits)} ->
  n:lbignum nLen -> a:lbignum nLen ->
  bBits:size_t{0 < v bBits} -> b:lbignum (v (bits_to_bn bBits)) -> res:lbignum nLen ->
  Stack unit
    (requires (fun h -> live h n /\ live h a /\ live h b /\ live h res))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 res h0 h1))
  #reset-options "--z3rlimit 150 --max_fuel 0"
  [@"c_inline"]    
let mod_exp #nLen pow2_i modBits nnLen n a bBits b res =
  //push_frame();
  let rrLen = size_incr nnLen in
  assume (128 * v rrLen < max_size_t);
  let exp_r = mul #SIZE (size 64) rrLen in
  let exp2 = add #SIZE exp_r exp_r in

  let bLen = bits_to_bn bBits in
  assume (v bBits / 64 < v bLen);

  let karaLen = add #SIZE (add #SIZE nnLen nnLen) (mul #SIZE (size 4) pow2_i) in
  let stLen = add #SIZE (mul #SIZE (size 4) nnLen) karaLen in

  alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem n; BufItem a; BufItem b] [BufItem res]
  (fun h0 _ h1 -> True)
  (fun st ->
    let r2 = Buffer.sub #uint64 #(v stLen) #nLen st (size 0) nnLen in
    let acc = Buffer.sub #uint64 #(v stLen) #nLen st nnLen nnLen in
    let aM = Buffer.sub #uint64 #(v stLen) #nLen st (mul #SIZE (size 2) nnLen) nnLen in
    let accM = Buffer.sub #uint64 #(v stLen) #nLen st (mul #SIZE (size 3) nnLen) nnLen in
    
    let st_exp = Buffer.sub #uint64 #(v stLen) #(nLen + nLen) st (mul #SIZE (size 2) nnLen) (mul #SIZE (size 2) nnLen) in
    let st_kara = Buffer.sub #uint64 #(v stLen) #(v karaLen) st (mul #SIZE (size 4) nnLen) karaLen in
    let tmp = Buffer.sub #uint64 #(v stLen) #(nLen + v rrLen) st (mul #SIZE (size 4) nnLen) (add #SIZE nnLen rrLen) in
    
    acc.(size 0) <- u64 1;
    assume (v modBits / 64 < v nnLen);
    assume (disjoint r2 n);
    bn_pow2_mod_n nnLen modBits n exp2 r2; // r2 = r * r % n
    let n0 = n.(size 0) in
    let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))
    assume (disjoint st_kara a /\ disjoint st_kara r2 /\ disjoint st_kara n);
    to_mont #nLen #(v rrLen) nnLen rrLen pow2_i n nInv_u64 r2 a st_kara aM;
    to_mont #nLen #(v rrLen) nnLen rrLen pow2_i n nInv_u64 r2 acc st_kara accM;
    mod_exp_ #nLen #(v rrLen) nnLen rrLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b (size 0);
    assume (disjoint tmp n);
    from_mont #nLen #(v rrLen) nnLen rrLen pow2_i n nInv_u64 accM tmp res; admit()
    )
    //pop_frame()
