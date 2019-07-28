module Hacl.Impl.Bignum.Exponentiation

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Math.Algebra

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Modular
open Hacl.Impl.Bignum.Montgomery
open Hacl.Impl.Bignum.Multiplication
open Hacl.Impl.Bignum.Shift
open Hacl.Spec.Bignum

module ST = FStar.HyperStack.ST

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val mul_mod_mont:
     nLen:bn_len
  -> rLen:bn_len{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> st_kara:lbignum (nLen +. nLen +. 4ul *. pow2_i)
  -> aM:lbignum nLen
  -> bM:lbignum nLen
  -> resM:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h aM /\ live h bM /\ live h resM /\ live h n /\ live h st_kara /\
      disjoint st_kara aM /\ disjoint st_kara bM /\ disjoint st_kara n /\ disjoint resM st_kara)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc resM) (loc st_kara)) h0 h1)
[@"c_inline"]
let mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM bM resM =
  let cLen = nLen +. nLen in
  let stLen = cLen +. 4ul *. pow2_i in
  let c = sub st_kara 0ul cLen in
  let tmp = sub st_kara cLen (nLen +. rLen) in
  karatsuba pow2_i nLen aM bM st_kara; // c = aM * bM
  mont_reduction nLen rLen n nInv_u64 c tmp resM // resM = c % n

val mod_exp_:
     nLen:bn_len
  -> rLen:bn_len{v nLen < v rLen /\ v nLen + v rLen < max_size_t}
  -> pow2_i:size_t{v nLen + v nLen + 4 * v pow2_i < max_size_t /\ v nLen <= v pow2_i /\ v rLen < 2 * v pow2_i}
  -> n:lbignum nLen
  -> nInv_u64:uint64
  -> st_kara:lbignum (nLen +. nLen +. 4ul *. pow2_i)
  -> st_exp:lbignum (nLen +. nLen)
  -> bBits:size_t{v bBits > 0}
  -> bLen:size_t{v bLen = v (blocks bBits 64ul) /\ (v bBits - 1) / 64 < v bLen}
  -> b:lbignum bLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h b /\ live h st_kara /\ live h st_exp /\
      disjoint st_exp st_kara /\ disjoint st_kara n /\ disjoint st_kara st_exp)
    (ensures  fun h0 _ h1 -> modifies (loc_union (loc st_exp) (loc st_kara)) h0 h1)
[@"c_inline"]
let mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b =
  let aM = sub st_exp 0ul nLen in
  let accM = sub st_exp nLen nLen in

  let h0 = ST.get () in
  let inv h1 i = modifies (loc_union (loc st_exp) (loc st_kara)) h0 h1 in
  Lib.Loops.for 0ul bBits inv
  (fun i ->
    (if (bn_is_bit_set b i) then
      mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM accM accM); // acc = (acc * a) % n
    mul_mod_mont nLen rLen pow2_i n nInv_u64 st_kara aM aM aM // a = (a * a) % n
  )

//128 * (v nLen + 1) < max_size_t
// res = a ^^ b mod n
val mod_exp:
     pow2_i:size_t{v pow2_i > 0}
  -> modBits:size_t{v modBits > 0}
  -> nLen:bn_len{
       v nLen = v (blocks modBits 64ul) /\
       5 * v nLen + 4 * v pow2_i < max_size_t /\
       v nLen <= v pow2_i /\
       v nLen + 1 < 2 * v pow2_i}
  -> n:lbignum nLen
  -> r2:lbignum nLen
  -> a:lbignum nLen
  -> bBits:size_t{v bBits > 0}
  -> b:lbignum (blocks bBits 64ul)
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h -> live h n /\ live h a /\ live h b /\ live h res /\ live h r2 /\ as_snat h n > 1)
    (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1)
[@"c_inline"]
let mod_exp pow2_i modBits nLen n r2 a bBits b res =
  push_frame ();
  let rLen = nLen +. 1ul in
  let exp_r = 64ul *. rLen in
  let exp2 = exp_r +. exp_r in

  let bLen = blocks bBits 64ul in

  let karaLen = nLen +! nLen +! 4ul *! pow2_i in
  let stLen = nLen +! nLen +! nLen +! karaLen in
  let st = create stLen (u64 0) in

  admit();

  let acc  = sub st 0ul nLen in
  let aM   = sub st nLen nLen in
  let accM = sub st (nLen +. nLen) nLen in

  let st_exp  = sub st nLen (nLen +. nLen) in
  let st_kara = sub st (nLen +. nLen +. nLen) karaLen in
  //let tmp     = sub #_ #(v stLen) #(v nLen + v rLen) st (nLen +. nLen +. nLen) (nLen +. rLen) in
  let tmp     = sub st (nLen +. nLen +. nLen) (nLen +. rLen) in

  acc.(0ul) <- u64 1;
  let n0 = n.(0ul) in
  let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))
  to_mont nLen rLen pow2_i n nInv_u64 r2 a st_kara aM;
  to_mont nLen rLen pow2_i n nInv_u64 r2 acc st_kara accM;
  mod_exp_ nLen rLen pow2_i n nInv_u64 st_kara st_exp bBits bLen b;
  from_mont nLen rLen pow2_i n nInv_u64 accM tmp res;
  pop_frame ()

#reset-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

// TODO doesn't have bounds validation, is
// used within bn_exp, which does have them
val naive_exp_loop:
     #aLen:bn_len_strict{(v aLen + v aLen) * 64 < max_size_t}
  -> #expLen:bn_len_strict
  -> a:lbignum aLen
  -> b:lbignum expLen
  -> res:lbignum aLen
  -> Stack unit
    (requires fun h ->
        disjoint a b /\ disjoint a res /\
        live h a /\ live h b /\ live h res)
    (ensures fun h0 _ h1 ->
        live h1 res /\ live h1 a /\ live h1 b /\
        modifies2 res b h0 h1)
let rec naive_exp_loop #aLen #expLen a b res =
  push_frame ();
  let tmp = create expLen (uint 0) in
  let tmp' = create aLen (uint 0) in
  assert_norm (issnat 0);
  assert_norm (nat_bytes_num 0 =. 1ul);
  let zero:lbignum 1ul = nat_to_bignum_exact 0 in
  let isnull = bn_is_equal b zero in
  if not isnull then begin
     let odd = eq_u64 (b.(0ul) &. uint 1) (uint 1) in
     bn_rshift1 b tmp; copy b tmp;
     naive_exp_loop #aLen a b res;
     let h = FStar.HyperStack.ST.get () in
     assume (issnat (as_snat h res * as_snat h res) /\
             v (nat_bytes_num (as_snat h res * as_snat h res)) <= v aLen);
     bn_mul_fitting res res tmp';
     copy res tmp';
     if odd then begin
       let h = FStar.HyperStack.ST.get () in
       assume (issnat (as_snat h res * as_snat h a) /\
               v (nat_bytes_num (as_snat h res * as_snat h a)) <= v aLen);
       bn_mul_fitting res a tmp';
       copy res tmp'
     end
  end;
  pop_frame ()

val bn_exp:
     #aLen:bn_len_strict{v aLen * 128 < max_size_t}
  -> #expLen:bn_len_strict
  -> a:lbignum aLen
  -> b:lbignum expLen
  -> res:lbignum aLen
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h res /\
      disjoint a res /\ disjoint b res /\
      nat_fits (exp (as_snat h a) (as_snat h b)) aLen)
    (ensures  fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      live h1 a /\ live h1 b /\ live h1 res /\
      as_snat h1 res = (exp (as_snat h0 a) (as_snat h0 b)))
let bn_exp #aLen #expLen a b res =
  let h0 = FStar.HyperStack.ST.get () in

  push_frame ();

  memset res (uint 0) aLen;
  res.(0ul) <- uint 1;
  let tmp_b = create expLen (uint 0) in
  copy tmp_b b;
  naive_exp_loop a tmp_b res;

  pop_frame ();

  let h1 = FStar.HyperStack.ST.get () in
  assume (as_snat h1 res = exp (as_snat h0 a) (as_snat h0 b))
