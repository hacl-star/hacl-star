module Hacl.Spec.Montgomery

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

open Hacl.Spec.Addition
open Hacl.Spec.Comparison
open Hacl.Spec.Multiplication
open Hacl.Spec.Shift

val bn_pow2_mod_n_:
  rLen:size_nat{0 < rLen} -> a:lseqbn rLen ->
  i:size_nat -> p:size_nat ->
  res:lseqbn rLen -> Tot (lseqbn rLen)
  (decreases (p - i))
  
let rec bn_pow2_mod_n_ rLen a i p res =
  if (i < p) then begin
    let res = bn_lshift1 rLen res res in
    let res =
      if not (bn_is_less rLen res rLen a)
      then bn_sub rLen res rLen a res
      else res in
    bn_pow2_mod_n_ rLen a (i + 1) p res end
  else res

// res = 2 ^^ p % a
val bn_pow2_mod_n:
  aBits:size_nat -> rLen:size_nat{0 < rLen /\ aBits / 64 < rLen} ->
  a:lseqbn rLen -> p:size_nat{aBits < p} ->
  res:lseqbn rLen -> Tot (lseqbn rLen)

let bn_pow2_mod_n aBits rLen a p res =
  let res = bn_set_bit rLen res aBits in
  let res = bn_sub rLen res rLen a res in // res = res - a
  bn_pow2_mod_n_ rLen a aBits p res

val degree_:
  aLen:size_nat -> a:lseqbn aLen ->
  i:size_nat{i / 64 < aLen} -> Tot size_nat
let rec degree_ aLen a i =
  if i = 0 then 0
  else begin
    if (bn_is_bit_set aLen a (i - 1)) then i
    else degree_ aLen a (i - 1)
  end

val degree:
  aLen:size_nat -> a:lseqbn aLen ->
  aBits:size_nat{aBits / 64 < aLen} -> Tot size_nat
let degree aLen a aBits = degree_ aLen a aBits

val shift_euclidean_mod_inv_f:
  rLen:size_nat{rLen > 0} ->
  m:lseqbn rLen -> tmp:lseqbn rLen ->
  f:size_nat -> i:size_nat -> Tot (lseqbn rLen)
  (decreases (f - i))
  
let rec shift_euclidean_mod_inv_f rLen m tmp f i =
  if (i < f) then begin
    let tmp = bn_add rLen tmp rLen tmp tmp in // tmp = tmp + tmp
    let tmp =
      if (bn_is_less rLen m rLen tmp)
      then bn_sub rLen tmp rLen m tmp // tmp = tmp - m
      else tmp in
    shift_euclidean_mod_inv_f rLen m tmp f (i + 1) end
  else tmp

val shift_euclidean_mod_inv_:
  rLen:size_nat{rLen + rLen < max_size_t} ->
  du:size_nat{du / 64 < rLen} -> ub:lseqbn rLen ->
  dv:size_nat{dv / 64 < rLen /\ dv <= du} -> vb:lseqbn rLen ->
  r:lseqbn rLen -> s:lseqbn rLen ->
  a:lseqbn rLen -> m:lseqbn rLen ->
  st_inv:lseqbn (rLen + rLen) -> res:lseqbn rLen -> Tot (lseqbn rLen)
  (decreases (du + dv))

#reset-options "--lax"
let rec shift_euclidean_mod_inv_ rLen du ub dv vb r s a m st_inv res =
  let stLen = rLen + rLen in
  let v_shift_f = sub st_inv 0 rLen in
  let tmp = sub st_inv rLen rLen in

  if (dv > 1) then begin
    let f = du - dv in
    let v_shift_f = bn_lshift rLen vb f v_shift_f in // v_shift_f = v << f
    let f =
      if (bn_is_less rLen ub rLen v_shift_f)
      then begin assume (f > 0); f - 1 end
      else f in
    let v_shift_f = bn_lshift rLen vb f v_shift_f in // v_shift_f = v << f
    let ub = bn_sub rLen ub rLen v_shift_f ub in // u = u - v_shift_f
       
    let tmp = update_sub tmp 0 rLen s in
    let tmp = shift_euclidean_mod_inv_f rLen m tmp f 0 in
    let r =
      if (bn_is_less rLen r rLen tmp)
      then begin // r < tmp
	let r = bn_add rLen r rLen m r in // r = r + m
        bn_sub rLen r rLen tmp r end
      else bn_sub rLen r rLen tmp r in

    let du' = degree rLen ub du in
    assume (du' < du);
    if (bn_is_less rLen ub rLen vb) // ub < vb
    then begin
      assume (du' < dv);
      shift_euclidean_mod_inv_ rLen dv vb du' ub s r a m st_inv res end
    else begin
      assume (dv <= du');
      shift_euclidean_mod_inv_ rLen du' ub dv vb r s a m st_inv res end
    end
  else begin
    if (dv = 0) then
      let res' = create rLen (u64 0) in
      update_sub res 0 rLen res'
    else update_sub res 0 rLen s
  end

#reset-options "--z3rlimit 30"

val shift_euclidean_mod_inv:
  rLen:size_nat{rLen > 0 /\ 6 * rLen < max_size_t} ->
  aBits:size_nat{aBits / 64 < rLen} -> a:lseqbn rLen ->
  mBits:size_nat{mBits / 64 < rLen /\ aBits <= mBits} -> m:lseqbn rLen ->
  res:lseqbn rLen -> Tot (lseqbn rLen)
  
let shift_euclidean_mod_inv rLen aBits a mBits m res =
  let stLen:size_nat = 6 * rLen in
  let st = create stLen (u64 0) in
    
  let ub = sub st 0 rLen in
  let vb = sub st rLen rLen in
  let r = sub st (2 * rLen) rLen in
  let s = sub st (3 * rLen) rLen in
  let st_inv = sub st (4 * rLen) (2 * rLen) in

  let ub = update_sub ub 0 rLen m in
  let vb = update_sub vb 0 rLen a in
  let s = s.[0] <- u64 1 in
  shift_euclidean_mod_inv_ rLen mBits ub aBits vb r s a m st_inv res

val mont_reduction:
  pow2_i:size_nat{4 * pow2_i < max_size_t} -> iLen:size_nat{iLen < pow2_i / 2} -> exp_r:size_nat{0 < exp_r} ->
  rLen:size_nat{0 < rLen /\ 6 * rLen < max_size_t /\ iLen + rLen = pow2_i /\ rLen = exp_r / 64 + 1} ->
  st_mont:lseqbn (3 * rLen) -> st:lseqbn (3 * rLen) -> st_kara:lseqbn (4 * pow2_i) ->
  cLen:size_nat{cLen = rLen + rLen} -> c:lseqbn cLen ->
  res:lseqbn rLen -> Tot (lseqbn rLen)
//merge st and st_kara
let mont_reduction pow2_i iLen exp_r rLen st_mont st st_kara cLen c res =
  let r2Len:size_nat = rLen + rLen in
  let stLen:size_nat = 3 * rLen in
  
  let r = sub st_mont 0 rLen in
  let n = sub st_mont rLen rLen in
  let nInv = sub st_mont r2Len rLen in
    
  let tmp1 = sub st 0 r2Len in
  let m = sub st r2Len rLen in
      
  let c1 = sub c 0 rLen in // c1 = c % r
  let tmp1 = karatsuba pow2_i iLen rLen c1 nInv st_kara tmp1 in // tmp1 = c1 * nInv
  
  let m = bn_mod_pow2_n r2Len tmp1 exp_r rLen m in // m = tmp1 % r
  let m = bn_sub rLen r rLen m m in // m = r - m
  let tmp1 = karatsuba pow2_i iLen rLen m n st_kara tmp1 in // tmp1 = m * n
  let tmp1 = bn_add r2Len tmp1 cLen c tmp1 in // tmp1 = c + tmp1
  let tmp1 = bn_rshift r2Len tmp1 exp_r tmp1 in // tmp1 = tmp1 / r

  let tmp1' = sub tmp1 0 rLen in
  update_sub res 0 rLen tmp1'

val to_mont:
  pow2_i:size_nat{4 * pow2_i < max_size_t} -> iLen:size_nat{iLen < pow2_i / 2} -> exp_r:size_nat{0 < exp_r} ->
  rLen:size_nat{0 < rLen /\ 6 * rLen < max_size_t /\ iLen + rLen = pow2_i /\ rLen = exp_r / 64 + 1} ->
  st_mont:lseqbn (3 * rLen) -> st:lseqbn (5 * rLen) -> st_kara:lseqbn (4 * pow2_i) ->
  r2:lseqbn rLen -> a:lseqbn rLen -> aM:lseqbn rLen -> Tot (lseqbn rLen)
//merge st and st_kara
let to_mont pow2_i iLen exp_r rLen st_mont st st_kara r2 a aM =
  let cLen:size_nat = rLen + rLen in
  let stLen:size_nat = 3 * rLen in
    
  let c = sub st 0 cLen in
  let st = sub st cLen stLen in
    
  let c = karatsuba pow2_i iLen rLen a r2 st_kara c in // c = a * r2 
  mont_reduction pow2_i iLen exp_r rLen st_mont st st_kara cLen c aM // aM = c % n
    
    
val from_mont:
  pow2_i:size_nat{4 * pow2_i < max_size_t} -> iLen:size_nat{iLen < pow2_i / 2} -> exp_r:size_nat{0 < exp_r} ->
  rLen:size_nat{0 < rLen /\ 6 * rLen < max_size_t /\ iLen + rLen = pow2_i /\ rLen = exp_r / 64 + 1} ->
  st_mont:lseqbn (3 * rLen) -> st:lseqbn (3 * rLen) -> st_kara:lseqbn (4 * pow2_i) ->
  aM:lseqbn rLen -> a:lseqbn rLen -> Tot (lseqbn rLen)
//merge st and st_kara
let from_mont pow2_i iLen exp_r rLen st_mont st st_kara aM a =
  let r2Len:size_nat = rLen + rLen in
  let stLen:size_nat = 3 * rLen in

  let r = sub st_mont 0 rLen in
  let n = sub st_mont rLen rLen in
  let nInv = sub st_mont r2Len rLen in

  let tmp = sub st 0 r2Len in
  let m = sub st r2Len rLen in
  
  let tmp = karatsuba pow2_i iLen rLen aM nInv st_kara tmp in // tmp = aM * nInv
  let m = bn_mod_pow2_n r2Len tmp exp_r rLen m in // m = tmp % r
  let m = bn_sub rLen r rLen m m in // m = r - m
  let tmp = karatsuba pow2_i iLen rLen m n st_kara tmp in // tmp = m * n
  let tmp = bn_add r2Len tmp rLen aM tmp in //tmp = aM + tmp
  let tmp = bn_rshift r2Len tmp exp_r tmp in //tmp = tmp / r
      
  let tmp' = sub tmp 0 rLen in
  update_sub a 0 rLen tmp'
