module Hacl.Spec.Exponentiation

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

open Hacl.Spec.Montgomery
open Hacl.Spec.Multiplication

val mul_mod_mont:
  rLen:size_nat{0 < rLen} ->
  pow2_i:size_nat{2 * rLen + 4 * pow2_i < max_size_t /\ rLen < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + rLen = pow2_i} ->
  n:lseqbn rLen -> nInv_u64:uint64 -> st_kara:lseqbn (2 * rLen + 4 * pow2_i) ->
  aM:lseqbn rLen -> bM:lseqbn rLen -> resM:lseqbn rLen -> Tot (lseqbn rLen)
let mul_mod_mont rLen pow2_i iLen n nInv_u64 st_kara aM bM resM =
  let cLen = rLen + rLen in
  let stLen = cLen + 4 * pow2_i in
  let c = sub st_kara 0 cLen in
  let c = karatsuba pow2_i iLen rLen aM bM st_kara in // c = aM * bM
  mont_reduction rLen n nInv_u64 c c resM // resM = c % n 

val mod_exp_:
  rLen:size_nat{0 < rLen} ->
  pow2_i:size_nat{2 * rLen + 4 * pow2_i < max_size_t /\ rLen < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + rLen = pow2_i} ->
  n:lseqbn rLen -> nInv_u64:uint64 -> st_kara:lseqbn (2 * rLen + 4 * pow2_i) -> st_exp:lseqbn (2 * rLen) ->
  bBits:size_nat{0 < bBits} -> bLen:size_nat{bLen = (bits_to_bn bBits) /\ bBits / 64 < bLen} -> b:lseqbn bLen ->
  i:size_nat{i <= bBits} -> Tot (lseqbn rLen)
  (decreases (bBits - i))
let rec mod_exp_ rLen pow2_i iLen n nInv_u64 st_kara st_exp bBits bLen b i =
  let aM = sub st_exp 0 rLen in
  let accM = sub st_exp rLen rLen in
  if (i < bBits) then begin
    let accM = 
      if (bn_is_bit_set bLen b i) 
      then mul_mod_mont rLen pow2_i iLen n nInv_u64 st_kara aM accM accM
      else accM in // acc = (acc * a) % n
    let aM = mul_mod_mont rLen pow2_i iLen n nInv_u64 st_kara aM aM aM in // a = (a * a) % n
    let st_exp = update_sub st_exp 0 rLen aM in
    let st_exp = update_sub st_exp rLen rLen accM in
    mod_exp_ rLen pow2_i iLen n nInv_u64 st_kara st_exp bBits bLen b (i + 1)
  end else accM

val mod_exp_mont:
  rLen:size_nat{0 < rLen} ->
  pow2_i:size_nat{9 * rLen + 4 * pow2_i < max_size_t /\ rLen < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + rLen = pow2_i} ->
  bBits:size_nat{0 < bBits} -> b:lseqbn (bits_to_bn bBits) ->
  nInv_u64:uint64 -> st:lseqbn (9 * rLen + 4 * pow2_i) -> Tot (lseqbn rLen)
  #reset-options "--z3rlimit 50 --max_fuel 0"
let mod_exp_mont rLen pow2_i iLen bBits b nInv_u64 st =
  let bLen = bits_to_bn bBits in
  //assert ((v bBits - 1) / 64 < v bLen);
  assume (bBits / 64 < bLen);
  let karaLen = 2 * rLen + 4 * pow2_i in
  let stLen = 7 * rLen + karaLen in
  
  let n1 = sub st 0 rLen in
  let r2 = sub st rLen rLen in
  let a1 = sub st (2 * rLen) rLen in
  let acc = sub st (3 * rLen) rLen in
  
  let aM = sub st (4 * rLen) rLen in
  let accM = sub st (5 * rLen) rLen in
  let res1 = sub st (6 * rLen) rLen in
  let st_exp = sub st (4 * rLen) (2 * rLen) in
  let st_kara = sub st (7 * rLen) karaLen in
  let st' = sub st (7 * rLen) (2 * rLen) in
  
  let aM = to_mont rLen pow2_i iLen n1 nInv_u64 r2 a1 st_kara aM in
  let accM = to_mont rLen pow2_i iLen n1 nInv_u64 r2 acc st_kara accM in
  let st_exp = update_sub st_exp 0 rLen aM in
  let st_exp = update_sub st_exp rLen rLen accM in
  let accM = mod_exp_ rLen pow2_i iLen n1 nInv_u64 st_kara st_exp bBits bLen b 0 in
  from_mont rLen pow2_i iLen n1 nInv_u64 accM st' res1

val mod_exp:
  nLen:size_nat ->
  pow2_i:size_nat{9 * (1 + nLen) + 4 * pow2_i < max_size_t /\ (1 + nLen) < pow2_i} ->
  iLen:size_nat{iLen < pow2_i / 2 /\ iLen + (1 + nLen) = pow2_i} ->
  modBits:size_nat{0 < modBits /\ nLen = bits_to_bn modBits} ->
  n:lseqbn nLen -> a:lseqbn nLen ->
  bBits:size_nat{0 < bBits} -> b:lseqbn (bits_to_bn bBits) -> res:lseqbn nLen ->
  Tot (lseqbn nLen)
  
let mod_exp nLen pow2_i iLen modBits n a bBits b res =
  let rLen:size_nat = nLen + 1 in
  assume (128 * rLen < max_size_t);
  let exp_r:size_nat = 64 * rLen in
  let exp2:size_nat = exp_r + exp_r in
  
  let karaLen:size_nat = 2 * rLen + 4 * pow2_i in
  let stLen:size_nat = 7 * rLen + karaLen in

  let st = create stLen (u64 0) in
  let n1 = sub st 0 rLen in
  let r2 = sub st rLen rLen in
  let a1 = sub st (2 * rLen) rLen in
  let acc = sub st (3 * rLen) rLen in
  
  //let aM = sub st (4 * rLen) rLen in
  //let accM = sub st (5 * rLen) rLen in
  let res1 = sub st (6 * rLen) rLen in
  //let st_exp = sub st (4 * rLen) (2 * rLen) in
  //let st_kara = sub st (7 * rLen) karaLen in
  //let st' = sub st (7 * rLen) (2 * rLen) in

  let n1 = update_sub n1 0 nLen n in
  let a1 = update_sub a1 0 nLen a in
  
  let acc = acc.[0] <- u64 1 in
  let r2 = bn_pow2_mod_n modBits rLen n1 exp2 r2 in// r2 = r * r % n
  let n0 = n.[0] in
  let nInv_u64 = mod_inv_u64 n0 in // n * nInv = 1 (mod (pow2 64))
  let res1 = mod_exp_mont rLen pow2_i iLen bBits b nInv_u64 st in
  let res1' = sub res1 0 nLen in
  update_sub res 0 nLen res1'
