module Hacl.Spec.Shift

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas
open Hacl.Spec.Lib

let bn_tbit = u64 0x8000000000000000

val bn_lshift_:
  aLen:size_nat ->
  a:lseqbn aLen -> count:size_nat -> nw:size_nat ->
  lb:uint32{0 < uint_v #U32 lb /\ uint_v #U32 lb < 64} ->
  res:lseqbn aLen{count + nw < aLen} -> Tot (lseqbn aLen)
let rec bn_lshift_ aLen a count nw lb res =
  if (count > 0) then begin
    let i = nw + count in
    let tmp = res.[i] in
    let count = count - 1 in
    let t1 = a.[count] in
    let rb = u32 64 -. lb in
    let res = res.[i] <- tmp |. (t1 >>. rb) in
    let res = res.[i - 1] <- t1 <<. lb in
    bn_lshift_ aLen a count nw lb res end
  else res

// res = a << n
val bn_lshift:
  aLen:size_nat ->
  a:lseqbn aLen -> nCount:size_nat{aLen - nCount / 64 > 0} ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_lshift aLen a nCount res =
  if (nCount = 0) then
    update_sub res 0 aLen a
  else begin
    //fill aLen res (u64 0);
    let res = create aLen (u64 0) in
    let nw = nCount / 64 in
    let lb = nCount % 64 in
    if (lb = 0) then begin
      let aLen' = aLen - nw in
      let a' = sub a 0 aLen' in
      update_sub res nw aLen' a' end
    else begin
      let lb = u32 lb in
      let count = aLen - nw - 1 in
      let t1 = a.[count] in
      let res = res.[nw + count] <- t1 <<. lb in
      bn_lshift_ aLen a count nw lb res end
  end

val bn_lshift1_:
  aLen:size_nat{aLen > 0} ->
  a:lseqbn aLen -> carry:uint64 -> i:size_nat{i <= aLen} ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
  (decreases (aLen - i))
let rec bn_lshift1_ aLen a carry i res =
  if (i < aLen) then begin
    let tmp = a.[i] in
    let res = res.[i] <- (tmp <<. (u32 1)) |. carry in
    let carry = if (eq_u64 (tmp &. bn_tbit) bn_tbit) then u64 1 else u64 0 in
    bn_lshift1_ aLen a carry (i + 1) res
  end else res

// res = a << 1
val bn_lshift1:
  aLen:size_nat{aLen > 0} -> a:lseqbn aLen ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_lshift1 aLen a res = bn_lshift1_ aLen a (u64 0) 0 res

val bn_rshift_:
  aLen:size_nat{aLen > 0} ->
  a:lseqbn aLen -> i:size_nat{i > 0} -> nw:size_nat ->
  rb:uint32{0 < uint_v #U32 rb /\ uint_v #U32 rb < 64} -> l:uint64 ->
  res:lseqbn aLen{i + nw <= aLen} -> Tot (lseqbn aLen)
  (decreases (aLen - i))
let rec bn_rshift_ aLen a i nw rb l res =
  if (i < aLen - nw) then begin
    let tmp = l >>. rb in
    let l = a.[nw + i] in
    let lb = u32 64 -. rb in
    let res = res.[i - 1] <- tmp |. (l <<. lb) in
    bn_rshift_ aLen a (i + 1) nw rb l res end
  else res.[i - 1] <- l >>. rb

// res = a >> n
val bn_rshift:
  aLen:size_nat ->
  a:lseqbn aLen -> nCount:size_nat{aLen - nCount / 64 > 0} ->
  res:lseqbn aLen -> Tot (lseqbn aLen)
let bn_rshift aLen a nCount res =
  if (nCount = 0) then
    update_sub res 0 aLen a
  else begin
    let nw = nCount / 64 in
    let rb = nCount % 64 in
    (if rb = 0 then begin
      let aLen' = aLen - nw in
      let a' = sub a nw aLen' in
      update_sub res 0 aLen' a' end
    else begin
      let l = a.[nw] in
      bn_rshift_ aLen a 1 nw (u32 rb) l res end)
  end

// res = a % (pow2 nCount)
val bn_mod_pow2_n:
  aLen:size_nat -> a:lseqbn aLen -> nCount:size_nat ->
  resLen:size_nat{resLen <= aLen /\ resLen - nCount / 64 > 0} ->
  res:lseqbn resLen -> Tot (lseqbn resLen)
let bn_mod_pow2_n aLen a nCount resLen res =
  let nw = nCount / 64 in
  let nb = nCount % 64 in
  let a' = sub a 0 resLen in
  let res = update_sub res 0 resLen a' in

  let (start_i, res) =
    if (nb > 0) then begin
      let lb = u32 64 -. u32 nb in
      let res = res.[nw] <- res.[nw] &. (u64 0xffffffffffffffff >>. lb) in
      (nw + 1, res) end
    else (nw, res) in

  if (start_i < resLen) then begin
    let resLen' = resLen - start_i in
    let res' = create resLen' (u64 0) in
    update_sub res start_i resLen' res' end
  else res
