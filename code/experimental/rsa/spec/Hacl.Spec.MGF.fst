module Hacl.Spec.MGF

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntSeq.Lemmas

open Hacl.Spec.Lib
open Hacl.Spec.Convert

module Hash = Spec.SHA2

(* SHA 256 *)
inline_for_extraction 
let hLen:size_nat = 32

let max_input_len_sha256 = pow2 61
val hash_sha256:
  msgLen:size_nat{msgLen < max_input_len_sha256} ->
  msg:lbytes msgLen ->
  hash:lbytes hLen ->
  Tot (msgHash:lbytes hLen)
let hash_sha256 msgLen msg hash = Hash.hash256 msgLen msg

(* Mask Generation Function *)
val mgf_sha256_:
  count_max:size_nat ->
  accLen:size_nat{accLen = hLen * count_max} ->
  stLen:size_nat{stLen = 4 + 2 * hLen + accLen} -> st:lbytes stLen ->
  counter:size_nat{counter <= count_max} -> Tot (lbytes accLen)
  (decreases (count_max - counter))
  #reset-options "--z3rlimit 50 --max_fuel 2"
let rec mgf_sha256_ count_max accLen stLen st counter =
  let mgfseed_counter_len:size_nat = hLen + 4 in
  let mgfseed_counter = sub st 0 mgfseed_counter_len in
  let mHash = sub st mgfseed_counter_len hLen in
  let acc = sub st (mgfseed_counter_len + hLen) accLen in
  let c = sub mgfseed_counter hLen 4 in

  if (counter < count_max) then begin
     let c = c.[0] <- to_u8 #U32 (u32 counter >>. u32 24) in
     let c = c.[1] <- to_u8 #U32 (u32 counter >>. u32 16) in
     let c = c.[2] <- to_u8 #U32 (u32 counter >>. u32 8) in
     let c = c.[3] <- to_u8 #U32 (u32 counter) in
     assert_norm (mgfseed_counter_len < max_input_len_sha256);
     let mgfseed_counter = update_sub mgfseed_counter hLen 4 c in
     let mHash = hash_sha256 mgfseed_counter_len mgfseed_counter mHash in
     let acc = update_sub acc (hLen * counter) hLen mHash in
     let st = update_sub st (mgfseed_counter_len + hLen) accLen acc in
     mgf_sha256_ count_max accLen stLen st (counter + 1)
  end else acc

val mgf_sha256:
    mgfseed:lbytes hLen ->
    len:size_nat{0 < len /\ 4 + 2 * hLen + hLen * (blocks len hLen) < max_size_t} ->
    res:lbytes len -> Tot (lbytes len)
    #reset-options "--z3rlimit 50 --max_fuel 0"
let mgf_sha256 mgfseed len res =
    let count_max = blocks len hLen in
    let accLen:size_nat = hLen * count_max in
    let mgfseed_counter_len:size_nat = hLen + 4 in
    let stLen:size_nat = mgfseed_counter_len + hLen + accLen in
    let st = create stLen (u8 0) in
    //let mgfseed_counter = sub st 0 mgfseed_counter_len in
    let st = update_sub st 0 hLen mgfseed in
    //let mHash = sub st mgfseed_counter_len hLen in
    //let acc = sub st (mgfseed_counter_len + hLen) accLen in
    let acc = mgf_sha256_ count_max accLen stLen st 0 in
    let acc' = sub acc 0 len in
    update_sub res 0 len acc'


