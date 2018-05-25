module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key

open FStar.Endianness

module MM = FStar.Monotonic.Map

let rec random_bytes n =
  match n with
  | 0 -> let l:lbytes 0 = createL [] in l
  | _ -> append (createL [0x0buy]) (random_bytes (n-1))

let sh_hon #oparams sh = sh.h

let exp_hon #oparams exp = exp.sh.h

let get_exp_share #oparams e = e.sh

let get_share_raw #oparams sh = sh.raw_sh

let get_exponent_raw #oparams exp = exp.raw_exp

let gen_dh (oparam:odh_parameters) =
  let raw_exp = random_bytes oparam.exponent_length in
  let raw_sh = oparam.exponentiate raw_exp oparam.generator in
  let sh = SH raw_sh true in
  EXP raw_exp sh

let coerce_dh_sh  (oparam:odh_parameters) (raw_sh:lbytes oparam.share_length) =
  SH raw_sh false

let coerce_dh_exp  (oparam:odh_parameters) (raw_exp:lbytes oparam.exponent_length) =
  let raw_sh = oparam.exponentiate raw_exp oparam.generator in
  let sh = SH raw_sh false in
  EXP raw_exp sh

let create_id #oparam sh1 sh2 =
  let int_sh1 = little_endian sh1.raw_sh in
  let int_sh2 = little_endian sh2.raw_sh in
  //let int_sh1 = int_of_bytes sh1.raw_sh in
  //let int_sh2 = int_of_bytes sh2.raw_sh in
  if int_sh1 < int_sh2 then
    (sh1.raw_sh,sh2.raw_sh)
  else
    (sh2.raw_sh,sh1.raw_sh)

let lemma_symmetric_id #oparam sh1 sh2 =
  lemma_little_endian_bij sh1.raw_sh sh2.raw_sh

let get_flag #key_length #key_type #kp #oparam op = op.b

let get_op_rgn (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (#kp:key_package key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package #key_length #key_type kp oparam) = op.rgn

let get_op_log (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (#kp:key_package key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package #key_length #key_type kp oparam) = op.kp_log

let recall_op_log #key_length #key_type #kp #oparam op =
  recall op.kp_log

let create_odh_package (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (kp:key_package key_length key_type) (oparam:odh_parameters{oparam.hash_length = key_length}) (rgn:erid) (b:bool) =
  let odh_rgn = new_region rgn in
  let kp_log = MM.alloc #odh_rgn #key_package_log_key #(key_package_log_range key_type) #(key_package_log_inv key_type) in
  ODH odh_rgn b kp_log

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
let dh_op #key_length #key_type #kp #oparam op sh exp =
  let both_honest = sh.h && exp.sh.h in
  let i = create_id sh exp.sh in
  if both_honest then
    if op.b then
      (recall op.kp_log;
      match MM.lookup op.kp_log i with
      | None ->
        let k = gen kp i in
        MM.extend op.kp_log i k;
        k
      | Some k -> k)
    else
      (recall op.kp_log;
      set kp i (oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)))
  else
    (recall op.kp_log;
    cset kp i (oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)))
