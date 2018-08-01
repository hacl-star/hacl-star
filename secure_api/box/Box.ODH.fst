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

let get_exp_share #oparams e = e.sh

let get_share_raw #oparams sh = sh.raw_sh

let get_exponent_raw #oparams exp = exp.raw_exp

let gen_dh_footprint ip oparams h0 h1 =
  register_footprint ip h0 h1

let gen_dh ip oparam =
  let raw_exp = random_bytes oparam.exponent_length in
  let raw_sh = oparam.exponentiate raw_exp oparam.generator in
  let h0 = get() in
  assume(fresh ip (PK_id raw_sh) h0);
  register ip (PK_id raw_sh) true;
  let sh = SH raw_sh in
  (EXP raw_exp sh,sh)

let coerce_dh_sh_footprint ip oparams raw_sh h0 h1 =
  register_footprint ip h0 h1

let coerce_dh_sh ip oparam raw_sh =
  register ip (PK_id raw_sh) false;
  SH raw_sh

let coerce_dh_exp_footprint ip oparams raw_sh h0 h1 =
  register_footprint ip h0 h1

let coerce_dh_exp ip oparam raw_exp =
  let raw_sh = oparam.exponentiate raw_exp oparam.generator in
  register ip (PK_id raw_sh) false;
  let sh = SH raw_sh in
  EXP raw_exp sh

let get_op_rgn #ip #key_length #key_type #kp #oparam op = op.kp_log_rgn

let get_op_log #ip #key_length #key_type #kp #oparam op = op.kp_log

let recall_op_log #ip #key_length #key_type #kp #oparam op =
  recall op.kp_log

let create_odh_package #ip #key_length #key_type rgn kp oparam =
  let odh_rgn = new_region rgn in
  let kp_log = MM.alloc #odh_rgn #key_package_log_key #(key_package_log_range key_type) #(key_package_log_inv key_type) in
  ODH odh_rgn kp_log

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
let dh_op #ip #key_length #key_type #kp #oparam op sh exp =
  let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
  let both_honest = get_honesty ip i in
    if Flags.prf_odh && both_honest then
      (recall op.kp_log;
      match MM.lookup op.kp_log i with
      | None ->
        //let k:(k:key_type i{kp.hon k = true}) = kp.gen i in
        let k = kp.gen i in
        MM.extend op.kp_log i k;
        k
      | Some k -> k)
    else
      (recall op.kp_log;
      kp.coerce i (oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)))
