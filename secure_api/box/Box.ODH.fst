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

let create_odh_index_package rgn oparams =
  create_leaf_index_package rgn (lbytes oparams.share_length)

let gen_dh_footprint oparams ip h0 h1 =
  register_footprint ip h0 h1

#set-options "--z3rlimit 50 --max_ifuel 2 --max_fuel 2 --print_implicits"
let gen_dh oparams ip =
  let raw_exp = random_bytes oparams.exponent_length in
  let raw_sh = oparams.exponentiate raw_exp oparams.generator in
  let h0 = get() in
  assume(fresh #ip raw_sh h0); // Fixme!
  register #ip raw_sh true;
  let sh = SH raw_sh in
  let exp = EXP raw_exp sh in
  exp,sh

let coerce_dh_sh_footprint oparams ip raw_sh h0 h1 =
  register_footprint ip h0 h1

let coerce_dh_sh oparam ip raw_sh =
  SH raw_sh

let coerce_dh_exp_footprint oparams ip raw_sh h0 h1 =
  register_footprint ip h0 h1

let coerce_dh_exp oparam ip raw_exp =
  let raw_sh = oparam.exponentiate raw_exp oparam.generator in
  let sh = SH raw_sh in
  EXP raw_exp sh

let get_op_rgn #oparams #ip #kp op = op.log_rgn

let get_op_log #oparams #ip #kp op = op.log

let recall_op_log #oparams #ip #kp op =
  if Flags.model then
    let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
    recall log
  else
    ()

let create_odh_package #oparams ip rgn kp =
  let odh_rgn = new_region rgn in
  let kp_log =
    if Flags.model then
      MM.alloc #odh_rgn #(key_log_key (composed_ip ip)) #(key_log_range (composed_ip ip) kp.key_type) #(key_log_inv (composed_ip ip) kp.key_type)
    else
      ()
  in
  ODH odh_rgn kp_log

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 2"
let dh_op #oparams #ip #kp op sh exp =
  let h0 = get() in
  let i:id (composed_ip ip) = composed_id sh exp.sh in
  let both_honest = get_honesty #(composed_ip ip) i in
    if Flags.prf_odh && both_honest then
      let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
      (recall log;
      match MM.lookup log i with
      | None ->
        let k = kp.gen i in
        MM.extend log i k;
        k
      | Some k -> k)
    else
      (recall_op_log op;
      kp.coerce i (oparams.hash (oparams.exponentiate exp.raw_exp sh.raw_sh)))
