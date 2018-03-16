module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key

open Crypto.Symmetric.Bytes

module MR = FStar.Monotonic.RRef
module MM = FStar.Monotonic.Map

assume val random_bytes: n:nat -> lbytes n

noeq abstract type odh_parameters =
  | OP:
  share_length:nat ->
  exponent_length:nat ->
  hash_length:nat ->
  generator:lbytes share_length ->
  exponentiate:(lbytes share_length -> lbytes exponent_length -> lbytes share_length) ->
  hash:(bytes -> lbytes hash_length) ->
  odh_parameters

abstract type share (op:odh_parameters) =
  | SH:
  raw_sh:lbytes op.share_length ->
  h:bool ->
  share op

abstract type exponent (op:odh_parameters) =
  | EXP:
  raw_exp:lbytes op.exponent_length ->
  sh:share op{sh.raw_sh = op.exponentiate op.generator raw_exp} ->
  exponent op

let gen_dh (oparam:odh_parameters) =
  let raw_exp = random_bytes oparam.exponent_length in
  let raw_sh = oparam.exponentiate oparam.generator raw_exp in
  let sh = SH raw_sh true in
  EXP raw_exp sh

let coerce_dh_sh (oparam:odh_parameters) (raw_sh:lbytes oparam.share_length) =
  SH raw_sh false

let coerce_dh_exp (oparam:odh_parameters) (raw_exp:lbytes oparam.exponent_length) =
  let raw_sh = oparam.exponentiate oparam.generator raw_exp in
  let sh = SH raw_sh false in
  EXP raw_exp sh

let id = id:(bytes*bytes)

val create_id: #oparam:odh_parameters -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> i:id
let create_id #oparam sh1 sh2 =
  let end_sh1 = FStar.Endianness.little_endian sh1.raw_sh in
  let end_sh2 = FStar.Endianness.little_endian sh2.raw_sh in
  if end_sh1 < end_sh2 then
    (sh1.raw_sh,sh2.raw_sh)
  else
    (sh2.raw_sh,sh1.raw_sh)

val lemma_symmetric_id: #oparam:odh_parameters -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> Lemma
  (requires True)
  (ensures create_id sh1 sh2 = create_id sh2 sh1)
  [SMTPat (create_id #oparam sh1 sh2)]
let lemma_symmetric_id #oparam sh1 sh2 =
  FStar.Endianness.lemma_little_endian_bij sh1.raw_sh sh2.raw_sh

let key_package_log_key = id
let key_package_log_value (key_length:nat) (i:id) = key_package #id key_length i
let key_package_log_range (key_length:nat) (k:key_package_log_key) = key_package_log_value key_length k
let key_package_log_inv (key_length:nat) (f:MM.map' (key_package_log_key) (key_package_log_range key_length)) = True

let key_package_log (rgn:MR.rid) (key_length:nat) =
  MM.t rgn (key_package_log_key) (key_package_log_range key_length) (key_package_log_inv key_length)

noeq abstract type odh_package (op:odh_parameters) =
  | ODH:
  rgn:MR.rid ->
  kp_log:key_package_log rgn op.share_length ->
  b:bool ->
  odh_package op

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val dh_op: #oparam:odh_parameters -> #op:odh_package oparam -> sh:share oparam -> exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh} -> ST (key_package #id oparam.share_length (create_id sh exp.sh))
  (requires (fun h0 -> True))
  (ensures (fun h0 kp h1 ->
    let i = create_id sh exp.sh in
    let both_honest = sh.h && exp.sh.h in
    ((both_honest /\ op.b) ==>
      (MM.defined op.kp_log i h0 ==>
        h0 == h1)
      /\ (MM.fresh op.kp_log i h0 ==>
        MR.witnessed (MM.contains op.kp_log i kp)
        /\ MR.m_sel h1 op.kp_log == MM.upd (MR.m_sel h0 op.kp_log) i kp
        /\ modifies (Set.singleton op.rgn) h0 h1
        ))
    /\ ((~both_honest \/ ~op.b) ==>
      h0 == h1)
  ))
let dh_op #oparam #op sh exp =
  let both_honest = sh.h && exp.sh.h in
  let i = create_id sh exp.sh in
  if both_honest && op.b then
    (MR.m_recall op.kp_log;
    match MM.lookup op.kp_log i with
    | None ->
      let kp = gen oparam.share_length i in
      MM.extend op.kp_log i kp;
      kp
    | Some kp -> kp)
  else
    (MR.m_recall op.kp_log;
    set oparam.share_length (oparam.exponentiate sh.raw_sh exp.raw_exp) i)
