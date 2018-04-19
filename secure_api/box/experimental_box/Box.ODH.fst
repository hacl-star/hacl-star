module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key

open FStar.Endianness

module MM = FStar.Monotonic.Map

assume val random_bytes: n:nat{n<=32} -> lbytes n

noeq abstract type odh_parameters =
  | OP:
  share_length:(n:nat{n<=32}) ->
  exponent_length:(n:nat{n<=32}) ->
  hash_length:(n:nat{n<=32}) ->
  generator:lbytes share_length ->
  exponentiate:(lbytes share_length -> lbytes exponent_length -> lbytes share_length) ->
  hash:(bytes -> lbytes hash_length) ->
  odh_parameters

abstract type share (oparam:odh_parameters) =
  | SH:
  raw_sh:lbytes oparam.share_length ->
  h:bool ->
  share oparam

abstract type exponent (oparam:odh_parameters) =
  | EXP:
  raw_exp:lbytes oparam.exponent_length ->
  sh:share oparam{sh.raw_sh = oparam.exponentiate oparam.generator raw_exp} ->
  exponent oparam

let gen_dh (oparam:odh_parameters) =
  let raw_exp = random_bytes oparam.exponent_length in
  let raw_sh = oparam.exponentiate oparam.generator raw_exp in
  let sh = SH raw_sh true in
  EXP raw_exp sh

let coerce_dh_sh  (oparam:odh_parameters) (raw_sh:lbytes oparam.share_length) =
  SH raw_sh false

let coerce_dh_exp  (oparam:odh_parameters) (raw_exp:lbytes oparam.exponent_length) =
  let raw_sh = oparam.exponentiate oparam.generator raw_exp in
  let sh = SH raw_sh false in
  EXP raw_exp sh

let id = id:(bytes*bytes)

val create_id: (#oparam:odh_parameters) -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> i:id
let create_id #oparam sh1 sh2 =
  let int_sh1 = little_endian sh1.raw_sh in
  let int_sh2 = little_endian sh2.raw_sh in
  //let int_sh1 = int_of_bytes sh1.raw_sh in
  //let int_sh2 = int_of_bytes sh2.raw_sh in
  if int_sh1 < int_sh2 then
    (sh1.raw_sh,sh2.raw_sh)
  else
    (sh2.raw_sh,sh1.raw_sh)

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 1"
val lemma_symmetric_id: (#oparam:odh_parameters) -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> Lemma
  (requires True)
  (ensures create_id sh1 sh2 = create_id sh2 sh1)
  [SMTPat (create_id #oparam sh1 sh2)]
let lemma_symmetric_id #oparam sh1 sh2 =
  lemma_little_endian_bij sh1.raw_sh sh2.raw_sh
  //bytes_of_int_of_bytes sh1.raw_sh;
  //bytes_of_int_of_bytes sh2.raw_sh

let key_package_log_key = id
let key_package_log_value (i:id) (key_type:(id -> Type0)) = key_type i
let key_package_log_range  (key_type:(id -> Type0)) (k:key_package_log_key) = key_package_log_value k key_type
let key_package_log_inv (key_type:(id -> Type0)) (f:MM.map' (key_package_log_key) (key_package_log_range key_type)) = True

let key_package_log (rgn:erid) (key_type:(id -> Type0)) =
  MM.t rgn (key_package_log_key) (key_package_log_range key_type) (key_package_log_inv key_type)

noeq abstract type odh_package (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (kp:key_package key_length key_type) (oparam:odh_parameters{oparam.hash_length = key_length}) =
  | ODH:
  rgn:erid ->
  kp_log:key_package_log rgn key_type ->
  b:bool ->
  odh_package #key_length #key_type kp oparam

#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val dh_op: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (#kp:key_package key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> #op:odh_package kp oparam -> sh:share oparam -> exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh} -> ST (key_type (create_id sh exp.sh))
  (requires (fun h0 -> True))
  (ensures (fun h0 k h1 ->
    let i = create_id sh exp.sh in
    let both_honest = sh.h && exp.sh.h in
    ((both_honest /\ op.b) ==>
      (MM.defined op.kp_log i h0 ==>
        h0 == h1)
      /\ (MM.fresh op.kp_log i h0 ==>
        witnessed (MM.contains op.kp_log i k)
        /\ sel h1 op.kp_log == MM.upd (sel h0 op.kp_log) i k
        /\ modifies (Set.singleton op.rgn) h0 h1
        ))
    /\ ((~both_honest \/ ~op.b) ==>
      h0 == h1)
  ))

let dh_op #key_length #key_type #kp #oparam #op sh exp =
  let both_honest = sh.h && exp.sh.h in
  let i = create_id sh exp.sh in
  if both_honest && op.b then
    (recall op.kp_log;
    match MM.lookup op.kp_log i with
    | None ->
      let k = kp.gen i in
      MM.extend op.kp_log i k;
      k
    | Some k -> k)
  else
    (recall op.kp_log;
    kp.set i (oparam.hash (oparam.exponentiate sh.raw_sh exp.raw_exp)))
