module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Key

open FStar.Endianness

module MM = FStar.Monotonic.Map

val random_bytes: n:nat{n<=32} -> lbytes n

noeq type odh_parameters =
  | OP:
  share_length:(n:nat{n<=32}) ->
  exponent_length:(n:nat{n<=32}) ->
  hash_length:(n:nat{n<=32}) ->
  generator:lbytes share_length ->
  exponentiate:(lbytes exponent_length -> lbytes share_length -> lbytes share_length) ->
  hash:(lbytes share_length -> lbytes hash_length) ->
  odh_parameters

abstract type share (oparam:odh_parameters) =
  | SH:
  raw_sh:lbytes oparam.share_length ->
  h:bool ->
  share oparam

abstract type exponent (oparam:odh_parameters) =
  | EXP:
  raw_exp:lbytes oparam.exponent_length ->
  sh:share oparam{sh.raw_sh = oparam.exponentiate raw_exp oparam.generator} ->
  exponent oparam

val sh_hon: #oparams:odh_parameters -> sh:share oparams -> GTot (b:bool{b=sh.h})

val exp_hon: #oparams:odh_parameters -> exp:exponent oparams -> GTot (b:bool{b=exp.sh.h})

val get_exp_share: #oparams:odh_parameters -> e:exponent oparams -> sh:share oparams{e.sh = sh}

val get_share_raw: #oparams:odh_parameters -> sh:share oparams -> raw:lbytes oparams.share_length{raw = sh.raw_sh}

val get_exponent_raw: #oparams:odh_parameters -> exp:exponent oparams -> GTot (raw:lbytes oparams.exponent_length{raw = exp.raw_exp})

val gen_dh: (oparam:odh_parameters) -> exponent oparam

val coerce_dh_sh: (oparam:odh_parameters) -> (rash_sh:lbytes oparam.share_length) -> sh:share oparam

val coerce_dh_exp: (oparam:odh_parameters) -> (raw_exp:lbytes oparam.exponent_length) -> exp:exponent oparam

let id = id:(bytes*bytes)

val create_id: (#oparam:odh_parameters) -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> i:id

#set-options "--z3rlimit 300 --max_ifuel 0 --max_fuel 1"
val lemma_symmetric_id: (#oparam:odh_parameters) -> sh1:share oparam -> sh2:share oparam{sh1.raw_sh <> sh2.raw_sh} -> Lemma
  (requires True)
  (ensures create_id sh1 sh2 = create_id sh2 sh1)
  [SMTPat (create_id #oparam sh1 sh2)]

let key_package_log_key = id
let key_package_log_value (i:id) (key_type:(id -> Type0)) = key_type i
let key_package_log_range  (key_type:(id -> Type0)) (k:key_package_log_key) = key_package_log_value k key_type
let key_package_log_inv (key_type:(id -> Type0)) (f:MM.map' (key_package_log_key) (key_package_log_range key_type)) = True

let key_package_log (rgn:erid) (key_type:(id -> Type0)) =
  MM.t rgn (key_package_log_key) (key_package_log_range key_type) (key_package_log_inv key_type)

val b:bool

val get_flag: unit -> GTot (flag:bool{flag = b})

noeq abstract type odh_package (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (kp:key_package key_length key_type) (oparam:odh_parameters{oparam.hash_length = key_length}) =
  | ODH:
  rgn:erid ->
  kp_log:key_package_log rgn key_type ->
  odh_package #key_length #key_type kp oparam

val get_op_rgn: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (#kp:key_package key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> (op:odh_package #key_length #key_type kp oparam) -> (rgn:erid{rgn = op.rgn})

val get_op_log: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (#kp:key_package key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> (op:odh_package #key_length #key_type kp oparam) -> GTot (log:key_package_log op.rgn key_type)

val recall_op_log: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (#kp:key_package key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> (op:odh_package #key_length #key_type kp oparam) -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ contains h1 op.kp_log
  ))

val create_odh_package: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (kp:key_package key_length key_type) -> (oparam:odh_parameters{oparam.hash_length = key_length}) -> (rgn:erid) -> ST (odh_package #key_length #key_type kp oparam)
  (requires (fun h0 -> True))
  (ensures (fun h0 op h1 ->
    modifies (Set.singleton rgn) h0 h1
    /\ extends op.rgn rgn
  ))

let dh_op_modified_regions (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (#kp:key_package key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (h0:mem) : (GTot (Set.set rid)) =
  let i = create_id sh exp.sh in
  let both_honest = sh.h && exp.sh.h in
  if both_honest && b then
    match MM.sel (sel h0 op.kp_log) i with
    | Some _ ->
      Set.empty
    | None ->
        Set.singleton op.rgn
  else
    Set.empty

let dh_op_log_change (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (#kp:key_package key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (h0:mem) (h1:mem) =
  let i = create_id sh exp.sh in
  let both_honest = sh.h && exp.sh.h in
  contains h0 op.kp_log
  /\ ((both_honest /\ b) ==>
      (MM.defined op.kp_log i h0 ==>
        Some? (sel h1 op.kp_log i)
        /\ (let k = Some?.v (sel h1 op.kp_log i) in
          sel h1 op.kp_log == sel h0 op.kp_log
        /\ witnessed (MM.contains op.kp_log i k)))
      /\ (MM.fresh op.kp_log i h0 ==>
          Some? (sel h1 op.kp_log i)
          /\ (let k = Some?.v (sel h1 op.kp_log i) in
          witnessed (MM.contains op.kp_log i k)
          /\ sel h1 op.kp_log == MM.upd (sel h0 op.kp_log) i k))
    )
  /\ ((~both_honest \/ ~b) ==>
      sel h1 op.kp_log == sel h0 op.kp_log)

// Do we need/want this?
let dh_op_functional_spec (#key_length:(n:nat{n<=32})) (#key_type:(id -> Type0)) (#kp:key_package key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (k:key_type (create_id sh exp.sh)) (h:mem) =
  let i = create_id sh exp.sh in
  let both_honest = sh.h && exp.sh.h in
  ((both_honest) ==>
    (b ==>
      (Some? (MM.sel (sel h op.kp_log) i)
      /\ k == Some?.v (MM.sel (sel h op.kp_log) i))) // If possible, indicate somehow that k was randomly drawn.
    /\ (~b ==>
      getGT kp i k == oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)
      /\ hon kp i k = true)
    )
  /\ ((~both_honest) ==>
      getGT kp i k == oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)
      /\ hon kp i k = false)


#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val dh_op: (#key_length:(n:nat{n<=32})) -> (#key_type:(id -> Type0)) -> (#kp:key_package key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> op:odh_package kp oparam -> sh:share oparam -> exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh} -> ST (key_type (create_id sh exp.sh))
  (requires (fun h0 -> True))
  (ensures (fun h0 k h1 ->
    let i = create_id sh exp.sh in
    let both_honest = sh.h && exp.sh.h in
    modifies (dh_op_modified_regions op sh exp h0) h0 h1
    /\ dh_op_log_change op sh exp h0 h1
   // /\ dh_op_functional_spec op sh exp k h1
  /\ ((both_honest) ==>
    (b ==>
      (Some? (MM.sel (sel h1 op.kp_log) i)
      /\ k == Some?.v (MM.sel (sel h1 op.kp_log) i)))
    /\ (~b ==>
      getGT kp i k == oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)
      /\ hon kp i k = true)
    ) // If possible, indicate somehow that k was randomly drawn.
  /\ ((~both_honest) ==>
      getGT kp i k == oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)
      /\ hon kp i k = false)
  ))
