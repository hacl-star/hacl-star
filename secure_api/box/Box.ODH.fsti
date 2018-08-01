module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Index
open Box.Key

open FStar.Endianness

module MM = FStar.Monotonic.Map

val random_bytes: n:nat{n<=32} -> lbytes n

//val random_bytes: n:nat{n<=32} -> ST (lbytes n)
//  (requires (fun h0 -> True))
//  (ensures (fun h0 b h1 ->
//    h0 == h1
//  ))

noeq type odh_parameters =
  | OP:
  share_length:(n:nat{n=32}) ->
  exponent_length:(n:nat{n=32}) ->
  hash_length:(n:nat{n=32}) ->
  generator:lbytes share_length ->
  exponentiate:(lbytes exponent_length -> lbytes share_length -> lbytes share_length) ->
  hash:(lbytes share_length -> lbytes hash_length) ->
  odh_parameters

abstract type share (oparam:odh_parameters) =
  | SH:
  raw_sh:lbytes oparam.share_length ->
  share oparam

abstract type exponent (oparam:odh_parameters) =
  | EXP:
  raw_exp:lbytes oparam.exponent_length ->
  sh:share oparam{sh.raw_sh = oparam.exponentiate raw_exp oparam.generator} ->
  exponent oparam

val get_exp_share: #oparams:odh_parameters -> e:exponent oparams -> sh:share oparams{e.sh = sh}

val get_share_raw: #oparams:odh_parameters -> sh:share oparams -> raw:lbytes oparams.share_length{raw = sh.raw_sh}

val get_exponent_raw: #oparams:odh_parameters -> exp:exponent oparams -> GTot (raw:lbytes oparams.exponent_length{raw = exp.raw_exp})

val gen_dh_footprint: ip:index_package -> oparam:odh_parameters -> h0:mem -> h1:mem -> Type0

val gen_dh: (ip:index_package) -> (oparam:odh_parameters) -> ST (dh_keypair:(exponent oparam*share oparam))
  (requires (fun h0 -> True))
  (ensures (fun h0 (e,sh) h1 ->
    e.sh == sh
    /\ registered ip (PK_id sh.raw_sh)
    /\ honest ip (PK_id sh.raw_sh)
    /\ gen_dh_footprint ip oparam h0 h1
  ))

val coerce_dh_sh_footprint: (ip:index_package) -> (oparam:odh_parameters) -> (raw_sh:lbytes oparam.share_length) -> h0:mem -> h1:mem -> Type0

val coerce_dh_sh: (ip:index_package) -> (oparam:odh_parameters) -> (raw_sh:lbytes oparam.share_length) -> ST (sh:share oparam{sh.raw_sh = raw_sh})
  (requires (fun h0 ->
    fresh ip (PK_id raw_sh) h0
  ))
  (ensures (fun h0 sh h1 ->
    registered ip (PK_id raw_sh)
    /\ dishonest ip (PK_id raw_sh)
    /\ coerce_dh_sh_footprint ip oparam raw_sh h0 h1
  ))

val coerce_dh_exp_footprint: (ip:index_package) -> (oparam:odh_parameters) -> (raw_exp:lbytes oparam.exponent_length) -> h0:mem -> h1:mem -> Type0

val coerce_dh_exp: (ip:index_package) -> (oparam:odh_parameters) -> (raw_exp:lbytes oparam.exponent_length) -> ST (exp:exponent oparam{exp.raw_exp = raw_exp})
  (requires (fun h0 ->
    let raw_sh = oparam.exponentiate raw_exp oparam.generator in
    fresh ip (PK_id raw_sh) h0
  ))
  (ensures (fun h0 sh h1 ->
    let raw_sh = oparam.exponentiate raw_exp oparam.generator in
    registered ip (PK_id raw_sh)
    /\ dishonest ip (PK_id raw_sh)
    /\ coerce_dh_exp_footprint ip oparam raw_exp h0 h1
  ))

let key_package_log_key = inst_id
let key_package_log_value (i:inst_id) (key_type:(inst_id -> Type0)) = key_type i
let key_package_log_range  (key_type:(inst_id -> Type0)) (k:key_package_log_key) = key_package_log_value k key_type
let key_package_log_inv (key_type:(inst_id -> Type0)) (f:MM.map' (key_package_log_key) (key_package_log_range key_type)) = True

let key_package_log (rgn:erid) (key_type:(inst_id -> Type0)) =
  MM.t rgn (key_package_log_key) (key_package_log_range key_type) (key_package_log_inv key_type)

noeq abstract type odh_package (#ip:index_package) (#key_length:(n:nat{n<=32})) (#key_type:(inst_id -> Type0)) (kp:key_package ip key_length key_type) (oparam:odh_parameters{oparam.hash_length = key_length}) =
  | ODH:
  kp_log_rgn:erid ->
  kp_log:key_package_log kp_log_rgn key_type ->
  odh_package #ip #key_length #key_type kp oparam

val get_op_rgn: (#ip:index_package) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> (#kp:key_package ip key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> op:odh_package kp oparam -> (rgn:erid{rgn = op.kp_log_rgn})

val get_op_log: (#ip:index_package) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> (#kp:key_package ip key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> op:odh_package kp oparam -> GTot (log:key_package_log op.kp_log_rgn key_type)

val recall_op_log: (#ip:index_package) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> (#kp:key_package ip key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> op:odh_package kp oparam -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ contains h1 op.kp_log
  ))

val create_odh_package: (#ip:index_package) -> (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> (rgn:erid) -> (kp:key_package ip key_length key_type) -> (oparam:odh_parameters{oparam.hash_length = key_length}) -> ST (odh_package #ip #key_length #key_type kp oparam)
  (requires (fun h0 -> True))
  (ensures (fun h0 op h1 ->
    modifies (Set.singleton op.kp_log_rgn) h0 h1
    /\ extends op.kp_log_rgn rgn
  ))

let dh_op_memory_footprint (#ip:index_package) (#key_length:(n:nat{n<=32})) (#key_type:(inst_id -> Type0)) (#kp:key_package ip key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (h0:mem) (h1:mem) =
  let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
  let both_honest = honest ip i in
  ((both_honest /\ Flags.prf_odh) ==>
    (match MM.sel (sel h0 op.kp_log) i with
    | Some _ ->
      modifies Set.empty h0 h1
    | None ->
      modifies (Set.singleton op.kp_log_rgn) h0 h1))
  /\ ((~both_honest \/ ~Flags.prf_odh) ==>
      modifies Set.empty h0 h1)

let dh_op_log_change (#ip:index_package) (#key_length:(n:nat{n<=32})) (#key_type:(inst_id -> Type0)) (#kp:key_package ip key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (h0:mem) (h1:mem) =
  let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
  let both_honest = honest ip i in
  contains h0 op.kp_log
  /\ ((both_honest /\ Flags.prf_odh) ==>
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
  /\ ((~both_honest \/ ~Flags.prf_odh) ==>
      sel h1 op.kp_log == sel h0 op.kp_log)

// Do we need/want this?
let dh_op_functional_spec (#ip:index_package) (#key_length:(n:nat{n<=32})) (#key_type:(inst_id -> Type0)) (#kp:key_package ip key_length key_type) (#oparam:odh_parameters{oparam.hash_length = key_length}) (op:odh_package kp oparam) (sh:share oparam) (exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh}) (k:key_type (compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh))) (h1:mem) =
  let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
  let both_honest = honest ip i in
    ((Flags.prf_odh /\ both_honest) ==>
        (Some? (MM.sel (sel h1 op.kp_log) i)
        /\ k == Some?.v (MM.sel (sel h1 op.kp_log) i)
        /\ honest ip i
      )) // If possible, indicate somehow that k was randomly drawn.
    /\ (~Flags.prf_odh ==>
        kp.getGT k == oparam.hash (oparam.exponentiate exp.raw_exp sh.raw_sh)
        /\ (both_honest ==> honest ip i)
        /\ ~both_honest ==> dishonest ip i)


#set-options "--z3rlimit 300 --max_ifuel 2 --max_fuel 1"
val dh_op: (#ip:index_package) ->  (#key_length:(n:nat{n<=32})) -> (#key_type:(inst_id -> Type0)) -> (#kp:key_package ip key_length key_type) -> (#oparam:odh_parameters{oparam.hash_length = key_length}) -> op:odh_package kp oparam -> sh:share oparam -> exp:exponent oparam{exp.sh.raw_sh <> sh.raw_sh} -> ST (key_type (compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh)))
  (requires (fun h0 ->
    let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
    (kp.flag ==> Flags.prf_odh)
    /\ registered ip i
  ))
  (ensures (fun h0 k h1 ->
    let i = compose_id (PK_id sh.raw_sh) (PK_id exp.sh.raw_sh) in
    let both_honest = honest ip i in
    dh_op_memory_footprint op sh exp h0 h1
    /\ dh_op_log_change op sh exp h0 h1
    /\ dh_op_functional_spec op sh exp k h1
  ))
