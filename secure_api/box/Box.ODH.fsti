module Box.ODH

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Box.Index
open Box.Key

open FStar.Endianness

module MM = FStar.Monotonic.Map

let n32 = n:nat{n<=32}

val random_bytes: n:n32 -> lbytes n

noeq type odh_parameters =
  | OP:
  share_length:(n:n32) ->
  exponent_length:(n:n32) ->
  hash_length:(n:n32) ->
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

let odh_index_package (oparams:odh_parameters) = ip:index_package{
  Leaf_IP? ip
  /\ (match ip with
    | Leaf_IP t rgn log -> t == lbytes oparams.share_length)
  }

val create_odh_index_package: rgn:erid -> oparams:odh_parameters -> ST (odh_index_package oparams)
  (requires (fun h0 -> True))
  (ensures (fun h0 ip h1 ->
    create_leaf_index_package_footprint rgn (lbytes oparams.share_length) ip h0 h1
  ))

val gen_dh_footprint: #oparams:odh_parameters -> ip:odh_index_package oparams -> h0:mem -> h1:mem -> Type0

val gen_dh: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> ST (dh_keypair:(exponent oparams*share oparams))
  (requires (fun h0 ->
    Flags.model))
  (ensures (fun h0 dh_pair h1 ->
    let e,sh = dh_pair in
    let i:id ip = sh.raw_sh in
    e.sh == sh
    /\ registered i
    /\ honest i
    /\ gen_dh_footprint #oparams ip h0 h1
  ))

val coerce_dh_sh_footprint: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> (raw_sh:lbytes oparams.share_length) -> h0:mem -> h1:mem -> Type0

val coerce_dh_sh: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> (raw_sh:lbytes oparams.share_length) -> ST (sh:share oparams{sh.raw_sh = raw_sh})
  (requires (fun h0 ->
    registered #ip raw_sh
    /\ corrupt #ip raw_sh
  ))
  (ensures (fun h0 sh h1 ->
    coerce_dh_sh_footprint #oparams ip raw_sh h0 h1
  ))

val coerce_dh_exp_footprint: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> (raw_exp:lbytes oparams.exponent_length) -> h0:mem -> h1:mem -> Type0

val coerce_dh_exp: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> (raw_exp:lbytes oparams.exponent_length) -> ST (exp:exponent oparams{exp.raw_exp = raw_exp})
  (requires (fun h0 ->
    let raw_sh = oparams.exponentiate raw_exp oparams.generator in
    registered #ip raw_sh
    /\ corrupt #ip raw_sh
  ))
  (ensures (fun h0 sh h1 ->
    let raw_sh = oparams.exponentiate raw_exp oparams.generator in
    coerce_dh_exp_footprint #oparams ip raw_exp h0 h1
  ))

let key_log_key (ip:index_package) = id ip
let key_log_value (ip:index_package) (i:id ip) (key_type:(id ip -> Type0)) = key_type i
let key_log_range (ip:index_package) (key_type:(id ip -> Type0)) (k:key_log_key ip) = key_log_value ip k key_type
let key_log_inv (ip:index_package) (key_type:(id ip -> Type0)) (f:MM.map' (key_log_key ip) (key_log_range ip key_type)) = True

let i_key_log (rgn:erid) (ip:index_package) (key_type:(id ip -> Type0)) =
    MM.t rgn (key_log_key ip) (key_log_range ip key_type) (key_log_inv ip key_type)

let key_log (rgn:erid) (ip:index_package) (key_type:(id ip -> Type0)) =
  if Flags.model then
    i_key_log rgn ip key_type
  else
    unit

let empty_key_log (ip:index_package) (key_type:(id ip -> Type0)) = MM.empty_map (key_log_key ip) (key_log_range ip key_type)

let composed_ip (ip:index_package) = Node_IP [ip;ip]

let key_package (ip:index_package) (oparams:odh_parameters) = kp:key_package ip {kp.key_length = oparams.hash_length}

noeq abstract type odh_package (#oparams:odh_parameters) (ip:odh_index_package oparams) (kp:key_package (composed_ip ip) oparams) =
  | ODH:
  log_rgn:erid ->
  log:key_log log_rgn (composed_ip ip) kp.key_type ->
  odh_package #oparams ip kp

val get_op_rgn: (#oparams:odh_parameters) -> (#ip:odh_index_package oparams) -> (#kp:key_package (composed_ip ip) oparams) -> op:odh_package ip kp -> (rgn:erid{rgn = op.log_rgn})

val get_op_log: (#oparams:odh_parameters) -> (#ip:odh_index_package oparams) -> (#kp:key_package (composed_ip ip) oparams) -> op:odh_package ip kp -> GTot (log:key_log op.log_rgn (composed_ip ip) kp.key_type)

val recall_op_log: (#oparams:odh_parameters) -> (#ip:odh_index_package oparams) -> (#kp:key_package (composed_ip ip) oparams) -> op:odh_package ip kp -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    (Flags.model ==>
      (let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
      contains h1 log))
    /\ h0 == h1
  ))

val create_odh_package: (#oparams:odh_parameters) -> (ip:odh_index_package oparams) -> (rgn:erid) -> (kp:key_package (composed_ip ip) oparams) -> ST (odh_package #oparams ip kp)
  (requires (fun h0 -> True))
  (ensures (fun h0 op h1 ->
    if Flags.model then
      let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
      modifies (Set.singleton op.log_rgn) h0 h1
      /\ extends op.log_rgn rgn
      /\ sel h1 log == empty_key_log (composed_ip ip) kp.key_type
      /\ contains h1 log
    else
      modifies_none h0 h1
  ))

let composed_id (#oparams:odh_parameters) (sh1:share oparams) (sh2:share oparams{
    sh1.raw_sh <> sh2.raw_sh
  }) =
  let le_sh1 = little_endian sh1.raw_sh in
  let le_sh2 = little_endian sh2.raw_sh in
  if le_sh1 < le_sh2 then
    sh1.raw_sh,sh2.raw_sh
  else
    sh2.raw_sh,sh1.raw_sh

let dh_op_memory_footprint
  (#oparams:odh_parameters)
  (#ip:odh_index_package oparams)
  (#kp:key_package (composed_ip ip) oparams)
  (op:odh_package ip kp)
  (sh:share oparams)
  (exp:exponent oparams{
    exp.sh.raw_sh <> sh.raw_sh
  })
  (h0:mem)
  (h1:mem) =
  let i:id (composed_ip ip) = composed_id sh exp.sh in
  let both_honest = honest i in
  ((both_honest /\ Flags.prf_odh) ==>
    (let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
    match MM.sel (sel h0 log) i with
    | Some _ ->
      modifies Set.empty h0 h1
    | None ->
      modifies (Set.singleton op.log_rgn) h0 h1))
  /\ ((~both_honest \/ ~Flags.prf_odh) ==>
      modifies Set.empty h0 h1)

let dh_op_log_change
  (#oparams:odh_parameters)
  (#ip:odh_index_package oparams)
  (#kp:key_package (composed_ip ip) oparams)
  (op:odh_package ip kp)
  (sh:share oparams)
  (exp:exponent oparams{
    exp.sh.raw_sh <> sh.raw_sh
  })
  (h0:mem)
  (h1:mem) =
  let i:id (composed_ip ip) = composed_id sh exp.sh in
  let both_honest = honest i in
  if Flags.model then
    (let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
    contains h0 log
    /\ ((both_honest /\ Flags.prf_odh) ==>
        (MM.defined log i h0 ==>
          Some? (sel h1 log i)
          /\ (let k = Some?.v (sel h1 log i) in
            sel h1 log == sel h0 log
          /\ witnessed (MM.contains log i k)))
        /\ (MM.fresh log i h0 ==>
            Some? (sel h1 log i)
            /\ (let k = Some?.v (sel h1 log i) in
            witnessed (MM.contains log i k)
            /\ sel h1 log == MM.upd (sel h0 log) i k))
      ))
  else
    True

// Do we need/want this?
let dh_op_functional_spec
  (#oparams:odh_parameters)
  (#ip:odh_index_package oparams)
  (#kp:key_package (composed_ip ip) oparams)
  (op:odh_package ip kp)
  (sh:share oparams)
  (exp:exponent oparams{
    exp.sh.raw_sh <> sh.raw_sh
  })
  (k:kp.key_type (composed_id sh exp.sh))
  (h1:mem) =
  let i:id (composed_ip ip) = composed_id sh exp.sh in
  let both_honest = honest i in
    ((Flags.prf_odh /\ both_honest) ==>
        (let log:i_key_log op.log_rgn (composed_ip ip) kp.key_type = op.log in
        Some? (MM.sel (sel h1 log) i)
        /\ k == Some?.v (MM.sel (sel h1 log) i)
        /\ honest i
      )) // If possible, indicate somehow that k was randomly drawn.
    /\ (~Flags.prf_odh ==>
        kp.getGT k == oparams.hash (oparams.exponentiate exp.raw_exp sh.raw_sh)
        /\ (both_honest ==> honest i)
        /\ ~both_honest ==> corrupt i)

#set-options "--z3rlimit 50 --max_ifuel 2 --max_fuel 2"
val dh_op:
  (#oparams:odh_parameters) ->
  (#ip:odh_index_package oparams) ->
  (#kp:key_package (composed_ip ip) oparams) ->
  (op:odh_package ip kp) ->
  (sh:share oparams) ->
  (exp:exponent oparams{exp.sh.raw_sh <> sh.raw_sh}) ->
  ST (kp.key_type (composed_id sh exp.sh))
    (requires (fun h0 ->
      let i:id (composed_ip ip) = composed_id sh exp.sh in
      (kp.flag ==> Flags.prf_odh)
      /\ registered #(composed_ip ip) i
    ))
    (ensures (fun h0 k h1 ->
      let i:id (composed_ip ip) = composed_id sh exp.sh in
      let both_honest = honest #(composed_ip ip) i in
      dh_op_memory_footprint op sh exp h0 h1
      /\ dh_op_log_change op sh exp h0 h1
      /\ dh_op_functional_spec op sh exp k h1
    ))
