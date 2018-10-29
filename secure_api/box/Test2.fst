module Test2

open FStar.Endianness

let n32 = n:nat{n <= 32}

assume val exp_fun: lbytes 32 -> lbytes 32 -> lbytes 32

noeq type odh_parameters =
  | OP:
  share_length:(n:n32) ->
  exponentiate:(lbytes share_length -> lbytes share_length -> lbytes share_length) ->
  odh_parameters

abstract type share (oparam:odh_parameters) =
  | SH:
  raw_sh:lbytes oparam.share_length ->
  share oparam

val get_share_raw: #oparams:odh_parameters -> sh:share oparams -> raw:lbytes oparams.share_length{raw = sh.raw_sh}
let get_share_raw #oparams sh = sh.raw_sh
