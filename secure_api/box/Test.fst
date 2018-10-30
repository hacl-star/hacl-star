module Test

open FStar.Endianness

module ODH = Test2
module ODH_Spec = Spec.Curve25519

#set-options "--z3rlimit 30 --max_ifuel 0 --max_fuel 0"

assume val id: int -> eqtype

let odh_params = ODH.OP 32 (ODH_Spec.scalarmult)

let pkey = ODH.share odh_params

val get_pkey_raw: pkey -> lbytes 32
let get_pkey_raw = ODH.get_share_raw #odh_params

assume val compose_ip : ip:int{id ip == lbytes 32 * lbytes 32}

let coerce (#a:Type) (#b:Type{a == b}) (x:a) : y:b{x == y} = x

val composed_id: pk1:pkey -> pk2:pkey -> id compose_ip
let composed_id pk1 pk2 =
  let pk1_raw = get_pkey_raw pk1 in
  let pk2_raw = get_pkey_raw pk2 in
  let le_sh1 = little_endian pk1_raw in
  let le_sh2 = little_endian pk2_raw in
  if le_sh1 < le_sh2 then
    coerce (pk1_raw, pk2_raw)
  else
    coerce (pk2_raw, pk1_raw)

abstract type protected_plain (#ip:int) (i:id ip) = bytes

let extended_message_log
  (ip:int)
  (pk1:pkey)
  (pk2:pkey)
  (p:protected_plain #compose_ip (composed_id pk1 pk2))
=
  let i : id (compose_ip) = composed_id pk1 pk2 in
  let log_value: protected_plain #compose_ip i = coerce p in
  True
