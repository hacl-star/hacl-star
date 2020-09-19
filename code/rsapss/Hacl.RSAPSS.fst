module Hacl.RSAPSS

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module IR = Hacl.Impl.RSAPSS
module IK = Hacl.Impl.RSAPSS.Keys

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val rsapss_sign: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_sign_st a
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  IR.rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt

val rsapss_verify: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_verify_st a
let rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg =
  IR.rsapss_verify a modBits eBits pkey sLen k sgnt msgLen msg

val new_rsapss_load_pkey: IK.new_rsapss_load_pkey_st
let new_rsapss_load_pkey r modBits eBits nb eb =
  IK.new_rsapss_load_pkey r modBits eBits nb eb

val new_rsapss_load_skey: IK.new_rsapss_load_skey_st
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  IK.new_rsapss_load_skey r modBits eBits dBits nb eb db

val rsapss_skey_sign: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_skey_sign_st a
let rsapss_skey_sign a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt =
  IR.rsapss_skey_sign a modBits eBits dBits nb eb db sLen salt msgLen msg sgnt

val rsapss_pkey_verify: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_pkey_verify_st a
let rsapss_pkey_verify a modBits eBits nb eb sLen k sgnt msgLen msg =
  IR.rsapss_pkey_verify a modBits eBits nb eb sLen k sgnt msgLen msg
