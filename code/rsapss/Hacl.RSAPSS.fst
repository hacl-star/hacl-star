module Hacl.RSAPSS

module S = Spec.RSAPSS
module Hash = Spec.Agile.Hash

module IR = Hacl.Impl.RSAPSS

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val rsapss_sign: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_sign_st a
let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt =
  IR.rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg sgnt

val rsapss_verify: a:Hash.algorithm{S.hash_is_supported a} -> IR.rsapss_verify_st a
let rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg =
  IR.rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg


val new_rsapss_load_pkey: IR.new_rsapss_load_pkey_st
let new_rsapss_load_pkey r modBits eBits nb eb =
  IR.new_rsapss_load_pkey r modBits eBits nb eb

val new_rsapss_load_skey: IR.new_rsapss_load_skey_st
let new_rsapss_load_skey r modBits eBits dBits nb eb db =
  IR.new_rsapss_load_skey r modBits eBits dBits nb eb db
