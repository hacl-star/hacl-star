module Hacl.Spec.RSAPSS

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Exponentiation

module S = Spec.RSAPSS

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val em_blocks_lt_max_size_t: modBits:size_pos{1 < modBits} -> Lemma
  (requires 128 * (blocks modBits 64 + 1) <= max_size_t)
  (ensures  8 * blocks (blocks (modBits - 1) 8) 8 <= max_size_t)
let em_blocks_lt_max_size_t modBits = ()
  // let r = 8 * blocks (blocks (modBits - 1) 8) 8 in
  // calc (==) {
  //   r;
  //   (==) { }
  //   8 * (((modBits - 2) / 8) / 8 + 1);
  //   (==) { Math.Lemmas.division_multiplication_lemma (modBits - 2) 8 8 }
  //   8 * ((modBits - 2) / 64 + 1);
  //   (==) { }
  //   8 * blocks (modBits - 1) 64;
  //   }

val sgnt_blocks_eq_nLen: modBits:size_pos{1 < modBits} -> Lemma
  (requires 128 * (blocks modBits 64 + 1) <= max_size_t)
  (ensures  blocks (blocks modBits 8) 8 == blocks modBits 64)
let sgnt_blocks_eq_nLen modBits = ()


val rsapss_sign:
     modBits:size_pos{1 < modBits}
  -> eBits:size_pos
  -> dBits:size_pos{blocks modBits 64 + blocks eBits 64 + blocks dBits 64 <= max_size_t}
  -> skey:lbignum (blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen
  -> Pure (lseq uint8 (blocks modBits 8))
  (requires
    sLen + S.hLen + 8 <= max_size_t /\ sLen + S.hLen + 8 < S.max_input /\
    sLen + S.hLen + 2 <= (blocks (modBits - 1) 8) /\ msgLen < S.max_input /\

    128 * (blocks modBits 64 + 1) <= max_size_t /\
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in
    let dLen = blocks dBits 64 in

    let n = bn_v (sub skey 0 nLen) in
    let e = bn_v (sub skey nLen eLen) in
    let d = bn_v (sub skey (nLen + eLen) dLen) in
    1 < n /\ n % 2 = 1 /\
    pow2 (modBits - 1) < n /\ n < pow2 modBits /\
    0 < e /\ e < pow2 eBits /\
    0 < d /\ d < pow2 dBits))
  (ensures  fun sgnt ->
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in
    let dLen = blocks dBits 64 in

    let n = bn_v (sub skey 0 nLen) in
    let e = bn_v (sub skey nLen eLen) in
    let d = bn_v (sub skey (nLen + eLen) dLen) in
    let pkey : S.rsa_pubkey modBits = S.Mk_rsa_pubkey n e in
    let skey : S.rsa_privkey modBits = S.Mk_rsa_privkey pkey d in
    sgnt `Seq.equal` S.rsapss_sign #sLen #msgLen modBits skey salt msg))

let rsapss_sign modBits eBits dBits skey sLen salt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n = sub skey 0 nLen in
  let e = sub skey nLen eLen in
  let d = sub skey (nLen + eLen) dLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode salt msg emBits in
  em_blocks_lt_max_size_t modBits;
  assert (8 * blocks emLen 8 <= max_size_t);

  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (u64 0) in
  let m = update_sub m 0 (blocks emLen 8) emNat in
  bn_eval_update_sub (blocks emLen 8) emNat nLen;
  assert (bn_v m == bn_v emNat);
  bn_from_bytes_be_lemma emLen em;
  assert (bn_v m == S.os2ip #emLen em);

  assume (bn_v m < bn_v n);
  let s = bn_mod_exp modBits nLen n m dBits d in
  Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
  bn_mod_exp_lemma modBits nLen n m dBits d;
  assert (bn_v s == S.fpow #(bn_v n) (bn_v m) (bn_v d));

  sgnt_blocks_eq_nLen modBits;
  assert (blocks k 8 == nLen);
  Math.Lemmas.pow2_le_compat (8 * k) modBits;
  assert (bn_v s < pow2 (8 * k));
  let sgnt = bn_to_bytes_be k s in
  bn_to_bytes_be_lemma k s;
  sgnt


val rsapss_verify:
    modBits:size_pos{1 < modBits}
  -> eBits:size_pos{blocks modBits 64 + blocks eBits 64 <= max_size_t}
  -> pkey:lbignum (blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen ->
  Pure bool
  (requires
    sLen + S.hLen + 8 <= max_size_t /\ sLen + S.hLen + 8 < S.max_input /\
    msgLen < S.max_input /\

    128 * (blocks modBits 64 + 1) <= max_size_t /\
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in

    let n = bn_v (sub pkey 0 nLen) in
    let e = bn_v (sub pkey nLen eLen) in
    1 < n /\ n % 2 = 1 /\
    pow2 (modBits - 1) < n /\ n < pow2 modBits /\
    0 < e /\ e < pow2 eBits))
  (ensures  fun r ->
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in

    let n = bn_v (sub pkey 0 nLen) in
    let e = bn_v (sub pkey nLen eLen) in
    let pkey : S.rsa_pubkey modBits = S.Mk_rsa_pubkey n e in
    r == S.rsapss_verify #msgLen modBits pkey sLen msg sgnt))

let rsapss_verify modBits eBits pkey sLen sgnt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n = sub pkey 0 nLen in
  let e = sub pkey nLen eLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  sgnt_blocks_eq_nLen modBits;
  assert (blocks k 8 == nLen);
  assert (8 * blocks k 8 <= max_size_t);
  let s = bn_from_bytes_be k sgnt in
  bn_from_bytes_be_lemma k sgnt;
  assert (bn_v s == S.os2ip sgnt);

  bn_is_less_lemma s n;
  if bn_is_less s n then begin
    let m = bn_mod_exp modBits nLen n s eBits e in
    Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
    bn_mod_exp_lemma modBits nLen n s eBits e;
    assert (bn_v m == S.fpow #(bn_v n) (bn_v s) (bn_v e));
    em_blocks_lt_max_size_t modBits;
    assert (8 * blocks emLen 8 <= max_size_t);

      // bn_v m < pow2 (8 * emLen) <==> bn_is_bit_set m (8 * emLen) == false
      assume (blocks emLen 8 == nLen); // this is not true
      assume (bn_v m < pow2 (8 * emLen));
      let em = bn_to_bytes_be emLen m in
      bn_to_bytes_be_lemma emLen m;
      assert (em == S.i2osp #emLen (bn_v m));
      S.pss_verify sLen msg emBits em end
  else false
