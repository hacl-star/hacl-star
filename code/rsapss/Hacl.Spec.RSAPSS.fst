module Hacl.Spec.RSAPSS

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

open Hacl.Spec.Bignum.Definitions
open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Exponentiation

module S = Spec.RSAPSS
module BSeq = Lib.ByteSequence
module Hash = Spec.Agile.Hash

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val em_blocks_lt_max_size_t: modBits:size_pos{1 < modBits} -> Lemma
  (requires 128 * blocks modBits 64 <= max_size_t)
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
  (requires 128 * blocks modBits 64 <= max_size_t)
  (ensures  blocks (blocks modBits 8) 8 == blocks modBits 64)
let sgnt_blocks_eq_nLen modBits = ()


val rsapss_sign_inv:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos
  -> dBits:size_pos{blocks modBits 64 + blocks eBits 64 + blocks dBits 64 <= max_size_t}
  -> skey:lbignum (blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen -> Type0

let rsapss_sign_inv a modBits eBits dBits skey sLen salt msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\ sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  sLen + Hash.hash_length a + 2 <= (blocks (modBits - 1) 8) /\ msgLen <= Hash.max_input_length a /\

  128 * blocks modBits 64 <= max_size_t /\
 (let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n = bn_v (sub skey 0 nLen) in
  let e = bn_v (sub skey nLen eLen) in
  let d = bn_v (sub skey (nLen + eLen) dLen) in
  n % 2 = 1 /\
  pow2 (modBits - 1) < n /\ n < pow2 modBits /\
  0 < e /\ e < pow2 eBits /\
  0 < d /\ d < pow2 dBits)


val rsapss_sign:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos
  -> dBits:size_pos{blocks modBits 64 + blocks eBits 64 + blocks dBits 64 <= max_size_t}
  -> skey:lbignum (blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen
  -> Pure (lseq uint8 (blocks modBits 8))
  (requires rsapss_sign_inv a modBits eBits dBits skey sLen salt msgLen msg)
  (ensures  fun sgnt -> True)

let rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n = sub skey 0 nLen in
  let d = sub skey (nLen + eLen) dLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode #a salt msg emBits in
  em_blocks_lt_max_size_t modBits;
  assert (8 * blocks emLen 8 <= max_size_t);
  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (u64 0) in
  let m = update_sub m 0 (blocks emLen 8) emNat in

  let s = bn_mod_exp modBits nLen n m dBits d in
  sgnt_blocks_eq_nLen modBits;
  assert (blocks k 8 == nLen);
  let sgnt = bn_to_bytes_be k s in
  sgnt


val rsapss_sign_lemma:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos
  -> dBits:size_pos{blocks modBits 64 + blocks eBits 64 + blocks dBits 64 <= max_size_t}
  -> skey:lbignum (blocks modBits 64 + blocks eBits 64 + blocks dBits 64)
  -> sLen:size_nat
  -> salt:lseq uint8 sLen
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen -> Lemma
  (requires
    rsapss_sign_inv a modBits eBits dBits skey sLen salt msgLen msg)
  (ensures
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in
    let dLen = blocks dBits 64 in

    let n = bn_v (sub skey 0 nLen) in
    let e = bn_v (sub skey nLen eLen) in
    let d = bn_v (sub skey (nLen + eLen) dLen) in
    let pkeys : S.rsa_pubkey modBits = S.Mk_rsa_pubkey n e in
    let skeys : S.rsa_privkey modBits = S.Mk_rsa_privkey pkeys d in
    let sgnt = rsapss_sign a modBits eBits dBits skey sLen salt msgLen msg in
    sgnt `Seq.equal` S.rsapss_sign #a #sLen #msgLen modBits skeys salt msg))

let rsapss_sign_lemma a modBits eBits dBits skey sLen salt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in
  let dLen = blocks dBits 64 in

  let n = sub skey 0 nLen in
  let e = sub skey nLen eLen in
  let d = sub skey (nLen + eLen) dLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  let em = S.pss_encode #a salt msg emBits in
  em_blocks_lt_max_size_t modBits;
  assert (8 * blocks emLen 8 <= max_size_t);

  let emNat = bn_from_bytes_be emLen em in
  let m = create nLen (u64 0) in
  let m = update_sub m 0 (blocks emLen 8) emNat in
  bn_eval_update_sub (blocks emLen 8) emNat nLen;
  assert (bn_v m == bn_v emNat);
  bn_from_bytes_be_lemma emLen em;
  S.os2ip_lemma emBits em;

  assert (bn_v m < bn_v n);
  let s = bn_mod_exp modBits nLen n m dBits d in
  Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
  bn_mod_exp_lemma modBits nLen n m dBits d;

  sgnt_blocks_eq_nLen modBits;
  assert (blocks k 8 == nLen);
  Math.Lemmas.pow2_le_compat (8 * k) modBits;
  assert (bn_v s < pow2 (8 * k));
  let sgnt = bn_to_bytes_be k s in
  bn_to_bytes_be_lemma k s


val bn_eval_lt_pow2_modBits: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_v m == (bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1))

let bn_eval_lt_pow2_modBits modBits m =
  calc (==) {
    bn_v m;
    (==) { Math.Lemmas.euclidean_division_definition (bn_v m) (pow2 (modBits - 1)) }
    bn_v m / pow2 (modBits - 1) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.euclidean_division_definition (bn_v m / pow2 (modBits - 1)) 2 }
    (bn_v m / pow2 (modBits - 1) / 2 * 2 + bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v m) (pow2 (modBits - 1)) 2; Math.Lemmas.pow2_plus (modBits - 1) 1}
    (bn_v m / pow2 modBits * 2 + bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    (==) { Math.Lemmas.small_division_lemma_1 (bn_v m) (pow2 modBits) }
    (bn_v m / pow2 (modBits - 1) % 2) * pow2 (modBits - 1) + bn_v m % pow2 (modBits - 1);
    }


val bn_is_less_pow2: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> bool
let bn_is_less_pow2 modBits m =
  if (modBits - 1) % 8 <> 0 then true
  else FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (bn_get_ith_bit m (modBits - 1)) =^ 0uL)

val bn_is_less_pow2_lemma: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 modBits)
  (ensures  bn_is_less_pow2 modBits m == (bn_v m < pow2 (8 * blocks (modBits - 1) 8)))

let bn_is_less_pow2_lemma modBits m =
  let k = blocks modBits 8 in
  let emLen = blocks (modBits - 1) 8 in
  let mLen = blocks emLen 8 in
  let nLen = blocks k 8 in
  assert (nLen == blocks modBits 64);

  if (modBits - 1) % 8 <> 0 then Math.Lemmas.pow2_le_compat (8 * emLen) modBits
  else begin
    assert (k == emLen + 1);
    bn_eval_unfold_i m nLen;
    assert (8 * k == modBits + 7);
    assert (8 * emLen == modBits - 1);

    bn_eval_lt_pow2_modBits modBits m;
    let r = FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 (bn_get_ith_bit m (modBits - 1)) =^ 0uL) in
    bn_get_ith_bit_lemma m (modBits - 1) end


val bn_eval_sub: modBits:size_pos{1 < modBits} -> m:lbignum (blocks modBits 64) -> Lemma
  (requires bn_v m < pow2 (8 * blocks (modBits - 1) 8))
  (ensures  bn_v m == bn_v (sub m 0 (blocks (blocks (modBits - 1) 8) 8)))

let bn_eval_sub modBits m =
  let emLen = blocks (modBits - 1) 8 in
  let mLen = blocks emLen 8 in
  let nLen = blocks modBits 64 in
  assert (bn_v m < pow2 (8 * emLen));
  let m1 = sub m 0 mLen in
  bn_eval_split_i m mLen;
  assert (bn_v m == bn_v m1 + pow2 (64 * mLen) * bn_v (slice m mLen nLen));
  bn_eval_bound m1 mLen;
  assert (bn_v m1 < pow2 (64 * mLen));
  Math.Lemmas.pow2_le_compat (64 * mLen) (8 * emLen)


val rsapss_verify_inv:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos{blocks modBits 64 + blocks eBits 64 <= max_size_t}
  -> pkey:lbignum (blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen -> Type0

let rsapss_verify_inv a modBits eBits pkey sLen sgnt msgLen msg =
  sLen + Hash.hash_length a + 8 <= max_size_t /\ sLen + Hash.hash_length a + 8 <= Hash.max_input_length a /\
  msgLen <= Hash.max_input_length a /\

  128 * blocks modBits 64 <= max_size_t /\
 (let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n = bn_v (sub pkey 0 nLen) in
  let e = bn_v (sub pkey nLen eLen) in
  n % 2 = 1 /\
  pow2 (modBits - 1) < n /\ n < pow2 modBits /\
  0 < e /\ e < pow2 eBits)


val rsapss_verify:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos{blocks modBits 64 + blocks eBits 64 <= max_size_t}
  -> pkey:lbignum (blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen ->
  Pure bool
  (requires rsapss_verify_inv a modBits eBits pkey sLen sgnt msgLen msg)
  (ensures  fun r -> True)

let rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg =
  let nLen = blocks modBits 64 in
  let eLen = blocks eBits 64 in

  let n = sub pkey 0 nLen in
  let e = sub pkey nLen eLen in

  let k = blocks modBits 8 in
  let emBits = modBits - 1 in
  let emLen = blocks emBits 8 in

  sgnt_blocks_eq_nLen modBits;
  assert (blocks k 8 == nLen);
  let s = bn_from_bytes_be k sgnt in

  let mask = bn_lt_mask s n in
  if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB) then begin
    let m = bn_mod_exp modBits nLen n s eBits e in
    em_blocks_lt_max_size_t modBits;
    assert (8 * blocks emLen 8 <= max_size_t);

    if bn_is_less_pow2 modBits m then begin
      let m1 = sub m 0 (blocks emLen 8) in
      let em = bn_to_bytes_be emLen m1 in
      S.pss_verify #a sLen msg emBits em end
    else false end
  else false


val rsapss_verify_lemma:
    a:Hash.algorithm{S.hash_is_supported a}
  -> modBits:size_pos{1 < modBits}
  -> eBits:size_pos{blocks modBits 64 + blocks eBits 64 <= max_size_t}
  -> pkey:lbignum (blocks modBits 64 + blocks eBits 64)
  -> sLen:size_nat //saltLen
  -> sgnt:lseq uint8 (blocks modBits 8)
  -> msgLen:size_nat
  -> msg:lseq uint8 msgLen -> Lemma
  (requires
    rsapss_verify_inv a modBits eBits pkey sLen sgnt msgLen msg)
  (ensures
   (let nLen = blocks modBits 64 in
    let eLen = blocks eBits 64 in

    let n = bn_v (sub pkey 0 nLen) in
    let e = bn_v (sub pkey nLen eLen) in
    let pkeys : S.rsa_pubkey modBits = S.Mk_rsa_pubkey n e in
    rsapss_verify a modBits eBits pkey sLen sgnt msgLen msg ==
    S.rsapss_verify #a #msgLen modBits pkeys sLen msg sgnt))

let rsapss_verify_lemma a modBits eBits pkey sLen sgnt msgLen msg =
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

  let mask = bn_lt_mask s n in
  bn_lt_mask_lemma s n;
  let res =
  if FStar.UInt64.(Lib.RawIntTypes.u64_to_UInt64 mask =^ ones U64 PUB) then begin
    let m = bn_mod_exp modBits nLen n s eBits e in
    Math.Lemmas.pow2_le_compat (64 * nLen) modBits;
    bn_mod_exp_lemma modBits nLen n s eBits e;
    em_blocks_lt_max_size_t modBits;
    assert (8 * blocks emLen 8 <= max_size_t);

    bn_is_less_pow2_lemma modBits m;
    if bn_is_less_pow2 modBits m then begin
      let m1 = sub m 0 (blocks emLen 8) in
      bn_eval_sub modBits m;
      assert (bn_v m1 == bn_v m);
      let em = bn_to_bytes_be emLen m1 in
      bn_to_bytes_be_lemma emLen m1;
      S.pss_verify #a sLen msg emBits em end
    else false end
  else false in
  ()
