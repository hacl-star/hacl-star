module Spec.RSA

open FStar.Mul
open Lib.IntTypes

open Lib.NatMod
open Lib.Sequence
open Lib.ByteSequence
open Lib.LoopCombinators

module Hash = Spec.Agile.Hash

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(**
 This spec defines the raw RSA cryptosystem.
 It should be use in combination with an encoding format like PSS (for signatures) or OAEP (for encryption)
*)

///
/// Auxillary functions
///

val blocks: x:size_pos -> m:size_pos -> Tot (r:size_pos{x <= m * r})
let blocks x m = (x - 1) / m + 1

val xor_bytes: #len:size_pos -> b1:lbytes len -> b2:lbytes len -> Tot (lbytes len)
let xor_bytes #len b1 b2 = map2 (fun x y -> x ^. y) b1 b2

(* Bignum convert functions *)
val os2ip: #len:size_nat -> b:lbytes len -> Tot (res:nat{res < pow2 (8 * len)})
let os2ip #len b = nat_from_bytes_be b

val i2osp: len:size_nat -> n:nat{n < pow2 (8 * len)} -> Tot (lbytes len)
let i2osp len n = nat_to_intseq_be len n

///
///  RSA
///

type modBits_t = modBits:size_nat{1 < modBits}

noeq type rsa_pkey (modBits:modBits_t) =
  | Mk_rsa_pkey: n:pos{pow2 (modBits - 1) < n /\ n < pow2 modBits} -> e:pos -> rsa_pkey modBits

noeq type rsa_skey (modBits:modBits_t) =
  | Mk_rsa_skey: pkey:rsa_pkey modBits -> d:pos -> rsa_skey modBits


val rsa_dec_skey:
    modBits:modBits_t
  -> skey:rsa_skey modBits
  -> cipher:lbytes (blocks modBits 8) ->
  tuple2 bool (lbytes (blocks modBits 8))

let rsa_dec_skey modBits skey cipher =
  let pkey = Mk_rsa_skey?.pkey skey in
  let n = Mk_rsa_pkey?.n pkey in
  let e = Mk_rsa_pkey?.e pkey in
  let d = Mk_rsa_skey?.d skey in

  let k = blocks modBits 8 in
  FStar.Math.Lemmas.pow2_le_compat (8 * k) modBits;

  let c = os2ip #k cipher in
  if c < n then 
    begin
    let m = pow_mod #n c d in
    let c' = pow_mod #n m e in
    let eq_c = c = c' in
    let o = if eq_c then m else 0 in
    (eq_c, i2osp k o)
    end
  else (false, i2osp k 0)


val rsa_enc_pkey:
    modBits:modBits_t
  -> pkey:rsa_pkey modBits
  -> msg:lbytes (blocks modBits 8)
  -> tuple2 bool (lbytes (blocks modBits 8))

let rsa_enc_pkey modBits pkey msg =
  let n = Mk_rsa_pkey?.n pkey in
  let e = Mk_rsa_pkey?.e pkey in
  let k = blocks modBits 8 in
  FStar.Math.Lemmas.pow2_le_compat (8 * k) modBits;

  let m = os2ip #k msg in
  if m < n then begin
    let c = pow_mod #n m e in
    if c < pow2 (8*k) then
      let ec = i2osp k c in
      (true,ec)
    else (false,i2osp k 0)
    end
  else (false,i2osp k 0)


val rsa_load_pkey:
    modBits:modBits_t
  -> eBits:size_pos
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8) ->
  option (rsa_pkey modBits)

let rsa_load_pkey modBits eBits nb eb =
  let n = os2ip #(blocks modBits 8) nb in
  let e = os2ip #(blocks eBits 8) eb in

  //`n % 2 = 1` is needed to store `r2 = r * r % n` as a part of pkey
  if (n % 2 = 1 && pow2 (modBits - 1) < n && n < pow2 modBits &&
      0 < e && e < pow2 eBits) then
    Some (Mk_rsa_pkey n e)
  else
    None


val rsa_load_skey:
    modBits:modBits_t
  -> eBits:size_pos
  -> dBits:size_pos
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8) ->
  option (rsa_skey modBits)

let rsa_load_skey modBits eBits dBits nb eb db =
  let pkey = rsa_load_pkey modBits eBits nb eb in
  let d = os2ip #(blocks dBits 8) db in

  if (Some? pkey && 0 < d && d < pow2 dBits) then
    Some (Mk_rsa_skey (Some?.v pkey) d)
  else
    None


val rsa_dec:
    modBits:modBits_t
  -> eBits:size_pos
  -> dBits:size_pos
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> db:lseq uint8 (blocks dBits 8)
  -> cipher:lbytes (blocks modBits 8) ->
  tuple2 bool (lbytes (blocks modBits 8))

let rsa_dec modBits eBits dBits nb eb db cipher =
  match rsa_load_skey modBits eBits dBits nb eb db with
  | Some sk ->
    rsa_dec_skey modBits sk cipher
  | None ->
    (false, create (blocks modBits 8) (uint 0))


val rsa_enc:
    modBits:modBits_t
  -> eBits:size_pos
  -> nb:lseq uint8 (blocks modBits 8)
  -> eb:lseq uint8 (blocks eBits 8)
  -> msg:lbytes (blocks modBits 8) ->
  tuple2 bool (lbytes (blocks modBits 8))

let rsa_enc modBits eBits nb eb msg =
  match rsa_load_pkey modBits eBits nb eb with
  | Some pk ->
    rsa_enc_pkey modBits pk msg
  | None ->
    (false, create (blocks modBits 8) (uint 0))


