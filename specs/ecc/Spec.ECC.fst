module Spec.ECC

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

module M = Lib.NatMod
module LE = Lib.Exponentiation
module PL = Spec.EC.Lemmas

include Spec.EC

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

///  Elliptic curve scalar multiplication

let mk_ec_comm_monoid (k:curve) : LE.comm_monoid (aff_point k) = {
  LE.one = aff_point_at_inf k;
  LE.mul = aff_point_add k;
  LE.lemma_one = PL.aff_point_at_inf_lemma k;
  LE.lemma_mul_assoc = PL.aff_point_add_assoc_lemma k;
  LE.lemma_mul_comm = PL.aff_point_add_comm_lemma k;
}

// [a]P in affine coordinates
let aff_point_mul (k:curve) (a:nat) (p:aff_point k) : aff_point k =
  LE.pow (mk_ec_comm_monoid k) p a

// TODO: add point_inv
inline_for_extraction
class ec_concrete_ops = {
  ec: curve;
  t: Type; // projective or jacobian
  to_point_t: aff_point ec -> t;
  to_aff_point: t -> aff_point ec;
  lemma_to_from_aff_point: p:aff_point ec -> Lemma (to_aff_point (to_point_t p) == p);
  is_point_at_inf: p:t -> res:bool{res ==> is_aff_point_at_inf ec (to_aff_point p)};
  point_mul: a:M.nat_mod ec.order -> p:t -> res:t
    { to_aff_point res == aff_point_mul ec a (to_aff_point p) };
  point_mul_double_g: a1:M.nat_mod ec.order -> a2:M.nat_mod ec.order -> p:t -> res:t
    { to_aff_point res ==
      aff_point_add ec
        (aff_point_mul ec a1 ec.base_point)
        (aff_point_mul ec a2 (to_aff_point p)) };
  }


let point_mul_g (k:ec_concrete_ops) (a:M.nat_mod k.ec.order)
  : res:k.t{to_aff_point res == aff_point_mul ec a k.ec.base_point}
 =
  k.lemma_to_from_aff_point k.ec.base_point;
  k.point_mul a (to_point_t k.ec.base_point)


let load_point (k:ec_concrete_ops) (b:lbytes (2 * k.ec.prime_len_bytes)) : option k.t =
  match (aff_point_load k.ec b) with
  | Some p -> Some (k.to_point_t p)
  | None -> None

let point_store (k:ec_concrete_ops) (p:k.t) : lbytes (2 * k.ec.prime_len_bytes) =
  aff_point_store k.ec (k.to_aff_point p)


///  ECDSA

let ecdsa_sign_msg_as_qelem
  (k:ec_concrete_ops) (m:qelem k.ec)
  (private_key nonce:lbytes k.ec.order_len_bytes)
  : option (lbytes (2 * k.ec.order_len_bytes))
 =
  let k_q = nat_from_bytes_be nonce in
  let d_a = nat_from_bytes_be private_key in
  let is_privkey_valid = 0 < d_a && d_a < k.ec.order in
  let is_nonce_valid = 0 < k_q && k_q < k.ec.order in

  if not (is_privkey_valid && is_nonce_valid) then None
  else begin
    let res = point_mul_g k k_q in
    let x = fst (to_aff_point res) in
    let r = x % k.ec.order in

    let kinv = qinv k.ec k_q in
    let s = qmul k.ec kinv (qadd k.ec m (qmul k.ec r d_a)) in
    let lenq = k.ec.order_len_bytes in
    let rb = nat_to_bytes_be lenq r in
    let sb = nat_to_bytes_be lenq s in
    if r = 0 || s = 0 then None
    else Some (concat #_ #lenq #lenq rb sb) end


let ecdsa_verify_msg_as_qelem
  (k:ec_concrete_ops) (m:qelem k.ec)
  (public_key:lbytes (2 * k.ec.prime_len_bytes))
  (sign_r sign_s:lbytes k.ec.order_len_bytes) : bool
 =
  let pk = load_point k public_key in
  let r = nat_from_bytes_be sign_r in
  let s = nat_from_bytes_be sign_s in
  let is_r_valid = 0 < r && r < k.ec.order in
  let is_s_valid = 0 < s && s < k.ec.order in

  if not (Some? pk && is_r_valid && is_s_valid) then false
  else begin
    let sinv = qinv k.ec s in
    let u1 = qmul k.ec sinv m in
    let u2 = qmul k.ec sinv r in
    let res = k.point_mul_double_g u1 u2 (Some?.v pk) in
    if k.is_point_at_inf res then false
    else begin
      let x = fst (k.to_aff_point res) in
      x % k.ec.order = r end
  end


///  ECDH

let secret_to_public
  (k:ec_concrete_ops) (private_key:lbytes k.ec.order_len_bytes)
  : option (lbytes (2 * k.ec.prime_len_bytes))
 =
  let sk = nat_from_bytes_be private_key in
  let is_sk_valid = 0 < sk && sk < k.ec.order in
  if is_sk_valid then
    let pk = point_mul_g k sk in
    Some (point_store k pk)
  else None


let ecdh
  (k:ec_concrete_ops) (their_public_key:lbytes (2 * k.ec.prime_len_bytes))
  (private_key:lbytes k.ec.order_len_bytes)
  : option (lbytes (2 * k.ec.prime_len_bytes))
 =
  let pk = load_point k their_public_key in
  let sk = nat_from_bytes_be private_key in
  let is_sk_valid = 0 < sk && sk < k.ec.order in
  if Some? pk && is_sk_valid then
    let ss = k.point_mul sk (Some?.v pk) in
    Some (point_store k ss)
  else None


///  Parsing and Serializing public keys

// raw          = [ x; y ], 2 * k.ec.prime_len_bytes
// uncompressed = [ 0x04; x; y ], 2 * k.ec.prime_len_bytes + 1
// compressed   = [ 0x02 for even `y` and 0x03 for odd `y`; x ], k.ec.prime_len_bytes + 1

let validate_public_key (k:ec_concrete_ops) (pk:lbytes (2 * k.ec.prime_len_bytes)) : bool =
  Some? (load_point k pk)


let pk_uncompressed_to_raw
  (k:ec_concrete_ops) (pk:lbytes (2 * k.ec.prime_len_bytes + 1))
  : option (lbytes (2 * k.ec.prime_len_bytes))
 =
  if Lib.RawIntTypes.u8_to_UInt8 pk.[0] <> 0x04uy then None
  else Some (sub pk 1 (2 * k.ec.prime_len_bytes))


let pk_uncompressed_from_raw
  (k:ec_concrete_ops) (pk:lbytes (2 * k.ec.prime_len_bytes))
  : lbytes (2 * k.ec.prime_len_bytes + 1)
 =
  concat (create 1 (u8 0x04)) pk


let pk_compressed_from_raw
  (k:ec_concrete_ops) (pk:lbytes (2 * k.ec.prime_len_bytes))
  : lbytes (k.ec.prime_len_bytes + 1)
 =
  let len = k.ec.prime_len_bytes in
  let pk_x = sub pk 0 len in
  let pk_y = sub pk len len in
  let is_pk_y_odd = nat_from_bytes_be pk_y % 2 = 1 in // <==> pk_y % 2 = 1
  let pk0 = if is_pk_y_odd then u8 0x03 else u8 0x02 in
  concat (create 1 pk0) pk_x


// TODO: handle more cases
let fsqrt (k:curve{k.prime % 4 = 3}) (a:felem k) : felem k =
  M.pow_mod #k.prime a ((k.prime + 1) / 4)

let is_fodd (x:nat) : bool = x % 2 = 1

let recover_y (k:curve{k.prime % 4 = 3}) (x:felem k) (is_odd:bool) : option (felem k) =
  let y2 = fadd k (fadd k (fmul k (fmul k x x) x) (fmul k k.coeff_a x)) k.coeff_b in
  let y = fsqrt k y2 in
  if fmul k y y <> y2 then None
  else begin
    let y = if is_fodd y <> is_odd then (k.prime - y) % k.prime else y in
    Some y end


let aff_point_decompress (k:curve{k.prime % 4 = 3}) (s:lbytes (k.prime_len_bytes + 1))
  : option (aff_point k)
 =
  let s0 = Lib.RawIntTypes.u8_to_UInt8 s.[0] in
  if not (s0 = 0x02uy || s0 = 0x03uy) then None
  else begin
    let x = nat_from_bytes_be (sub s 1 k.prime_len_bytes) in
    let is_x_valid = x < k.prime in
    let is_y_odd = s0 = 0x03uy in

    if not is_x_valid then None
    else
      match (recover_y k x is_y_odd) with
      | Some y -> Some (x, y)
      | None -> None end


let pk_compressed_to_raw
  (k:ec_concrete_ops{k.ec.prime % 4 = 3}) (pk:lbytes (k.ec.prime_len_bytes + 1))
  : option (lbytes (2 * k.ec.prime_len_bytes))
 =
  let len = k.ec.prime_len_bytes in
  let pk_x = sub pk 1 len in
  match (aff_point_decompress k.ec pk) with
  | Some (x, y) -> Some (concat #_ #len #len pk_x (nat_to_bytes_be len y))
  | None -> None
