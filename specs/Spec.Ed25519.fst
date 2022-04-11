module Spec.Ed25519

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Curve25519

module LE = Lib.Exponentiation
module SE = Spec.Exponentiation
module EL = Spec.Ed25519.Lemmas

include Spec.Ed25519.PointOps

#reset-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction
let size_signature: size_nat = 64

let q: n:nat{n < pow2 256} =
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 < pow2 255 - 19);
  (pow2 252 + 27742317777372353535851937790883648493) // Group order

let max_input_length_sha512 = Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_512
let _: squash(max_input_length_sha512 > pow2 32 + 64) =
  assert_norm (max_input_length_sha512 > pow2 32 + 64)

let sha512_modq (len:nat{len <= max_input_length_sha512}) (s:bytes{length s = len}) : n:nat{n < pow2 256} =
  nat_from_bytes_le (Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512 s) % q

///  Point Multiplication

let aff_point_c = p:aff_point{is_on_curve p}
let aff_point_add_c (p:aff_point_c) (q:aff_point_c) : aff_point_c =
  EL.aff_point_add_lemma p q;
  aff_point_add p q

let mk_ed25519_comm_monoid: LE.comm_monoid aff_point_c = {
  LE.one = aff_point_at_infinity;
  LE.mul = aff_point_add_c;
  LE.lemma_one = EL.aff_point_at_infinity_lemma;
  LE.lemma_mul_assoc = EL.aff_point_add_assoc_lemma;
  LE.lemma_mul_comm = EL.aff_point_add_comm_lemma;
  }

let ext_point_c = p:ext_point{point_inv p}
let mk_to_ed25519_comm_monoid : SE.to_comm_monoid ext_point_c = {
  SE.a_spec = aff_point_c;
  SE.comm_monoid = mk_ed25519_comm_monoid;
  SE.refl = (fun (x:ext_point_c) -> to_aff_point x);
  }

val point_at_inifinity_c: SE.one_st ext_point_c mk_to_ed25519_comm_monoid
let point_at_inifinity_c _ =
  EL.to_aff_point_at_infinity_lemma ();
  point_at_infinity

val point_add_c: SE.mul_st ext_point_c mk_to_ed25519_comm_monoid
let point_add_c p q =
  EL.to_aff_point_add_lemma p q;
  point_add p q

val point_double_c: SE.sqr_st ext_point_c mk_to_ed25519_comm_monoid
let point_double_c p =
  EL.to_aff_point_double_lemma p;
  point_double p

let mk_ed25519_concrete_ops : SE.concrete_ops ext_point_c = {
  SE.to = mk_to_ed25519_comm_monoid;
  SE.one = point_at_inifinity_c;
  SE.mul = point_add_c;
  SE.sqr = point_double_c;
  }

// [a]P
let point_mul (a:lbytes 32) (p:ext_point_c) : ext_point_c =
  SE.exp_fw mk_ed25519_concrete_ops p 256 (nat_from_bytes_le a) 4

// [a1]P1 + [a2]P2
let point_mul_double (a1:lbytes 32) (p1:ext_point_c) (a2:lbytes 32) (p2:ext_point_c) : ext_point_c =
  SE.exp_double_fw mk_ed25519_concrete_ops p1 256 (nat_from_bytes_le a1) p2 (nat_from_bytes_le a2) 4

// [a]G
let point_mul_g (a:lbytes 32) : ext_point_c =
  EL.g_is_on_curve ();
  point_mul a g

// [a1]G + [a2]P
let point_mul_double_g (a1:lbytes 32) (a2:lbytes 32) (p:ext_point_c) : ext_point_c =
  EL.g_is_on_curve ();
  point_mul_double a1 g a2 p

// [a1]G - [a2]P
let point_negate_mul_double_g (a1:lbytes 32) (a2:lbytes 32) (p:ext_point_c) : ext_point_c =
  let p1 = point_negate p in
  EL.to_aff_point_negate p;
  point_mul_double_g a1 a2 p1

///  Ed25519 API

let secret_expand (secret:lbytes 32) : (lbytes 32 & lbytes 32) =
  let h = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512 secret in
  let h_low : lbytes 32 = slice h 0 32 in
  let h_high : lbytes 32 = slice h 32 64 in
  let h_low = h_low.[ 0] <- h_low.[0] &. u8 0xf8 in
  let h_low = h_low.[31] <- (h_low.[31] &. u8 127) |. u8 64 in
  h_low, h_high


let secret_to_public (secret:lbytes 32) : lbytes 32 =
  let a, dummy = secret_expand secret in
  point_compress (point_mul_g a)


let expand_keys (secret:lbytes 32) : (lbytes 32 & lbytes 32 & lbytes 32) =
  let s, prefix = secret_expand secret in
  let pub = point_compress (point_mul_g s) in
  pub, s, prefix


val sign_expanded (pub s prefix:lbytes 32) (msg:bytes{length msg <= max_size_t}) : lbytes 64
let sign_expanded pub s prefix msg =
  let len = length msg in
  let r = sha512_modq (32 + len) (Seq.append prefix msg) in
  let r' = point_mul_g (nat_to_bytes_le 32 r) in
  let rs = point_compress r' in
  let h = sha512_modq (64 + len) (Seq.append (concat rs pub) msg) in
  let s = (r + (h * nat_from_bytes_le s) % q) % q in
  concat #_ #32 #32 rs (nat_to_bytes_le 32 s)


val sign: secret:lbytes 32 -> msg:bytes{length msg <= max_size_t} -> lbytes 64
let sign secret msg =
  let pub, s, prefix = expand_keys secret in
  sign_expanded pub s prefix msg


val verify: public:lbytes 32 -> msg:bytes{length msg <= max_size_t} -> signature:lbytes 64 -> bool
let verify public msg signature =
  let len = length msg in
  let a' = point_decompress public in
  match a' with
  | None -> false
  | Some a' -> (
    let rs = slice signature 0 32 in
    let r' = point_decompress rs in
    match r' with
    | None -> false
    | Some r' -> (
      let sb = slice signature 32 64 in
      if nat_from_bytes_le sb >= q then false
      else (
        let h = sha512_modq (64 + len) (Seq.append (concat rs public) msg) in
        let hb = nat_to_bytes_le 32 h in

        EL.point_decompress_lemma public;
        let exp_d = point_negate_mul_double_g sb hb a' in
        point_equal exp_d r'
      )
    )
  )
