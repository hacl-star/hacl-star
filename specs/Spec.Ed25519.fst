module Spec.Ed25519

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes

open Spec.Curve25519

#reset-options "--max_fuel 0 --z3rlimit 100"

///
/// Constants
///

inline_for_extraction
let size_signature: size_nat = 64


type aff_point = elem & elem               // Affine point
type ext_point = elem & elem & elem & elem // Homogeneous extended coordinates

let modp_sqrt_m1 : elem = 2 **% ((prime - 1) / 4)

let d : elem =
  let x = 37095705934669439343138083508754565189542113879843219016388785533085940283555 in
  assert_norm(x < prime);
  x

let q: n:nat{n < pow2 256} =
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 < pow2 255 - 19);
  (pow2 252 + 27742317777372353535851937790883648493) // Group order

let _:_:unit{Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_512 > pow2 32} = assert_norm (Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_512 > pow2 32)

let g_x : elem = 15112221349535400772501151409588531511454012693041857206046113283949847762202
let g_y : elem = 46316835694926478169428394003475163141307993866256225615783033603165251855960

let g: ext_point = (g_x, g_y, 1, g_x *% g_y)

///
/// Internal functions
///

let modp_inv (x:elem) : Tot elem =
  x **% (prime - 2)

let sha512_modq (len:size_nat) (s:lbytes len) : n:nat{n < pow2 256} =
  nat_from_bytes_le (Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512 s) % q

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let x2, y2, z2, t2 = q in
  let a = (y1 -% x1) *% (y2 -% x2) in
  let b = (y1 +% x1) *% (y2 +% x2) in
  let c = (2 *% d *% t1) *% t2 in
  let d = (2 *% z1) *% z2 in
  let e = b -% a in
  let f = d -% c in
  let g = d +% c in
  let h = b +% a in
  let x3 = e *% f in
  let y3 = g *% h in
  let t3 = e *% h in
  let z3 = f *% g in
  (x3, y3, z3, t3)

let point_double (p:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let a = x1 *% x1 in
  let b = y1 *% y1 in
  let c = 2 *% (z1 *% z1) in
  let h = a +% b in
  let e = h -% ((x1 +% y1) *% (x1 +% y1)) in
  let g = a -% b in
  let f = c +% g in
  let x3 = e *% f in
  let y3 = g *% h in
  let t3 = e *% h in
  let z3 = f *% g in
  (x3, y3, z3, t3)

let ith_bit (k:lbytes 32) (i:size_nat{i < 256}) =
  let q = i / 8 in let r = size (i % 8) in
  (index #uint8 #32 k q >>. r) &. u8 1

let cswap2 (sw:uint8) (x:ext_point) (xp1:ext_point) =
  if uint_to_nat sw = 1 then (xp1, x) else (x, xp1)

let ladder_step (k:lbytes 32) (i:nat{i < 256}) (x, xp1) =
  let bit = ith_bit k (255 - i) in
  let x, xp1 = cswap2 bit x xp1 in
  let xx = point_double x in
  let xxp1 = point_add x xp1 in
  cswap2 bit xx xxp1

let montgomery_ladder (x:ext_point) (xp1:ext_point) (k:lbytes 32) : Tot (ext_point & ext_point) =
  Lib.LoopCombinators.repeati 256 (ladder_step k) (x, xp1)

let point_mul (a:lbytes 32) (p:ext_point) =
  fst (montgomery_ladder (zero, one, one, zero) p a)

let recover_x (y:nat) (sign:bool) : Tot (option elem) =
  if y >= prime then None
  else (
    let y2 = y *% y in
    let x2 = (y2 -% one) *% (modp_inv ((d *% y2) +% one)) in
    if x2 = zero then (
      if sign then None
      else Some zero)
    else (
      let x = x2 **% ((prime + 3) / 8) in
      let x = if ((x *% x) -% x2) <> zero then x *% modp_sqrt_m1 else x in
      if ((x *% x) -% x2) <> zero then None
      else (
        let x = if (x % 2 = 1) <> sign then (prime - x) % prime else x in
        Some x)))

let point_compress (p:ext_point) : Tot (lbytes 32) =
  let px, py, pz, pt = p in
  let zinv = modp_inv pz in
  let x = px *% zinv in
  let y = py *% zinv in
  nat_to_bytes_le 32 (pow2 255 * (x % 2) + y)

let point_decompress (s:lbytes 32) : Tot (option ext_point) =
  let y = nat_from_bytes_le s in
  let sign = (y / pow2 255) % 2 = 1 in
  let y = y % pow2 255 in
  let x = recover_x y sign in
  match x with
  | Some x -> Some (x, y, one, x *% y)
  | _ -> None

let secret_expand (secret:lbytes 32) : (lbytes 32 & lbytes 32) =
  let h = Spec.Agile.Hash.hash Spec.Hash.Definitions.SHA2_512 secret in
  let h_low : lbytes 32 = slice #uint8 #64 h 0 32 in
  let h_high : lbytes 32 = slice #uint8 #64 h 32 64 in
  let h_low0 : uint8  = index #uint8 #32 h_low 0 in
  let h_low31 = index #uint8 #32 h_low 31 in
  let h_low = h_low.[ 0] <- index #uint8 #32 h_low 0 &. u8 0xf8 in
  let h_low = h_low.[31] <- (index #uint8 #32 h_low 31 &. u8 127) |. u8 64 in
  h_low, h_high

let secret_to_public (secret:lbytes 32) =
  let a, dummy = secret_expand secret in
  point_compress (point_mul a g)

let point_equal (p:ext_point) (q:ext_point) =
  let px, py, pz, pt = p in
  let qx, qy, qz, qt = q in
  if ((px *% qz) <> (qx *% pz)) then false
  else if ((py *% qz) <> (qy *% pz)) then false
  else true

///
/// Ed25519 API
///

let expand_keys (secret: lbytes 32) : (lbytes 32 & lbytes 32 & lbytes 32) =
  let s, prefix = secret_expand secret in
  let pub = secret_to_public secret in
  pub, s, prefix

val sign_expanded:
  pub:lbytes 32 ->
  s:lbytes 32 ->
  prefix:lbytes 32 ->
  msg: bytes{64 + length msg <= max_size_t} ->
  Tot (lbytes 64)
let sign_expanded pub s prefix msg =
  let len = length msg in
  let r = sha512_modq (32 + len) (concat #uint8 #32 #(length msg) prefix msg) in
  let r' = point_mul (nat_to_bytes_le 32 r) g in
  let rs = point_compress r' in
  let h = sha512_modq (64 + len)
    (concat #uint8 #64 #(length msg) (concat #uint8 #32 #32 rs pub) msg)
  in
  let s = (r + (h * nat_from_bytes_le s) % q) % q in
  concat #uint8 #32 #32 rs (nat_to_bytes_le 32 s)

val sign:
    secret: lbytes 32
  -> msg: bytes{64 + length msg <= max_size_t} ->
  Tot (lbytes 64)

let sign secret msg =
  let pub, s, prefix = expand_keys secret in
  sign_expanded pub s prefix msg

val verify:
    public: lbytes 32
  -> msg: bytes{64 + length msg <= max_size_t}
  -> signature: lbytes 64 ->
  Tot bool

let verify public msg signature =
  let len = length msg in
  let a' = point_decompress public in
  match a' with
  | None -> false
  | Some a' -> (
    let rs = slice #uint8 #64 signature 0 32 in
    let r' = point_decompress rs in
    match r' with
    | None -> false
    | Some r' -> (
      let s = nat_from_bytes_le (slice #uint8 #64 signature 32 64) in
      if s >= q then false
      else (
        let h = sha512_modq (64 + len)
	  (concat #uint8 #64 #(length msg) (concat #uint8 #32 #32 rs public) msg)
	in
        let sB = point_mul (nat_to_bytes_le 32 s) g in
        let hA = point_mul (nat_to_bytes_le 32 h) a' in
        point_equal sB (point_add r' hA)
      )
    )
  )
