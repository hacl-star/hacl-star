module Spec.Ed25519

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.RawIntTypes
open Spec.SHA2
open Spec.Curve25519


#reset-options "--max_fuel 0 --z3rlimit 20"

(* Point addition *)
type aff_point = tuple2 elem elem           // Affine point
type ext_point = tuple4 elem elem elem elem // Homogeneous extended coordinates

// let sha512 (b:bytes{length b < pow2 32}) : Tot (lbytes 64) =
//   assert_norm(pow2 32 < pow2 125);
//   hash b

let modp_inv (x:elem) : Tot elem =
  x ** (prime - 2)

let d : elem = 37095705934669439343138083508754565189542113879843219016388785533085940283555

let q: elem =
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 < pow2 255 - 19);
  pow2 252 + 27742317777372353535851937790883648493 // Group order

let sha512_modq (len:size_t) (s:lbytes len) : Tot elem =
  nat_from_bytes_le (hash512 len s) % q

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let x2, y2, z2, t2 = q in
  let a = (y1 `fsub` x1) `fmul` (y2 `fsub` x2) in
  let b = (y1 `fadd` x1) `fmul` (y2 `fadd` x2) in
  let c = (2 `fmul` d `fmul` t1) `fmul` t2 in
  let d = (2 `fmul` z1) `fmul` z2 in
  let e = b `fsub` a in
  let f = d `fsub` c in
  let g = d `fadd` c in
  let h = b `fadd` a in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

let point_double (p:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let a = x1 `fmul` x1 in
  let b = y1 `fmul` y1 in
  let c = 2 `fmul` (z1 `fmul` z1) in
  let h = a `fadd` b in
  let e = h `fsub` ((x1 `fadd` y1) `fmul` (x1 `fadd` y1)) in
  let g = a `fsub` b in
  let f = c `fadd` g in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

#reset-options "--max_fuel 0 --z3rlimit 100"

let ith_bit (len:size_t) (k:lbytes len) (i:size_t{i < 8 * len}) =
  let q = i / 8 in let r = u32 (i % 8) in
  (k.[q] >>. r) &. u8 1

let rec montgomery_ladder_ (x:ext_point) (xp1:ext_point) (len:size_t{8 * len <= max_size_t}) (k:lbytes len) (ctr:size_t{ ctr <= 8 * len})
  : Tot (tuple2 ext_point ext_point) (decreases ctr) =
  if ctr = 0 then x, xp1
  else (
    let x, xp1 = montgomery_ladder_ x xp1 len k (ctr-1) in
    let ctr' : size_t = 8 * len - ctr in
    let x, xp1 = if uint_to_nat (ith_bit len k ctr') = 1 then xp1, x else x, xp1 in
    let xx = point_double x in
    let xxp1 = point_add x xp1 in
    if uint_to_nat (ith_bit len k ctr') = 1 then xxp1, xx else xx, xxp1
  )

let point_mul (len:size_t{8 * len <= max_size_t}) (a:lbytes len) (p:ext_point) =
  fst (montgomery_ladder_ (zero, one, one, zero) p len a (8 * len))

let modp_sqrt_m1 : elem = 2 ** ((prime - 1) / 4)

noeq type record = { s:(s':lseq bool 3)}

let recover_x (y:nat) (sign:bool) : Tot (option elem) =
  if y >= prime then None
  else (
    let x2 = ((y `fmul` y) `fsub` 1) `fmul` (modp_inv ((d `fmul` (y `fmul` y)) `fadd` one)) in
    if x2 = zero then (
      if sign then None
      else Some zero
    ) else (
      let x = x2 ** ((prime + 3) / 8) in
      let x = if ((x `fmul` x) `fsub` x2) <> zero then x `fmul` modp_sqrt_m1 else x in
      if ((x `fmul` x) `fsub` x2) <> zero then None
      else (
        let x = if (x % 2 = 1) <> sign then prime `fsub` x else x in
        Some x)))

let g_x : elem = 15112221349535400772501151409588531511454012693041857206046113283949847762202
let g_y : elem = 46316835694926478169428394003475163141307993866256225615783033603165251855960

let g: ext_point = (g_x, g_y, 1, g_x `fmul` g_y)

let point_compress (p:ext_point) : Tot (lbytes 32) =
  let px, py, pz, pt = p in
  let zinv = modp_inv pz in
  let x = px `fmul` zinv in
  let y = py `fmul` zinv in
  nat_to_bytes_le 32 ((pow2 255 * (x % 2)) + y)

let point_decompress (s:lbytes 32) : Tot (option ext_point) =
  let y = nat_from_bytes_le s in
  let sign = (y / pow2 255) % 2 = 1 in
  let y = y % (pow2 255) in
  let x = recover_x y sign in
  match x with
  | Some x -> Some (x, y % prime, one, x `fmul` (y % prime))
  | _ -> None

let secret_expand (secret:lbytes 32) =
  let h = hash512 32 secret in
  let h_low = slice h 0 32 in
  let h_high = slice h 32 64 in
  let h_low0  = h_low.[0] in
  let h_low31 = h_low.[31] in
  let h_low = h_low.[ 0] <- (h_low0 &. u8 0xf8) in
  let h_low = h_low.[31] <- ((h_low31 &. u8 127) |. u8 64) in
  h_low, h_high

let secret_to_public (secret:lbytes 32) =
  let a, dummy = secret_expand secret in
  point_compress (point_mul 32 a g)

#reset-options "--max_fuel 0 --z3rlimit 25"

let sign (secret:lbytes 32) (len:size_t{ 8 * len < max_size_t}) (msg:lbytes len) =
  let a, prefix = secret_expand secret in
  let a' = point_compress (point_mul 32 a g) in
  let tmp = create (len + 64) (u8 0) in
  let tmp = update_sub tmp 32 32 prefix in
  let tmp = update_sub tmp 64 len msg in
  let prefix_msg = sub tmp 32 (32 + len) in
  let r = sha512_modq (32 + len) prefix_msg in
  let r' = point_mul 32 (nat_to_bytes_le 32 r) g in
  let rs = point_compress r' in
  let tmp = update_sub tmp 0 32 rs in
  let rs_a_msg = update_sub tmp 32 32 a' in
  let h = sha512_modq (64 + len) rs_a_msg in
  let s = (r + ((h * (nat_from_bytes_le a)) % q)) % q in
  let tmp = update_sub tmp 32 32 (nat_to_bytes_le 32 s) in
  slice tmp 0 64


let point_equal (p:ext_point) (q:ext_point) =
  let px, py, pz, pt = p in
  let qx, qy, qz, qt = q in
  if ((px `fmul` qz) <> (qx `fmul` pz)) then false
  else if ((py `fmul` qz) <> (qy `fmul` pz)) then false
  else true

let verify (public:lbytes 32) (len:size_t{ 8 * len < max_size_t}) (msg:lbytes len) (signature:lbytes 64) =
  let a' = point_decompress public in
  match a' with
  | None -> false
  | Some a' -> (
      let rs = slice signature 0 32 in
      let r' = point_decompress rs in
      match r' with
      | None -> false
      | Some r' -> (
          let s = nat_from_bytes_le (slice signature 32 64) in
          if s >= q then false
          else (
            let rs_public_msg = create (64 + len) (u8 0) in
            let rs_public_msg = update_sub rs_public_msg 0 32 rs in
            let rs_public_msg = update_sub rs_public_msg 32 32 public in
            let rs_public_msg = update_sub rs_public_msg 64 len msg in
            let h = sha512_modq (64 + len) rs_public_msg in
            let sB = point_mul 32 (nat_to_bytes_le 32 s) g in
            let hA = point_mul 32 (nat_to_bytes_le 32 h) a' in
            point_equal sB (point_add r' hA)
          )))

