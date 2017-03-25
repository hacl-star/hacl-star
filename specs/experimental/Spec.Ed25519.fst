module Spec.Ed25519

open FStar.Mul
open FStar.Seq
open FStar.Endianness
open FStar.UInt8
open Spec.Lib
open Spec.Curve25519


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

(* Point addition *)
type aff_point = tuple2 elem elem           // Affine point
type ext_point = tuple4 elem elem elem elem // Homogeneous extended coordinates

(* Square root computation *)
let square_root_candidate (a:elem) =
  let x = a ** ((prime+3)/8) in
  let xx = x `fmul` x in
  if xx = a then Some x
  else if xx = zero `fsub` a then Some ((2 ** ((prime - 1)/4)) `fmul` x)
  else None

(* Point encoding *)
let encode_point (p:aff_point) =
  let x, y = p in
  assert_norm(pow2 255 + (pow2 255 - 19) < pow2 256);
  little_bytes 32ul ((pow2 255 * (x % 2)) + y)


(* Decode point *)
let d = 37095705934669439343138083508754565189542113879843219016388785533085940283555

let decode_point (p:lbytes 32) : Tot (option aff_point) =
  (* Step 1 *)
  let p_num = little_endian p in
  let x_0    = p_num / pow2 255 in
  let y     = p_num % pow2 255 in
  let x =
  if y >= prime then None
  (* Step 2 *)
  else (
    let u = (y ** 2) `fsub` one in
    let v = (d `fmul` (y ** 2)) `fadd` one in
    let x = u `fmul` (v ** 3) `fmul` ((u `fmul` (v **7)) ** ((prime-5)/8)) in
    (* Step 3 *)
    if v `fmul` (x ** 2) = u then Some x
    else if v `fmul` (x ** 2) = zero `fsub` u then Some (x `fmul` 2 ** ((prime-1)/4))
    else None
  ) in
  match x with
  | Some x ->
    begin
      (* Step 4 *)
      if x = 0 && x_0 = 1 then None
      else if x_0 <> (x % 2) then Some ((zero `fsub` x), y)
      else Some (x, y)
    end
  | _ -> None

let point_add (p:ext_point) (q:ext_point) : Tot ext_point =
  let x1, y1, z1, t1 = p in
  let x2, y2, z2, t2 = q in
  let a = (y1 `fsub` x1) `fmul` (y2 `fsub` x2) in
  let b = (y1 `fadd` x1) `fmul` (y2 `fadd` x2) in
  let c = t1 `fmul` 2 `fmul` d `fmul` t2 in
  let d = z1 `fmul` 2 `fmul` z2 in
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
  let a = x1 ** 2 in
  let b = y1 ** 2 in
  let c = 2 `fmul` (z1 ** 2) in
  let h = a `fadd` b in
  let e = h `fsub` ((x1 `fadd` y1) ** 2) in
  let g = a `fsub` b in
  let f = c `fadd` g in
  let x3 = e `fmul` f in
  let y3 = g `fmul` h in
  let t3 = e `fmul` h in
  let z3 = f `fmul` g in
  (x3, y3, z3, t3)

assume val sha512: bytes -> Tot (lbytes 64)

(* Conversions between coordinate systems *)
let affine_to_ext_hom (p:aff_point) : Tot (q:ext_point) =
  let x = fst p in
  let y = snd p in
  (x, y, 1, x `fmul` y)

let ext_hom_to_affine (p:ext_point) : Tot (q:aff_point) =
  let x, y, z, t = p in
  (x `fmul` (z ** (prime-2))), (y `fmul` (z ** (prime-2)))

let basepoint : aff_point =
  (15112221349535400772501151409588531511454012693041857206046113283949847762202,
   46316835694926478169428394003475163141307993866256225615783033603165251855960)

let neutral_point : aff_point =
  (zero, one)

(* Key generation *)
let prune_buffer (k:lbytes 32) =
  let k0  = k.[0] in
  let k31 = k.[31] in
  let k = k.[ 0] <- (k0 &^ 0xf8uy) in
  let k = k.[31] <- ((k31 &^ 0x7fuy) |^ 0x40uy) in
  k

let rec montgomery_ladder_ (x:ext_point) (xp1:ext_point) (k:scalar) (ctr:nat{ctr<=256})
  : Tot ext_point (decreases ctr) =
  if ctr = 0 then x
  else (
    let ctr' = ctr - 1 in
    let (x', xp1') =
      if ith_bit k ctr' = 1 then (
        let nqp2 = point_double xp1 in
        let nqp1 = point_add x xp1 in
        nqp1, nqp2
      ) else (
        let nqp1 = point_double x in
        let nqp2 = point_add x xp1 in
        nqp1, nqp2
      ) in
    montgomery_ladder_ x' xp1' k ctr'
  )

let montgomery_ladder (init:aff_point) (k:scalar) : Tot aff_point =
  let ext_neutral = affine_to_ext_hom neutral_point in
  let ext_init    = affine_to_ext_hom init in
  let ext_res     = montgomery_ladder_ ext_neutral ext_init k 256 in
  let aff_res     = ext_hom_to_affine ext_res in
  aff_res

let pk_gen (sk:lbytes 32) : Tot (lbytes 32) =
  let sha_block = sha512 sk in
  let b = slice sha_block 0 32 in
  let k = prune_buffer b in
  let pkp = montgomery_ladder basepoint k in
  encode_point pkp

(* Sign *)
let sign (privk:lbytes 32) (m:bytes) : Tot (lbytes 64) =
  let h = sha512 privk in
  let scalar, prefix = split h 32 in
  let pubkA = pk_gen scalar in
  let r_ = sha512 (prefix @| m) in
  let r = little_endian r_ % prime in
  let rbytes = little_bytes 32ul r in
  let rB = montgomery_ladder basepoint rbytes in
  let rString = encode_point rB in
  let k = sha512 (rString @| pubkA @| m) in
  let s = r `fadd`
           ((little_endian k % prime) `fmul` (little_endian scalar % prime)) in
  rString @| little_bytes 32ul (s % pow2 253)

(* Verify *)
let verify (sig:lbytes 64) (pkA:lbytes 32) (m:bytes) =
  let r,s = split sig 32 in
  let r_p = decode_point r in
  let a_p = decode_point pkA in
  match r_p, a_p with
  | Some r_p, Some a' -> (
      let k = sha512 (r @| pkA @| m) in
      let k = little_bytes 32ul (little_endian k % prime) in
      let sB = montgomery_ladder basepoint s in
      let kA = montgomery_ladder a' k in
      let rpkA = point_add (affine_to_ext_hom r_p) (affine_to_ext_hom kA) in
      if sB = ext_hom_to_affine rpkA then true
      else false)
   | _ -> false
