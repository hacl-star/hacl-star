module Spec.P256

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.NatMod



#reset-options "--max_fuel 0 --z3rlimit 20"


val p256_prime_value: n : nat ->  Lemma
  (requires (n = 256))
  (ensures (pow2 n - pow2 224 + pow2 192 + pow2 96 -1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
  [SMTPat (pow2 n - pow2 224 + pow2 192 + pow2 96 - 1)]

let p256_prime_value n =
  assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)


let prime = pow2 256 - pow2 224 + pow2 192 + pow2 96 -1


val p256_prime_value_inverse: prime : nat ->  Lemma
  (requires (prime = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff))
  (ensures (prime - 2 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd))
  [SMTPat (prime - 2)]


let p256_prime_value_inverse prime =
  assert_norm(pow2 256 - pow2 224 + pow2 192 + pow2 96 - 3 = 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd)


unfold type elem = nat_mod prime
let to_elem x = x `modulo` prime
let from_elem (x:elem) = nat_mod_v x
let zero : elem = to_elem 0
let one  : elem = to_elem 1

let modp_inv (x: elem) : Tot elem =
  x **% to_elem(prime - 2)

type scalar = lbytes 32
type serialized_point = lbytes 33
type jacobian = | Jacobian: x: elem -> y: elem -> z: elem -> jacobian
type affine = | Affine: x1: elem -> y1: elem -> affine


let point_compare p q =
  p.x = q.x && p.y = q.y && p.z = q.z


let pointAtInfinity = Jacobian 1 1 0


let point_double p =
  if point_compare p pointAtInfinity then p else
  let x1 = p.x in
  let y1 = p.y in
  let z1 = p.z in
  let delta = z1**%2 in
  let gamma = y1**%2 in
  let beta = x1 *% gamma in
  let alpha = 3 *% (x1 -% delta) *% (x1 +% delta) in
  let x3 = (alpha **%2) -% (8 *% beta) in
  let z3 = ((y1 +% z1) **%2) -% gamma -% delta in
  let y3 = alpha *% (4 *% beta -% x3) -% (8 *% (gamma**%2)) in
  Jacobian x3 y3 z3


val point_add : p: jacobian -> q: jacobian ->Tot jacobian
let point_add p q =
  if point_compare p pointAtInfinity then q
  else if point_compare q pointAtInfinity then p
  else
    let x1 = p.x in
    let y1 = p.y in
    let z1 = p.z in
    let x2 = q.x in
    let y2 = q.y in
    let z2 = q.z in
    let z1z1 = z1 **% 2 in
    let z2z2 = z2 **% 2 in
    let u1 = x1 *% z2z2  in
    let u2 = x2 *% z1z1 in
    let s1 = y1 *% z2 *% z2z2 in
    let s2 = y2 *% z1 *% z1z1 in
    if (u1 = u2) then (
      if (s1 = s2) then point_double p
      else Jacobian 0x1 0x01 0x0)
    else (
      let h = u2 -% u1 in
      let i = (2 *% h) **% 2 in
      let j = h *% i in
      let r = 2 *% (s2 -% s1) in
      let v = u1 *% i in
      let x3 = (r **% 2) -% j -% (2 *% v) in
      let y3 = r *% (v -% x3) -% (2 *% s1 *% j) in
      let z3_part = (z1 +% z2) **%2 in
      let z3 = (z3_part -% z1z1 -% z2z2) *% h in
      Jacobian x3 y3 z3
  )


let ith_bit (k:scalar) (i:nat{i < 256}) : uint8 =
  let (&.) = logand #U8 in
  let q = i / 8 in let r = size (i % 8) in
  (k.[q] >>. r) &. u8 1


val montgomery_ladder_ :
    r0: jacobian
  -> r1: jacobian
  -> k: scalar
  -> counter: nat{counter < 256} ->
  Tot jacobian (decreases counter)

let rec montgomery_ladder_ r0 r1 k counter =
  let (r0, r1) =
    if uint_to_nat #U8 (ith_bit k counter) = 1 then
      (point_add r0 r1, point_double r1)
    else
      (point_double r0, point_add r0 r1)
  in
  if counter > 0 then montgomery_ladder_ r0 r1 k (counter - 1)
  else r0


val montgomery_ladder: point: jacobian -> k: scalar -> Tot jacobian
let montgomery_ladder point k =
  let r0 = Jacobian (0x1) (0x1) (0x0) in
  let r1 = point in
  montgomery_ladder_ r0 r1 k 255


val point_of_list: l: list nat{List.Tot.length l = 3} -> Tot jacobian
let point_of_list l =
  Jacobian (to_elem(List.Tot.index l 0)) (to_elem(List.Tot.index l 1)) (to_elem(List.Tot.index l 2))


let norm p =
  let z2 = p.z **%2 in
  let z2i = modp_inv z2 in
  let z3 = p.z**%3 in
  let z3i = modp_inv z3 in
  Jacobian (p.x *% z2i) (p.y *% z3i) (to_elem 1)


assume val to_string: jacobian -> Tot string
