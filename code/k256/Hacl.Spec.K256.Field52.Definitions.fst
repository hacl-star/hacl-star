module Hacl.Spec.K256.Field52.Definitions

open FStar.Mul
open Lib.IntTypes

module S = Spec.K256

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


inline_for_extraction noextract
let felem4 = uint64 & uint64 & uint64 & uint64

noextract
let as_nat4 (f:felem4) =
  let (f0, f1, f2, f3) = f in
  v f0 + v f1 * pow2 64 + v f2 * pow2 128 + v f3 * pow2 192


inline_for_extraction noextract
let felem5 = uint64 & uint64 & uint64 & uint64 & uint64

[@"opaque_to_smt"]
let pow52: (pow52:pos{pow2 64 == 4096 * pow52 /\ pow2 128 == 16777216 * pow52 * pow52 /\ pow2 52 == pow52}) =
  let pow52:pos = normalize_term (pow2 52) in
  assert_norm (pow52 = pow2 52);
  assert_norm (pow2 64 = 4096 * pow52);
  assert_norm (pow2 128 = 16777216 * pow52 * pow52);
  pow52


inline_for_extraction noextract
let mask52: x:uint64{v x == pow2 52 - 1} =
  assert_norm (pow2 52 - 1 = 0xfffffffffffff);
  u64 0xfffffffffffff


inline_for_extraction noextract
let mask48: x:uint64{v x == pow2 48 - 1} =
  assert_norm (pow2 48 - 1 = 0xffffffffffff);
  u64 0xffffffffffff


[@"opaque_to_smt"]
let pow104: (pow104:pos{pow2 104 == pow104 /\ pow104 == pow52 * pow52}) =
  let pow104:pos = normalize_term (pow2 104) in
  assert_norm (pow104 = pow2 104);
  Math.Lemmas.pow2_plus 52 52;
  pow104

[@"opaque_to_smt"]
let pow156: (pow156:pos{pow2 156 == pow156 /\ pow156 == pow52 * pow52 * pow52}) =
  let pow156:pos = normalize_term (pow2 156) in
  assert_norm (pow156 = pow2 156);
  Math.Lemmas.pow2_plus 52 52;
  Math.Lemmas.pow2_plus 104 52;
  pow156

[@"opaque_to_smt"]
let pow208: (pow208:pos{pow2 208 == pow208 /\ pow208 == pow52 * pow52 * pow52 * pow52}) =
  let pow208:pos = normalize_term (pow2 208) in
  assert_norm (pow208 = pow2 208);
  Math.Lemmas.pow2_plus 52 52;
  Math.Lemmas.pow2_plus 104 52;
  Math.Lemmas.pow2_plus 156 52;
  pow208


noextract
let as_nat5 (f:felem5) : nat =
  let (f0, f1, f2, f3, f4) = f in
  v f0 + v f1 * pow52 + v f2 * pow104 + v f3 * pow156 + v f4 * pow208

noextract
let feval (f:felem5) : S.felem = as_nat5 f % S.prime


let scale64 = x:nat{x <= 4096}
let scale64_last = x:nat{x <= 65536}
let nat5 = nat & nat & nat & nat & nat
let mk_nat5 (x:nat) : nat5 = (x,x,x,x,x)

let scale64_5 = x:nat5{let (x0,x1,x2,x3,x4) = x in
  x0 <= 4096 /\ x1 <= 4096 /\ x2 <= 4096 /\ x3 <= 4096 /\ x4 <= 65536}


let ( <=* ) (x y:nat5) : Type =
  let (x0,x1,x2,x3,x4) = x in
  let (y0,y1,y2,y3,y4) = y in
  x0 <= y0 /\ x1 <= y1 /\ x2 <= y2 /\ x3 <= y3 /\ x4 <= y4

let ( +* ) (x y:nat5) : nat5 =
  let (x0,x1,x2,x3,x4) = x in
  let (y0,y1,y2,y3,y4) = y in
  (x0 + y0, x1 + y1, x2 + y2, x3 + y3, x4 + y4)

let ( ** ) (x y:nat5) : nat5 =
  let (x0,x1,x2,x3,x4) = x in
  let (y0,y1,y2,y3,y4) = y in
  (x0 * y0, x1 * y1, x2 * y2, x3 * y3, x4 * y4)


noextract
let max52 : pos =
  assert_norm (pow2 52 - 1 > 0);
  pow2 52 - 1

noextract
let max48 : pos =
  assert_norm (pow2 48 - 1 > 0);
  pow2 48 - 1


let felem_fits1 (x:uint64) (m:scale64) =
  v x <= m * max52

let felem_fits_last1 (x:uint64) (m:scale64_last) =
  v x <= m * max48

let felem_fits5 (f:felem5) (m:scale64_5) =
  let (f0,f1,f2,f3,f4) = f in
  let (m0,m1,m2,m3,m4) = m in
  felem_fits1 f0 m0 /\
  felem_fits1 f1 m1 /\
  felem_fits1 f2 m2 /\
  felem_fits1 f3 m3 /\
  felem_fits_last1 f4 m4
