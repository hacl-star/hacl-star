module Vale.Poly1305.Spec_s

open FStar.Mul
open Vale.Def.Words_s
open Vale.Def.Types_s

[@"opaque_to_smt"]
let modp (x:int) : int =
  x % (pow2_128 * 4 - 5)

[@"opaque_to_smt"]
let mod2_128 (x:int) : int =
  x % pow2_128

let rec poly1305_hash_blocks (h pad r:int) (inp:int -> nat128) (k:nat) : int =
  if k = 0 then h
  else
    let hh = poly1305_hash_blocks h pad r inp (k - 1) in
    modp ((hh + pad + inp (k - 1)) * r)

let make_r (key_r:nat128) : nat128 =
  iand key_r 0x0ffffffc0ffffffc0ffffffc0fffffff

let poly1305_hash_all (h:int) (key_r key_s:nat128) (inp:int -> nat128) (len:nat) : int =
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let hBlocks = poly1305_hash_blocks h pow2_128 (make_r key_r) inp nBlocks in
  if nExtra = 0 then
    mod2_128 (hBlocks + key_s)
  else
    let padLast = pow2 (nExtra * 8) in
    let hLast = modp ((hBlocks + padLast + inp nBlocks % padLast) * (make_r key_r)) in
    mod2_128 (hLast + key_s)

let poly1305_hash (key_r key_s:nat128) (inp:int -> nat128) (len:nat) : int =
  poly1305_hash_all 0 key_r key_s inp len
