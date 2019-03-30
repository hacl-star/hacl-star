module Poly1305.Spec_s

open FStar.Mul
open Words_s
open Types_s

[@"opaque_to_smt"]
let modp (x:int) : int =
  x % (pow2_128 * 4 - 5)

[@"opaque_to_smt"]
let mod2_128 (x:int) : int =
  x % pow2_128

let rec poly1305_hash_blocks (h:int) (pad:int) (r:int) (inp:int -> nat128) (k:nat) : int =
  if k = 0 then h
  else
    let kk = k - 1 in
    let hh = poly1305_hash_blocks h pad r inp kk in
    modp ((hh + pad + inp kk) * r)

let poly1305_hash (key_r:nat128) (key_s:nat128) (inp:int -> nat128) (len:nat) : int =
  let r = iand key_r 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let nBlocks = len / 16 in
  let nExtra = len % 16 in
  let padBlocks = pow2_128 in
  let hBlocks = poly1305_hash_blocks 0 padBlocks r inp nBlocks in
  if nExtra = 0 then
    mod2_128 (hBlocks + key_s)
  else
    let k = nBlocks in
    let padLast = pow2 (nExtra * 8) in
    let hLast = modp ((hBlocks + padLast + ((inp k) % padLast)) * r) in
    mod2_128 (hLast + key_s)
