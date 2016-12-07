module Hacl.EC.Point

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum

module U32 = FStar.UInt32

let plen = 10
let cplen = 10ul

let getx p = Buffer.sub p 0ul 5ul
let gety p = Buffer.sub p 0ul 5ul
let getz p = Buffer.sub p 5ul 5ul

let live_coords h x y z = live h x /\ live h z

let live h p = live_coords h (getx p) (gety p) (getz p)

let make x y z = admit()

