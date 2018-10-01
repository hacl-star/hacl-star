module Hacl.Impl.Poly1305.FieldSpec

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils

noextract
type field_spec = 
  | M32
  | M64


unfold
let limb (s:field_spec) =
  match s with
  | M32 -> uint32
  | M64 -> uint64

unfold
let wide (s:field_spec) =
  match s with
  | M32 -> uint64
  | M64 -> uint128

unfold
let nlimb (s:field_spec) : size_nat =
  match s with
  | M32 -> 5
  | M64 -> 3


type felem (s:field_spec) = lbuffer (limb s) (nlimb s)
type felem_wide (s:field_spec) = lbuffer (wide s) (nlimb s)

