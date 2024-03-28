module Hacl.Spec.SHA3.Vec.Common

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul
open Lib.LoopCombinators

open Spec.SHA3.Constants

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

noextract
type m_spec =
  | M32
  | M128
  | M256

inline_for_extraction noextract
let lanes_t = n:nat{n == 1 \/ n == 2 \/ n == 4}

inline_for_extraction noextract
let lanes (m:m_spec) : lanes_t =
  match m with
  | M128 -> 2
  | M256 -> 4
  | _ -> 1

noextract
let is_supported (m:m_spec) =
  lanes m = 1 \/ lanes m = 4

inline_for_extraction noextract
let element_t (m:m_spec) = vec_t U64 (lanes m)

inline_for_extraction noextract
val zero_element: m:m_spec -> element_t m
let zero_element m = vec_zero U64 (lanes m)

inline_for_extraction noextract
val load_element: m:m_spec -> uint_t U64 SEC -> element_t m
let load_element m x = vec_load x (lanes m)

inline_for_extraction noextract
let next_block_seq_zero (m:m_spec{is_supported m}) :
  Lib.MultiBuffer.multiseq (lanes m) 256 =
  match lanes m with
  | 1 -> Lib.NTuple.ntup1 (create 256 (u8 0))
  | 4 ->
    let b = create 256 (u8 0) in
    Lib.NTuple.ntup4 (b, (b, (b, b)))
