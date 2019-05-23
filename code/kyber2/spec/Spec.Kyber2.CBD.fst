module Spec.Kyber2.CBD

open FStar.Mul

open Spec.Kyber2.Params
open Lib.Poly
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums
open Lib.Arithmetic.Group.Uint_t
open Lib.Arithmetic.Ring.Uint_t

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas

open Spec.Kyber2.FunctionInstantiation

module Seq = Lib.Sequence

type lbits_l (l:secrecy_level) (len:size_nat) = lseq (uint_t U1 l) len

val to_bits: #l:secrecy_level -> #len:size_nat{len<max_size_t/8} -> (bytes:lbytes_l l len) -> lbits_l l (8*len)

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"



let to_bits #l #len bytes =
  let a (i:nat{i<=len}) = int in
  let f (i:nat{i<len}) (acc:a i) : a (i+1) & lseq (uint_t U1 l) 8 =
    let g (j:nat{j<8}) = (cast U1 l (bytes.[i] >>. (uint #U32 #PUB j))) in
    0, createi 8 g
  in
  let (_,s) = generate_blocks 8 len a f 0 in s

val to_bytes: #l:secrecy_level -> #len:size_nat{len%8=0} -> (bits:lbits_l l len) -> lbytes_l l (len/8)

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let to_bytes #l #len bits =
  let a (i:nat{i<=len/8}) = int in
  let f (i:nat{i<len/8}) : uint_t U8 l =
    let g (j:nat{j<8}) (acc:uint_t U8 l) =
      acc +. ((cast U8 l bits.[8*i+j]) <<. (uint #U32 #PUB j))
    in Lib.LoopCombinators.repeati 8 g (uint #U8 #l 0)
  in createi (len/8) f

val convert_to_field: #t:inttype -> #l:secrecy_level -> #len:size_nat -> lseq (uint_t t l) len -> lseq (field params_q) len

let convert_to_field #t #l #len s =
  let f (i:nat{i<len}) : field params_q = (uint_v s.[i]) % params_q in 
  createi len f
  
val cbd_eta: (bytes:lbytes_l SEC (64*params_eta)) -> lseq (field params_q) params_n

let cbd_eta bytes =
  let bits = convert_to_field (Seq.map to_u16 (to_bits bytes)) in
  let f (i:nat{i<params_n}) =
    let m = monoid_plus_mod #params_q in
    let r = ring_mod #params_q in
    let a = sum_n (Seq.sub bits (2*i*params_eta) params_eta) in
    let b = sum_n (Seq.sub bits (2*i*params_eta + params_eta) params_eta) in
    minus a b
  in
  createi params_n f
  
val cbd_kyber: (s:lbytes_l SEC 32) -> (b:uint_t U8 SEC) -> lseq (field params_q) params_n

let cbd_kyber s b = cbd_eta (prf (64*params_eta) s b)
