module Spec.Kyber2.CBD

open FStar.Mul

open Spec.Kyber2.Params
open Lib.Poly
open Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring
open Lib.Arithmetic.Sums

open Spec.Kyber2.Group
open Spec.Kyber2.Ring

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

let a_spec #l #len (i:nat) = lbytes_l l len

let to_bits_inner_ #l (e:uint_t U8 l) (j:nat{j<8}) = (cast U1 l (e >>. (size j)))

let to_bits_inner (#l:secrecy_level) (#len:size_nat) (i:nat{i<len}) (acc: a_spec i) : Tot (a:(a_spec (i+1) & lbits_l l 8){let (s,b) = a in s == acc}) =
  acc, createi 8 (to_bits_inner_ #l (index #_ #len acc i))

let to_bits #l #len bytes =
  let (_,s) = generate_blocks 8 len a_spec to_bits_inner bytes in s

val to_bytes: #l:secrecy_level -> #len:size_nat{len%8=0} -> (bits:lbits_l l len) -> lbytes_l l (len/8)

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 2 --using_facts_from '* -FStar.Seq'"

let to_bytes_inner__ #l (input:lbits_l l 8) (j:nat{j<8}) (acc:uint_t U8 l) =
  acc +. ((cast U8 l (input.[j])) <<. (size j))

let to_bytes_inner_ #l (input:lbits_l l 8) (j:nat{j<8}) (acc:lbytes_l l 1) =
  Seq.map (to_bytes_inner__ #l input j) acc
  
let to_bytes_inner #l (input:lbits_l l 8) : uint_t U8 l =
  (Lib.LoopCombinators.repeati 8 (to_bytes_inner_ #l input) (Seq.create 1 (uint #U8 #l 0))).[0]

let to_bytes_fun #l (#len:size_nat{len % 8 = 0}) (input:lbits_l l len) (i:size_nat{i < len / 8}) =
  to_bytes_inner (Seq.sub input (8*i) 8)
  
let to_bytes #l #len bits =
  createi (len/8) (to_bytes_fun bits)

(*
val convert_to_field: #t:inttype -> #l:secrecy_level -> #len:size_nat -> lseq (uint_t t l) len -> lseq (field params_q) len

let convert_to_field #t #l #len s =
  let f (i:nat{i<len}) : field params_q = (uint_v s.[i]) % params_q in 
  createi len f
*)

val cbd_eta: (bytes:lbytes_l SEC (64*params_eta)) -> lseq (Group.t) params_n

let cbd_eta bytes =
  let bits = Seq.map int16_to_t (Seq.map to_i16 (to_bits bytes)) in
  let f (i:nat{i<params_n}) =
    let m = monoid_plus_t in
    let r = ring_t in
    let a = sum_n (Seq.sub bits (2*i*params_eta) params_eta) in
    let b = sum_n (Seq.sub bits (2*i*params_eta + params_eta) params_eta) in
    minus a b
  in
  createi params_n f
  
val cbd_kyber: (s:lbytes_l SEC 32) -> (b:uint_t U8 SEC) -> lseq (Group.t) params_n

let cbd_kyber s b = cbd_eta (prf (64*params_eta) s b)
