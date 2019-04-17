module Spec.Kyber.NTT

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas
open FStar.Classical

open Spec.Kyber.Params
open Spec.Kyber.Lemmas
open Spec.Kyber.Poly

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

type reversed (#t:inttype) (#l:secrecy_level) (#m:nat) (a:poly #t #l m) = bool

unfold inline_for_extraction 
type nttpoly (#t:inttype) (#l:secrecy_level) (m:nat) = p:(poly #t #l m){reversed p}
type poly (#t:inttype) (#l:secrecy_level) (m:nat) =  p:(poly #t #l m){(reversed p) ==> false}
unfold inline_for_extraction
type pub_poly (#t:inttype) = poly #t #PUB
unfold inline_for_extraction
type sec_poly (#t:inttype) = poly #t #SEC

unfold inline_for_extraction
type pub_poly16 = pub_poly #U16

unfold inline_for_extraction
type poly_array (#t:inttype) (#l:secrecy_level) (k:size_nat) (m:nat) = lseq (poly #t #l m) k
unfold inline_for_extraction
type pub_poly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (pub_poly #t m) k
unfold inline_for_extraction
type sec_poly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (sec_poly #t m) k

unfold inline_for_extraction
type pub_poly_array16 (k:size_nat) (m:nat) = lseq (pub_poly16 m) k

unfold inline_for_extraction
type pub_nttpoly (#t:inttype) = nttpoly #t #PUB
unfold inline_for_extraction
type sec_nttpoly (#t:inttype) = nttpoly #t #SEC

unfold inline_for_extraction
type pub_nttpoly16 = pub_nttpoly #U16

unfold inline_for_extraction
type nttpoly_array (#t:inttype) (#l:secrecy_level) (k:size_nat) (m:nat) = lseq (nttpoly #t #l m) k
unfold inline_for_extraction
type pub_nttpoly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (pub_nttpoly #t m) k
unfold inline_for_extraction
type sec_nttpoly_array (#t:inttype) (k:size_nat) (m:nat) = lseq (sec_nttpoly #t m) k

unfold inline_for_extraction
type pub_nttpoly_array16 (k:size_nat) (m:nat) = lseq (pub_nttpoly16 m) k

val ntt: (#t:inttype) -> (#l:secrecy_level) -> (#m:nat) -> (p:poly #t #l m) -> (p':nttpoly #t #l m)

let ntt #t #l #m p =
  let (p':nttpoly m) = map (fun i -> i) p in p'
  
