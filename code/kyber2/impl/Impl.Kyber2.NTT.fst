module Impl.Kyber2.NTT

open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Impl.Kyber2.Group
open Impl.Kyber2.Ring
open Lib.Buffer

module ST = FStar.HyperStack.ST
module Buf = Lib.Buffer
module Seq = Lib.Sequence

open Spec.Kyber2.Params

noextract inline_for_extraction let zeta:t = i16 params_zeta

noextract inline_for_extraction let n2:(x:size_t{v x = params_n/2}) =
  size params_n >>. size 1
(*
let ntt_sequence1 (input:lbuffer t n2) (output:lbuffer t n2) (k:size_t{v k < params_n/2}) : Stack unit
  (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Lib.Poly.NTT.lib_ntt_sequence #t #Spec.Kyber2.Ring.ring_t (Lib.Arithmetic.Ring.exp #t #Spec.Kyber2.Ring.ring_t zeta 2) zeta h0.[|input|] (v k)) = 
  let h = ST.get () in
  mapiT output (fun i g -> mul_t (exp_t 
(*
let ntt1 (input:lbuffer t (size params_n >>. size 2)) (output:lbuffer t (size params_n >>. size 2)) : Stack unit
  (requires fun h -> live h input /\ live h output /\ Buf.disjoint input output)
  (ensures fun h0 _ h1 -> modifies1 output h0 h1 /\ h1.[|output|] == Lib.Poly.NTT.lib_ntt #t #Spec.Kyber2.Ring.ring_t (Lib.Arithmetic.Ring.exp #t #Spec.Kyber2.Ring.ring_t (i16 params_zeta) 2) (i16 params_zeta) h0.[|input|]) =
  let h0 = ST.get () in
  Buf.mapiT (size params_n >>. size 2) output (fun j g -> 
