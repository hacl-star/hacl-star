module Hacl.Impl.Bignum.Misc

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.ByteBuffer
open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Convert
open Hacl.Spec.Bignum

val bn_assign_uint64:
     #len:bn_len
  -> a:lbignum len
  -> x:uint64
  -> Stack unit
    (requires fun h -> live h a)
    (ensures fun h0 _ h1 -> modifies1 a h0 h1 /\ as_snat h1 a = v x)
let bn_assign_uint64 #len a x =
  a.(0ul) <- x;
  if len >. 1ul then memset (sub a 1ul (len -! 1ul)) (uint 0) (len -! 1ul);
  let h = FStar.HyperStack.ST.get () in
  assume (as_snat h a = v x)


//////// Some debugging, at least for the time being

noextract inline_for_extraction
let debugOn = false

// Prints in big endian, both with respect to uint64 chunks, and within them.
val print_lbignum:
     #aLen:bn_len
  -> a:lbignum aLen
  -> ST unit (requires fun h -> live h a) (ensures fun h0 _ h1 -> h0 == h1)
let print_lbignum #aLen a =
  assume (8 * v aLen < max_size_t);
  push_frame ();
  let bytes_n = aLen *! 8ul in
  let bytes = create bytes_n (uint 0) in
  let a' = bignum_to_bytes a bytes in
  print_bytes bytes_n bytes;
  pop_frame ();
  admit()

noextract inline_for_extraction
val trace_lbignum:
     #aLen:bn_len
  -> a:lbignum aLen
  -> ST unit (requires fun h -> live h a) (ensures fun h0 _ h1 -> h0 == h1)
let trace_lbignum #aLen a = if debugOn then print_lbignum a else ()

noextract inline_for_extraction
let trace (s:string) = if debugOn then C.String.print (C.String.of_literal s) else ()
