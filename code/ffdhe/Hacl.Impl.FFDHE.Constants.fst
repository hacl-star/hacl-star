module Hacl.Impl.FFDHE.Constants

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module ST = FStar.HyperStack.ST
module S = Spec.FFDHE

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let ffdhe_g2 :x:glbuffer pub_uint8 1ul{witnessed x S.ffdhe_g2 /\ recallable x} =
  createL_global S.list_ffdhe_g2

let ffdhe_p2048 :x:glbuffer pub_uint8 256ul{witnessed x S.ffdhe_p2048 /\ recallable x} =
  createL_global S.list_ffdhe_p2048

let ffdhe_p3072 :x:glbuffer pub_uint8 384ul{witnessed x S.ffdhe_p3072 /\ recallable x} =
  createL_global S.list_ffdhe_p3072

let ffdhe_p4096 :x:glbuffer pub_uint8 512ul{witnessed x S.ffdhe_p4096 /\ recallable x} =
  createL_global S.list_ffdhe_p4096

let ffdhe_p6144 :x:glbuffer pub_uint8 768ul{witnessed x S.ffdhe_p6144 /\ recallable x} =
  createL_global S.list_ffdhe_p6144

let ffdhe_p8192 :x:glbuffer pub_uint8 1024ul{witnessed x S.ffdhe_p8192 /\ recallable x} =
  createL_global S.list_ffdhe_p8192
