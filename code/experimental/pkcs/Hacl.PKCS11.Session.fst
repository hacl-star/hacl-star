module Hacl.PKCS11.Session

open Lib.Sequence
open Lib.IntTypes

noeq type session = 
  |Session of (a: uint32 -> lseq uint64 32 ->  session)
