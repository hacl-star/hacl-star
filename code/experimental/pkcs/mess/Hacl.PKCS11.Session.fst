module Hacl.PKCS11.Session

open Lib.Sequence
open Lib.IntTypes

(* session is a pointer to an object referencing a session  *)

(*Valid session handles in Cryptoki always have nonzero values. -> a: uint32 *)

noextract
noeq type session = |Session: sessionIndex: uint32 {uint_v sessionIndex > 0} -> session
