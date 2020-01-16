module PKCS11.DateTime

open FStar.Seq

(*TODO: check with PKCS11 data types *)

type date  = |MakeDate: day: FStar.UInt8.t -> month:  FStar.UInt8.t -> year:  FStar.UInt8.t -> date

assume val parseDate: seq FStar.UInt8.t -> Tot date