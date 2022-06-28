module Hacl.Impl.AES.SubBytes

module B = Lib.Buffer
module IT = Lib.IntTypes
module S = Lib.Sliceable

open FStar.HyperStack.ST

inline_for_extraction noextract
let u64 = S.uN IT.U64 IT.SEC

inline_for_extraction noextract
val sub_bytes_spec (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) : S.xNxM xN 8

val sub_bytes64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun h0 (o0,o1,o2,o3,o4,o5,o6,o7) h1 ->
        B.modifies LowStar.Monotonic.Buffer.loc_none h0 h1
        /\ S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7
          == sub_bytes_spec (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7)
      )
