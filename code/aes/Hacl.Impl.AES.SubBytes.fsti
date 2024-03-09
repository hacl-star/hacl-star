module Hacl.Impl.AES.SubBytes

module B = Lib.Buffer
module IT = Lib.IntTypes
module S = Lib.Sliceable

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

inline_for_extraction noextract
let u64 = S.uN IT.U64 IT.SEC

inline_for_extraction noextract
val sbox (s:nat{s<256}) : (r:nat{r<256})

inline_for_extraction noextract
val sbox_inv (s:nat{s<256}) : (r:nat{r<256})

val sbox_inv_theorem (s:nat{s<256}) : Lemma (sbox_inv (sbox s) == s)

// sub_bytes

inline_for_extraction noextract
val sub_bytes (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) : S.xNxM xN 8

val sub_bytes_theorem (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) (j:nat{j<n})
  : Lemma ( S.column j (sub_bytes x) == S.of_uint_rev (sbox (S.to_uint_rev (S.column j x))) )

val sub_bytes64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun h0 (o0,o1,o2,o3,o4,o5,o6,o7) h1 ->
        B.modifies LowStar.Monotonic.Buffer.loc_none h0 h1
        /\ S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7
          == sub_bytes (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7)
      )

// sub_bytes_inv

inline_for_extraction noextract
val sub_bytes_inv (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) : S.xNxM xN 8

val sub_bytes_inv_theorem (#n:IT.size_nat) (#xN:S.sig n) (x:S.xNxM xN 8) (j:nat{j<n})
  : Lemma ( S.column j (sub_bytes_inv x) == S.of_uint (sbox_inv (S.to_uint (S.column j x))) )

val sub_bytes_inv64x8
  (st0:u64.t) (st1:u64.t) (st2:u64.t) (st3:u64.t)
  (st4:u64.t) (st5:u64.t) (st6:u64.t) (st7:u64.t) :
    Stack
      (u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t * u64.t)
      (fun _ -> True)
      (fun h0 (o0,o1,o2,o3,o4,o5,o6,o7) h1 ->
        B.modifies LowStar.Monotonic.Buffer.loc_none h0 h1
        /\ S.uNx8_mk o0 o1 o2 o3 o4 o5 o6 o7
          == sub_bytes_inv (S.uNx8_mk st0 st1 st2 st3 st4 st5 st6 st7)
      )
