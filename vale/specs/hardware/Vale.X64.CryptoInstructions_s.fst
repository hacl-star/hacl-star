module Vale.X64.CryptoInstructions_s

open FStar.Mul
open Vale.Def.Opaque_s
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Four_s
open Spec.Hash.Definitions
open Spec.SHA2

friend Lib.IntTypes
friend Spec.SHA2

let sha256_rnds2_spec_update (a b c d e f g h wk : word SHA2_256) =
  let open FStar.UInt32 in   // Interop with UInt-based SHA spec
  let a' = add_mod (_Ch SHA2_256 e f g)
           (add_mod (_Sigma1 SHA2_256 e)
           (add_mod wk
           (add_mod h
           (add_mod (_Maj SHA2_256 a b c)
                    (_Sigma0 SHA2_256 a)))))  in
  let b' = a in
  let c' = b in
  let d' = c in
  let e' = add_mod (_Ch SHA2_256 e f g)
           (add_mod (_Sigma1 SHA2_256 e)
           (add_mod wk
           (add_mod h
                    d))) in
  let f' = e in
  let g' = f in
  let h' = g in
  (a', b', c', d', e', f', g', h')

let sha256_rnds2_spec_def (src1 src2 wk:quad32) : quad32 =
    let open FStar.UInt32 in   // Interop with UInt-based SHA spec
    let a0  = uint_to_t src2.hi3 in
    let b0  = uint_to_t src2.hi2 in
    let c0  = uint_to_t src1.hi3 in
    let d0  = uint_to_t src1.hi2 in
    let e0  = uint_to_t src2.lo1 in
    let f0  = uint_to_t src2.lo0 in
    let g0  = uint_to_t src1.lo1 in
    let h0  = uint_to_t src1.lo0 in
    let wk0 = uint_to_t wk.lo0 in
    let wk1 = uint_to_t wk.lo1 in
    let a1,b1,c1,d1,e1,f1,g1,h1 = sha256_rnds2_spec_update a0 b0 c0 d0 e0 f0 g0 h0 wk0 in
    let a2,b2,c2,d2,e2,f2,g2,h2 = sha256_rnds2_spec_update a1 b1 c1 d1 e1 f1 g1 h1 wk1 in
    let dst = Mkfour (v f2) (v e2) (v b2) (v a2) in
    dst
[@"opaque_to_smt"] let sha256_rnds2_spec = opaque_make sha256_rnds2_spec_def
irreducible let sha256_rnds2_spec_reveal = opaque_revealer (`%sha256_rnds2_spec) sha256_rnds2_spec sha256_rnds2_spec_def

let sha256_msg1_spec_def (src1 src2:quad32) : quad32 =
    let open FStar.UInt32 in   // Interop with UInt-based SHA spec
    let w4 = uint_to_t src2.lo0 in
    let w3 = uint_to_t src1.hi3 in
    let w2 = uint_to_t src1.hi2 in
    let w1 = uint_to_t src1.lo1 in
    let w0 = uint_to_t src1.lo0 in
    Mkfour (v (add_mod w0 (_sigma0 SHA2_256 w1)))
           (v (add_mod w1 (_sigma0 SHA2_256 w2)))
           (v (add_mod w2 (_sigma0 SHA2_256 w3)))
           (v (add_mod w3 (_sigma0 SHA2_256 w4)))
[@"opaque_to_smt"] let sha256_msg1_spec = opaque_make sha256_msg1_spec_def
irreducible let sha256_msg1_spec_reveal = opaque_revealer (`%sha256_msg1_spec) sha256_msg1_spec sha256_msg1_spec_def

let sha256_msg2_spec_def (src1 src2:quad32) : quad32 =
    let open FStar.UInt32 in   // Interop with UInt-based SHA spec
    let w14 = uint_to_t src2.hi2 in
    let w15 = uint_to_t src2.hi3 in
    let w16 = add_mod (uint_to_t src1.lo0) (_sigma1 SHA2_256 w14) in
    let w17 = add_mod (uint_to_t src1.lo1) (_sigma1 SHA2_256 w15) in
    let w18 = add_mod (uint_to_t src1.hi2) (_sigma1 SHA2_256 w16) in
    let w19 = add_mod (uint_to_t src1.hi3) (_sigma1 SHA2_256 w17) in
    Mkfour (v w16) (v w17) (v w18) (v w19)
[@"opaque_to_smt"] let sha256_msg2_spec = opaque_make sha256_msg2_spec_def
irreducible let sha256_msg2_spec_reveal = opaque_revealer (`%sha256_msg2_spec) sha256_msg2_spec sha256_msg2_spec_def
