module QTesla.Params

open Lib.IntTypes

#reset-options "--max_fuel 0 --max_ifuel 0"

inline_for_extraction let params_lambda = 95
inline_for_extraction let params_kappa = 32
inline_for_extraction let params_n = 512
inline_for_extraction let params_xi = 27
inline_for_extraction let params_k = 1
inline_for_extraction let params_q = 4205569
inline_for_extraction let params_h = 30
inline_for_extraction let params_Le = 1586
inline_for_extraction let params_Ls = 1586
inline_for_extraction let params_B = 1048575
inline_for_extraction let params_d = 21
inline_for_extraction let params_bGenA = 19
inline_for_extraction let params_rateXOF = 168

let params_prf1 = Spec.SHA3.shake128
let params_prf2 = Spec.SHA3.shake128
let params_genA_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_gaussSampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_enc_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_ysampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_hashG = Spec.SHA3.shake128
let params_hashH_shake = Spec.SHA3.shake128

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
inline_for_extraction let computed_phi = 3768668
inline_for_extraction let computed_omega = 118029
inline_for_extraction let computed_phi_inv = 3764481
inline_for_extraction let computed_omega_inv = 590666
inline_for_extraction let computed_n_inv = 4197355

// Generated using gaussSigma2Sample_table.magma from the submission package.
let cdt_list: list nat =
  [02000000000000000000000000000000;
   03000000000000000000000000000000;
   03200000000000000000000000000000;
   03210000000000000000000000000000;
   03210200000000000000000000000000;
   03210201000000000000000000000000;
   03210201002000000000000000000000;
   03210201002001000000000000000000;
   03210201002001000200000000000000;
   03210201002001000200010000000000;
   03210201002001000200010000200000;
   03210201002001000200010000200001]
