module QTesla.Params

open Lib.IntTypes

let params_lambda = 160 // security parameter
let params_kappa = 32 // output length of hash function in bytes (spec lists them in bits, so convert)
let params_n = 1024 // Dimension
let params_xi = 12     // Gaussian sampler scaling parameter
let params_k = 1       // #R-LWE samples (number of polynomials in e, t, a, etc)
let params_q = 8404993 // modulus
let params_h = 48      // # of nonzero entries of output elements of Enc
let params_Le = 1147   // bound on e_i for checkE
let params_Ls = 1233   // bound on s for checkS
let params_B = 2097151 // interval the randomness is chosing from during signing
let params_d = 22      // number of rounded bits
let params_bGenA = 38  // number of blocks requested to SHAKE128 for GenA

let params_rateXOF = 168

let params_prf1 = Spec.SHA3.shake128
let params_prf2 = params_prf1
let params_genA_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_gaussSampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_enc_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_ysampler_xof = Spec.QTesla.CShake.cshake128_qtesla
let params_hashG = Spec.SHA3.shake128
let params_hashH_shake = Spec.SHA3.shake128

// See the GenerateNTTConstants-Magma.txt script for computing these five
// constants used in NTT.
let computed_phi = 5216957
let computed_omega = 3851906
let computed_phi_inv = 4276303
let computed_omega_inv = 7267723
let computed_n_inv = 8396785

// Generated using gaussSigma2Sample_table.magma from the submission package.
unfold let cdt_list: list nat =
  [000002000000000000000000000000000000000000000000; 
   000003000000000000000000000000000000000000000000;
   000003200000000000000000000000000000000000000000;
   000003210000000000000000000000000000000000000000;
   000003210200000000000000000000000000000000000000;
   000003210201000000000000000000000000000000000000;
   000003210201002000000000000000000000000000000000;
   000003210201002001000000000000000000000000000000;
   000003210201002001000200000000000000000000000000;
   000003210201002001000200010000000000000000000000;
   000003210201002001000200010000200000000000000000;
   000003210201002001000200010000200001000000000000;
   000003210201002001000200010000200001000002000000;
   000003210201002001000200010000200001000002000001]
