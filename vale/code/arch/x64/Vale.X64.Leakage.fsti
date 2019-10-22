module Vale.X64.Leakage
open FStar.Mul
open Vale.X64.Machine_s
module S = Vale.X64.Machine_Semantics_s
open Vale.X64.Leakage_s
open Vale.X64.Leakage_Helpers
open Vale.X64.Leakage_Ins

val check_if_code_is_leakage_free (code:S.code) (ts:analysis_taints) (public_return:bool) : bool

// Only the args should be public
// REVIEW: move to specs directory?
val mk_analysis_taints (win:bool) (nbr_args:nat) : analysis_taints
