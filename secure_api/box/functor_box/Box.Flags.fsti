(**
   This module contains flags that control the idealization of encryption and decryption,
   both of AE and of PKE. The flags indicate whether certain assumption are assumed to be
   true or not. Also, the refinements on the flag type indicate implications between the
   assumptions such as ae_ind_cpa /\ ae_int_ctxt ==> ae_ind_cca.
   Note, that for purposes of type-checking, the flags are not set. This
   ensures that the program is well typed for any permutation of set flags (that is permissible
   by the refinements).
*)
module Box.Flags

val prf_odh : bool

val ae_int_ctxt : bool

val ae_ind_cpa : b:bool{b ==> ae_int_ctxt} // ae_int_ctxt needs to be idealized before ae_ind_cpa

val ae_ind_cca : b:bool{b <==> (b2t ae_ind_cpa /\ ae_int_ctxt)}

val pkae : b:bool{(b <==> b2t ae_ind_cca) /\ ~prf_odh} // This should be an implication.

// Flags representing steps/games in the proof.
type game =
  | Game0
  | Game1
  | Game2
  | Game3

// This should ensure that we're always in a well-defined game and that the code only verifies for all games.
val current_game : g:game{
  match g with
  | Game0 -> not ae_ind_cpa /\ ~ae_int_ctxt /\ ~prf_odh /\ not pkae
  | Game1 -> not ae_ind_cpa /\ ~ae_int_ctxt /\ prf_odh /\ not pkae
  | Game2 -> not ae_ind_cca /\ prf_odh /\ not pkae
  | Game3 -> b2t ae_ind_cca /\ ~prf_odh /\ b2t pkae
  }
