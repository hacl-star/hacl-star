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

//abstract type flags_module =
//  | FM:
//    prf_odh: bool ->
//    ae_int_ctxt: bool ->
//    ae_ind_cpa : (b:bool{b ==> ae_int_ctxt}) ->
//    ae_ind_cca : (b:bool{b <==> (b2t ae_ind_cpa /\ ae_int_ctxt)}) ->
//    pkae_int_ctxt : (b:bool{b <==> ae_int_ctxt}) ->
//    pkae_ind_cpa : (b:bool{b <==> b2t ae_ind_cpa}) ->
//    pkae : (b:bool{b ==> (((b2t ae_ind_cca) /\ prf_odh) /\ (b2t pkae_int_ctxt /\ b2t pkae_ind_cpa))}) ->
//    state : (b:bool{b2t ae_ind_cca \/ prf_odh ==> b}) ->
//    flags_module

val prf_odh : bool

val ae_int_ctxt : bool

val ae_ind_cpa : b:bool{b ==> ae_int_ctxt} // ae_int_ctxt needs to be idealized before ae_ind_cpa

val ae_ind_cca : b:bool{b <==> (b2t ae_ind_cpa /\ ae_int_ctxt)}

val pkae_int_ctxt : b:bool{b <==> ae_int_ctxt}

val pkae_ind_cpa : b:bool{b <==> b2t ae_ind_cpa}

//val pkae : b:bool{b ==> (((b2t ae_ind_cca) /\ prf_odh) /\ (b2t pkae_int_ctxt /\ b2t pkae_ind_cpa))}
val pkae : b:bool{(b <==> b2t pkae_int_ctxt /\ b2t pkae_ind_cpa)} // This should be an implication.

val state : b:bool{b2t ae_ind_cca \/ prf_odh ==> b}

// Flags representing steps/games in the proof.

type game =
  | Game0
  | Game1
  | Game2
  | Game3
// This flag expresses our claim of functional equality between our construction and PKAE in unidealized state.
val game0 : b:bool{b <==> not ae_ind_cpa /\ ~ae_int_ctxt /\ ~prf_odh /\ not pkae}

val game1 : b:bool{b <==> not ae_ind_cpa /\ ~ae_int_ctxt /\ prf_odh /\ not pkae}

val game2 : b:bool{b <==> not ae_ind_cca /\ prf_odh /\ not pkae}

// This flag expresses our claim of functional equality between our construction and PKAE in idealized state.
// We have to leafe prf_odh unidealized, so we can prove that zeroes are encrypted.
val game3 : b:bool{b <==> b2t ae_ind_cca /\ ~prf_odh /\ b2t pkae} // This should imply that forall ids, honest i = True

// This should ensure that we're always in a well-defined game and that the code only verifies for all games.
val current_game : g:game{
  match g with
  | Game0 -> b2t game0
  | Game1 -> b2t game1
  | Game2 -> b2t game2
  | Game3 -> b2t game3
  }
