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


// Flags representing steps/games in the proof.
type game =
  | Game0
  | Game1
  | Game2
  | Game3
  | Game4
  | Game5

(** The current game step indicates which modules are currently idealized,
    not idealized or for which modules idealization is not fixed.
    For the exact state of the game at each step, see the individual flags
    below.
*)
val current_game : g:game
//{
//  match g with
//  | Game0 -> not ae_ind_cpa /\ ~ae_int_ctxt /\ ~prf_odh /\ not pkae
//  | Game1 -> not ae_ind_cpa /\ ~ae_int_ctxt /\ not pkae
//  | Game2 -> prf_odh /\ not pkae
//  | Game3 -> b2t ae_ind_cca /\ prf_odh /\ not pkae
//  | Game4 -> b2t ae_ind_cca /\ not pkae
//  | Game5 -> b2t ae_ind_cca /\ ~prf_odh /\ b2t pkae
//  }

val prf_odh : b:bool{(Game0? current_game ==> ~b)
                     /\ (Game1? current_game ==> (b \/ ~b))
                     /\ (Game2? current_game ==> b)
                     /\ (Game3? current_game ==> b)
                     /\ (Game4? current_game ==> (b \/ ~b))
                     /\ (Game5? current_game ==> ~b)
                     }

val ae_int_ctxt : b:bool{(Game0? current_game ==> ~b)
                         /\ (Game1? current_game ==> ~b)
                         /\ (Game2? current_game ==> (b \/ ~b))
                         /\ (Game3? current_game ==> b)
                         /\ (Game4? current_game ==> b)
                         /\ (Game5? current_game ==> b)
                         }

val ae_ind_cpa : b:bool{(Game0? current_game ==> ~b)
                        /\ (Game1? current_game ==> ~b)
                        /\ (Game2? current_game ==> (b \/ ~b))
                        /\ (Game3? current_game ==> b)
                        /\ (Game4? current_game ==> b)
                        /\ (Game5? current_game ==> b)
                        }

val ae_ind_cca : b:bool{(Game0? current_game ==> ~b)
                        /\ (Game1? current_game ==> ~b)
                        /\ (Game2? current_game ==> (b \/ ~b))
                        /\ (Game3? current_game ==> b)
                        /\ (Game4? current_game ==> b)
                        /\ (Game5? current_game ==> b)
                        }

val pkae : b:bool{(Game0? current_game ==> ~b)
                  /\ (Game1? current_game ==> ~b)
                  /\ (Game2? current_game ==> ~b)
                  /\ (Game3? current_game ==> ~b)
                  /\ (Game4? current_game ==> ~b)
                  /\ (Game5? current_game ==> b)
                  }
