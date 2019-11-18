module Vale.Lib.Tactics
open FStar.Mul
open FStar.Tactics
open FStar.Tactics.Derived
open FStar.Reflection.Formula


(***** Tactic to destruct conjuctions in context *)

private val __squash_and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi
let __squash_and_elim #p #q #phi p_and_q f = ()

let squash_and_elim (t : term) : Tac unit =
    let ae = `__squash_and_elim in
    apply_lemma (mk_e_app ae [t])

let tf (t : term) =
  match unsquash t with
  | None -> and_elim
  | _ -> squash_and_elim

let rec iterate_env (bs : binders) : Tac unit =
    match bs with
    | [] -> ()
    | b :: bs ->
        let ty = type_of_binder b in
        let elim = tf ty in
        begin
          match term_as_formula_total ty with
          | And _ _  ->
            elim (pack (Tv_Var (bv_of_binder b)));
            clear b;
            let t1 = implies_intro () in
            let t2 = implies_intro () in
            iterate_env (t1 :: t2 :: bs)
          | _ -> iterate_env bs
        end

// Destructs all propositions of the form [A /\ B] (or [squash (A /\ B)]) in the context
let destruct_conj () : Tac unit =
   let e = cur_env () in
   iterate_env (binders_of_env e)
