module Vale.Lib.Tactics
open FStar.Mul
open FStar.Tactics.V2
open FStar.Tactics.V2.Derived
open FStar.Reflection.V2.Formula


(***** Tactic to destruct conjuctions in context *)

private val __squash_and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi
let __squash_and_elim #p #q #phi p_and_q f = ()

let squash_and_elim (t : term) : Tac unit =
    let ae = `__squash_and_elim in
    apply_lemma (mk_e_app ae [t])

let tf (t : term) : Tot (term -> Tac unit) =
  match unsquash_term t with
  | None -> and_elim
  | _ -> squash_and_elim

let rec iterate_env (bs : bindings) : Tac unit =
    match bs with
    | [] -> ()
    | b :: bs ->
        let ty = type_of_binding b in
        let elim = tf ty in
        begin
          match term_as_formula_total ty with
          | And _ _  ->
            elim (binding_to_term b);
            clear b;
            let t1 = implies_intro () in
            let t2 = implies_intro () in
            iterate_env (t1 :: t2 :: bs)
          | _ -> iterate_env bs
        end

// Destructs all propositions of the form [A /\ B] (or [squash (A /\ B)]) in the context
let destruct_conj () : Tac unit =
   iterate_env (cur_vars ())
