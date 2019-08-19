module MetaInterface

open FStar.Reflection
open FStar.Tactics

// Nodes in the call-graph are either specialize nodes or inline nodes.
// - Specialize nodes are expected to be constructed and provided by the client.
// - Inline nodes disappear at extraction-time via the "inline for extraction"
//   mechanism.
//
// Every (function) definition of the call-graph is thus rewritten to take as
// extra parameters all specialized functions reachable through its body.
//
// Every function call is rewritten.
// - Specialized calls become calls to function parameters.
// - Inlined calls become calls to rewritten inline functions, passing all the
//   needed extra parameters.
noeq
type mapping =
  | Inline: new_name:name -> mapping
  | Specialize: mapping

noeq
type state = {
  // A mapping from a top-level function name to its type; its inlining status;
  // and the extra parameters it transitively needs.
  seen: list (name & (term & mapping & list name));
  indent: string;
}

let rec string_of_name (n: name): Tac string =
  match n with
  | [ n ] -> n
  | n :: ns -> n ^ "." ^ string_of_name ns
  | [] -> fail "impossible: empty name"

let rec suffix_name (n: name) (s: string): Tac name =
  match n with
  | [ n ] -> cur_module () @ [ n ^ s ]
  | n :: ns -> suffix_name ns s
  | [] -> fail "impossible: empty name"

let assoc (#a: eqtype) #b (x: a) (l: list (a & b)): Tac b =
  match List.Tot.assoc x l with
  | Some x -> x
  | None -> fail "failure: assoc"

let has_attr (s: sigelt) (x: term) =
  List.Tot.existsb (fun t -> term_eq t x) (sigelt_attrs s)

// A demo on how to allocate a fresh variable and pack it as a binder.
let _: int -> int = _ by (
  let bv: bv = pack_bv ({ bv_ppname = "x"; bv_index = 42; bv_sort = `int }) in
  exact (pack (Tv_Abs (mk_binder bv) (pack (Tv_Var bv))))
)

let allocate_bv_for (st: state) (allocated: list (name & bv)) (n: name) =
  try
    assoc n allocated
  with
  | TacticFailure _ ->
      let typ, _, _ = assoc n st.seen in
      // watch out for case?
      let bv: bv = pack_bv ({
        bv_ppname = string_of_name n;
        bv_index = 42;
        bv_sort = typ
      }) in
      bv
  | _ ->
      fail "allocate_bv_for: unknown_failure"

let rec visit_function (st: state) (f_name: name): Tac (state & list sigelt) =
  if (List.Tot.existsb (fun (name, _) -> name = f_name) st.seen) then
    let _ = print (st.indent ^ "Already visited " ^ string_of_name f_name) in
    // We don't need a three-state graph traversal since we automatically refuse
    // to visit a node marked with a let-rec.
    st, []

  else
    // Environment lookup.
    let f = lookup_typ (cur_env ()) f_name in
    let f = match f with Some f -> f | None -> fail "unexpected: name not in the environment" in
    if not (has_attr f (`MetaAttribute.specialize) || has_attr f (`MetaAttribute.inline_)) then
      let _ = print (st.indent ^ "Not visiting " ^ string_of_name f_name) in
      // We want to user to specify which nodes should be traversed, otherwise,
      // we'd end up visiting the entire F* standard library.
      st, []
    else
      let _ = print (st.indent ^ "Visiting " ^ string_of_name f_name) in
      match inspect_sigelt f with
      | Sg_Let r _ _ f_typ f_body ->
        if r then
          fail ("user error: " ^  string_of_name f_name ^ " is recursive")
        else
          // Build a new function with proper parameters
          let old_indent = st.indent in
          let st = { st with indent = st.indent ^ "  " } in
          let new_name = suffix_name f_name "_inline" in
          let st, new_body, new_args, new_sigelts = visit_body st [] f_body in
          let st = { st with indent = old_indent } in
          let new_body = fold_right (fun (_, bv) acc ->
              pack (Tv_Abs (mk_binder bv) acc)
            ) new_args new_body
          in
          let new_args, new_bvs = List.Tot.split new_args in

          // Update the state with a mapping and which extra arguments are needed.
          let m = if has_attr f (`MetaAttribute.specialize) then Specialize else Inline new_name in
          let st = { st with seen = (f_name, (f_typ, m, new_args)) :: st.seen } in

          // Declaration for the new resulting function.
          // BUG: without the eta-expansion around mk_binder, "tactic got stuck".
          let new_typ = mk_tot_arr (List.Tot.map (fun x -> mk_binder x) new_bvs) f_typ in
          let se = pack_sigelt (Sg_Let false (pack_fv new_name) [] new_typ new_body) in
          let _ = print (st.indent ^ "New body for " ^ string_of_name new_name ^ ":\n" ^
            st.indent ^ term_to_string new_body) in
          let _ = print (st.indent ^ "New type for " ^ string_of_name new_name ^ ":\n" ^
            st.indent ^ term_to_string new_typ) in

          st, new_sigelts @ [ se ]

      | _ ->
          if has_attr f (`MetaAttribute.specialize) then
            // Assuming that this is a val, but we can't inspect it. Let's work around this.
            let t = pack (Tv_FVar (pack_fv f_name)) in
            let f_typ = tc t in
            let st = { st with seen = (f_name, (f_typ, Specialize, [])) :: st.seen } in
            st, []
          else
            st, []

and visit_body (st: state) (bvs: list (name & bv)) (e: term):
  Tac (state & term & list (name & bv) & list sigelt)
=
  // st is state that is threaded through
  // bvs are the extra parameters for this function we have allocated; threaded
  //   through as well to avoid allocating the same thing twice
  // ses is strictly bottom-up
  match inspect e with
  | Tv_App _ _ ->
      let e, es = collect_app e in

      // Recursively visit arguments
      let st, es, bvs, ses = fold_left (fun (st, es, bvs, ses) (e, q) ->
        let st, e, bvs, ses' = visit_body st bvs e in
        st, (e, q) :: es, bvs, ses @ ses'
      ) (st, [], bvs, []) es in
      let es = List.Tot.rev es in

      // If this is an application ...
      begin match inspect e with
      | Tv_FVar fv ->
          // ... of a top-level name ...
          let fv = inspect_fv fv in
          let st, ses' = visit_function st fv in
          let ses = ses @ ses' in
          begin try
            // ... that is one of the names of our call-graph
            let _, map, fns = assoc fv st.seen in
            let _ = print (st.indent ^ "Rewriting application of " ^ string_of_name fv) in

            // A helper that says: I will need a specialized instance of `name`,
            // so allocate an extra parameter for this current function if
            // needed.
            let allocate_bv_for name bvs: Tac _ =
              match List.Tot.assoc name bvs with
              | Some bv ->
                  // fv needs to receive a specialized instance of name;
                  // it's already found in this function's own bvs
                  (pack (Tv_Var bv), Q_Explicit), bvs
              | None ->
                  // this is the first time the current function needs to
                  // receive a specialized instance of name; add it to this
                  // function's own bvs
                  let _ = print (st.indent ^ "Allocating bv for " ^ string_of_name name) in
                  let typ, _, _ = assoc name st.seen in
                  let bv: bv = pack_bv ({
                    bv_ppname = "arg_" ^ string_of_name name;
                    bv_index = 42;
                    bv_sort = typ
                  }) in
                  (pack (Tv_Var bv), Q_Explicit), (name, bv) :: bvs
            in

            match map with
            | Inline fv ->
                // fv has been rewritten to take fns as extra arguments for the
                //   specialize nodes reachable through the body of fv; we need
                //   ourselves to take a dependency on those nodes
                let extra_args, bvs = fold_left (fun (extra_args, bvs) name ->
                  let term, bvs = allocate_bv_for name bvs in
                  term :: extra_args, bvs
                ) ([], bvs) fns in
                let extra_args = List.rev extra_args in

                let e = mk_app (pack (Tv_FVar (pack_fv fv))) (extra_args @ es) in
                st, e, bvs, ses

            | Specialize ->
                // Base case: we just found an application of a function from the interface.
                let e, bvs = allocate_bv_for fv bvs in
                let e = mk_app (fst e) es in
                st, e, bvs, ses
          with
          | _ ->
              let e = mk_app e es in
              st, e, bvs, ses
          end
      | _ ->
          let e = mk_app e es in
          st, e, bvs, ses
      end

  | Tv_Var _ | Tv_BVar _ | Tv_FVar _
  | Tv_Const _ ->
      st, e, bvs, []

  | Tv_Abs b e ->
      let st, e, bvs, ses = visit_body st bvs e in
      let e = pack (Tv_Abs b e) in
      st, e, bvs, ses

  | _ ->
      fail ("todo: recursively visit term structurally: " ^ term_to_string e)

let specialize (names: list term): Tac _ =
  let names = map (fun name ->
    match inspect name with
    | Tv_FVar fv -> inspect_fv fv
    | _ -> fail "error: arguemnt to specialize is not a top-level name"
  ) names in
  let st = { seen = []; indent = "" } in
  let _, ses = fold_left (fun (st, ses) name ->
    let st, ses' = visit_function st name in
    st, ses @ ses'
  ) (st, []) names in
  exact (quote ses)
