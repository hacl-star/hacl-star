module Meta.Interface

open FStar.Reflection
open FStar.Tactics

/// Local library
/// -------------

let assoc (#a: eqtype) #b (x: a) (l: list (a & b)): Tac b =
  match List.Tot.assoc x l with
  | Some x -> x
  | None -> fail "failure: assoc"

let rec zip #a #b (xs: list a) (ys: list b): Tac (list (a & b)) =
  match xs, ys with
  | x :: xs, y :: ys -> (x, y) :: zip xs ys
  | [], [] -> []
  | _ -> fail "invalid argument: zip"

/// Actual tactic
/// -------------
///
/// All function nodes in the call-graph are parameterized over an implicit
/// argument ``#i:t_i`` (coming first) that represents the specialization index.
///
/// The goal is to perform a call-graph rewriting, as follows.
///
/// At definition-site, every function ``f #i x`` is replaced by a function
///  ``mk_f #i (g1: g1_t i) ... (gn: gn_t i) x`` where:
///
/// - the gi are the ``specialize`` nodes reachable via a (possibly-empty) path
///   of ``inline`` nodes through the body of ``f``
/// - the gi_t are the types of the original gi, minus that index i, which has
///   been abstracted over, i.e. if gi had type ``#i:t_i -> t`` then ``gi_t`` is
///   ``fun #i:t_i -> t``
///
/// At call-site, when encountering ``f #i e``, we distinguish between two cases.
///
/// - If ``f`` is a specialize node: this becomes ``gi e`` and references the
///   bound variable instead of the global name
/// - If ``f`` is an inline node: this becomes ``mk_f #i gf1 ... gfn e`` where
///   ``gfi`` is the i-th function needed by f, i.e. one of our gk.
///
/// The intended usage is as follows.
///
/// - For each specialize node ``f``, clients instantiate as follows:
///   ``let f_specialized = mk_f I1 g1_specialized ... gn_specialized``
///   where the gn_specialized have been recursively generated the same way.
///
/// The new (rewritten) name of inline nodes is part of the global tactic state,
/// which we thread through as ``state`` below.
noeq
type mapping =
  | Inline: new_name:name -> mapping
  | Specialize: mapping

noeq
type state = {
  // A mapping from a top-level function f to:
  // - a boolean to indicate whether this function is parameterized over the index
  // - its type f_t (of type index -> Type OR Type if the function doesn't take the index);
  // - its inlining status; and
  // - the extra parameters it transitively needs (its g_i).
  seen: list (name & (bool & term & mapping & list name));
  // For debugging purposes only.
  indent: string;
}

/// Helpers
/// -------

let string_of_mapping = function
  | Inline _ -> "inline"
  | Specialize -> "specialize"

let rec string_of_name (n: name): Tac string =
  match n with
  | [ n ] -> n
  | n :: ns -> n ^ "_" ^ string_of_name ns
  | [] -> fail "impossible: empty name"

let rec suffix_name (n: name) (s: string): Tac name =
  match n with
  | [ m; n ] -> cur_module () @ [ String.lowercase m ^ "_" ^ n ^ s ]
  | n :: ns -> suffix_name ns s
  | [ _ ] | [] -> fail "impossible: empty name"

let has_attr (s: sigelt) (x: term) =
  List.Tot.existsb (fun t -> term_eq t x) (sigelt_attrs s)

let has_inline_for_extraction (s: sigelt) =
  List.Tot.existsb (function Inline_for_extraction -> true | _ -> false) (sigelt_quals s)

let is_implicit = function
  | Q_Implicit -> true
  | _ -> false

let rec push_pre (inv_bv: bv) (t: term): Tac term =
  match inspect t with
  | Tv_Arrow bv c ->
      let c =
        match inspect_comp c with
        | C_Eff us e a args ->
            if string_of_name e = "FStar_HyperStack_ST_Stack" then
              let args =
                match args with
                | (pre, qual) :: rest ->
                    let pre =
                      match inspect pre with
                      | Tv_Abs h body ->
                          let body = mk_app (`( /\ )) [ pack (Tv_Var inv_bv), Q_Explicit; body, Q_Explicit ] in
                          pack (Tv_Abs h body)
                      | _ ->
                          fail "impossible: argument to ST.Stack not a fun"
                    in
                    (pre, qual) :: rest
                | _ ->
                    fail ("impossible: effect not fully applied " ^ string_of_name e)
              in
              C_Eff us e a args
            else
              fail ("rewritten function has an unknown effect: " ^ string_of_name e)
        | C_Total t decr ->
            C_Total (push_pre inv_bv t) decr
        | _ ->
            fail ("rewritten type is neither a Tot or a stateful arrow: " ^ term_to_string t)
      in
      let c = pack_comp c in
      pack (Tv_Arrow bv c)
  | _ ->
      fail ("not just an arrow: " ^ term_to_string t)

let rec to_reduce t: Tac _ =
  match fst (collect_app t) with
  | Tv_FVar fv ->
      [ fv_to_string fv ]
  | Tv_Arrow bv c ->
      begin match inspect_comp c with
      | C_Total t _ ->
          to_reduce t
      | _ ->
          []
      end
  | _ ->
      []

let lambda_over_p (inv_bv: bv) (t: term): Tac term =
  pack (Tv_Abs (pack_binder inv_bv Q_Explicit) t)

let lambda_over_only_p (inv_bv: bv) (f_typ: term): Tac term =
  let fvs = to_reduce f_typ in
  print ("Names to reduce in " ^ term_to_string f_typ ^ ": " ^ String.concat ", " fvs);
  let f_typ = norm_term_env (top_env ()) [ delta_only (to_reduce f_typ) ] f_typ in
  lambda_over_p inv_bv (push_pre inv_bv f_typ)

// transforms #i:i -> t i into fun #i:i -> t i
let lambda_over_index_and_p (st: state) (f_name: name) (f_typ: term) (inv_bv: bv): Tac term =
  // this is a source of inefficiency... previously we could let this be a
  // user-defined abbreviation, such as cswap2_t
  let fvs = to_reduce f_typ in
  print ("Names to reduce in " ^ term_to_string f_typ ^ ": " ^ String.concat ", " fvs);
  let f_typ = norm_term_env (top_env ()) [ delta_only (to_reduce f_typ) ] f_typ in
  match inspect f_typ with
  | Tv_Arrow bv c ->
      let bv, qual = inspect_binder bv in
      if not (is_implicit qual) then
        fail ("The first parameter in the type of " ^ string_of_name f_name ^ " is not implicit");
      let { bv_sort = t } = inspect_bv bv in
      print (st.indent ^ "  Found index of type " ^ term_to_string t);
      let f_typ =
        match inspect_comp c with
        | C_Total t _ ->
            // ... -> ... (requires p) ...
            let t = push_pre inv_bv t in
            // fun p:Type. ... -> ... (requires p) ...
            let t = lambda_over_p inv_bv t in
            // fun #i:index -> fun p:Type. ... -> ... (requires p) ...
            pack (Tv_Abs (pack_binder bv Q_Implicit) t)
        | _ ->
            fail ("The first arrow of " ^ string_of_name f_name ^ " is impure")
      in
      f_typ
  | _ ->
      fail (string_of_name f_name ^ "is expected to have \
        an arrow type with the index as a first argument")

let must: _ -> Tac _ = function
  | Some x -> x
  | None -> fail "Invalid argument: must"

let tm_unit = `((()))

val add_check_with : term -> sigelt -> Tac sigelt
let add_check_with opts se =
  let attrs = sigelt_attrs se in
  let t = `(check_with (`#opts)) in
  set_sigelt_attrs (t :: attrs) se

/// Tactic core
/// -----------

let binder_is_legit f_name t_i binder: Tac bool =
  let bv, qual = inspect_binder binder in
  let { bv_sort = t; bv_ppname = name } = inspect_bv bv in
  let implicit = is_implicit qual in
  let right_type = term_eq t_i t in
  if implicit && not right_type then
    print ("WARNING: the first parameter of " ^ string_of_name f_name ^ " is \
      implicit but not of the index type");
  // Remember that the user asked to visit this function. Seems like a user mistake.
  if right_type && not implicit then
    fail ("the first parameter of " ^ string_of_name f_name ^ " is \
      not implicit but has the index type");
  right_type && implicit

#push-options "--z3rlimit 200"
let rec visit_function (t_i: term) (st: state) (f_name: name): Tac (state & list sigelt) =
  if (List.Tot.existsb (fun (name, _) -> name = f_name) st.seen) then
    let _ = print (st.indent ^ "Already visited " ^ string_of_name f_name) in
    // We don't need a three-state graph traversal since we automatically refuse
    // to visit a node marked with a let-rec.
    st, []

  else
    // Environment lookup.
    let f = lookup_typ (top_env ()) f_name in
    let f = match f with Some f -> f | None -> fail "unexpected: name not in the environment" in
    if not (has_attr f (`Meta.Attribute.specialize) || has_attr f (`Meta.Attribute.inline_)) then
      let _ = print (st.indent ^ "Not visiting " ^ string_of_name f_name) in
      // We want the user to specify which nodes should be traversed, otherwise,
      // we'd end up visiting the entire F* standard library.
      st, []
    else
      let _ = print (st.indent ^ "Visiting " ^ string_of_name f_name) in
      match inspect_sigelt f with
      | Sg_Let r _ _ f_typ f_body ->
        if r then
          fail ("user error: " ^  string_of_name f_name ^ " is recursive");

        let original_opts = sigelt_opts f in

        // Build a new function with proper parameters
        let old_indent = st.indent in
        let st = { st with indent = st.indent ^ "  " } in
        let new_name = suffix_name f_name "_higher" in

        // The function may be of the form fun (x: index) -> ...
        // We recognize and distinguish this index, if present.
        let index_bv, index_name, f_body =
          match inspect f_body with
          | Tv_Abs binder f_body' ->
              let bv, qual = inspect_binder binder in
              let { bv_sort = t; bv_ppname = name } = inspect_bv bv in
              if binder_is_legit f_name t_i binder then begin
                print (st.indent ^ "Found " ^ name ^ ", index of type " ^ term_to_string t);
                Some bv, name, f_body'
              end else
                // It can be convenient to specialize over a function without
                // the index as a parameter. In Curve, this is used to
                // specialize over store_felem64, a function that is already
                // specialized for the M64 value of the index, but that still
                // admits multiple implementations.
                None, "", f_body
          | _ ->
              fail (string_of_name f_name ^ "is expected to be a function!")
        in

        let inv_bv: bv = pack_bv ({
          bv_ppname = "p";
          bv_index = 355;
          bv_sort = `Type0;
        }) in

        let st, new_body, new_args, new_sigelts =
          match index_bv with
          | Some index_bv ->
              visit_body t_i (Some (pack (Tv_Var index_bv))) (pack (Tv_Var inv_bv)) st [] f_body
          | _ ->
              visit_body t_i None (pack (Tv_Var inv_bv)) st [] f_body
        in
        let st = { st with indent = old_indent } in

        // Update the state with a mapping and which extra arguments are
        // needed. Each function that has been transformed has a type that's a
        // function of the index.

        let m = if has_attr f (`Meta.Attribute.specialize) then Specialize else Inline new_name in
        let new_args, new_bvs = List.Tot.split new_args in

        // The type of ``f`` when it appears as a ``gi`` parameter, i.e. its ``gi_t``.
        let f_typ_name = suffix_name f_name "_higher_t" in
        let f_typ, f_typ_typ, has_index =
          match index_bv with
          | Some index_bv ->
              lambda_over_index_and_p st f_name f_typ inv_bv,
              mk_tot_arr [ pack_binder index_bv Q_Implicit ] (
                mk_tot_arr [ pack_binder inv_bv Q_Explicit ] (`Type0)),
              true
          | _ ->
              lambda_over_only_p inv_bv f_typ,
              mk_tot_arr [ pack_binder inv_bv Q_Explicit ] (`Type0),
              false
        in
        print (st.indent ^ "  let " ^ string_of_name f_typ_name ^ ": " ^
          term_to_string f_typ_typ ^ " = " ^
          term_to_string f_typ);
        let se_t = pack_sigelt (Sg_Let false (pack_fv f_typ_name) [] f_typ_typ f_typ) in
        let se_t = set_sigelt_quals [ NoExtract; Inline_for_extraction ] se_t in
        let se_t = match original_opts with
          | Some original_opts -> add_check_with original_opts se_t
          | _ -> se_t
        in
        let f_typ = pack (Tv_FVar (pack_fv f_typ_name)) in
        let st = { st with seen = (f_name, (has_index, f_typ, m, new_args)) :: st.seen } in

        // For debugging. This is very meta.
        let se_debug msg: Tac sigelt =
          let deps = map string_of_name new_args in
          let deps =
            match deps with
            | _ :: _ -> " (needs: " ^ String.concat ", " deps ^ ")"
            | _ -> ""
          in
          let quote_string s : Tac term = pack (Tv_Const (C_String s)) in
          pack_sigelt (Sg_Let
            false
            (pack_fv (suffix_name f_name "_higher_debug_print"))
            []
            (`unit)
            (`(let x: unit =
              _ by (
                print (`#(quote_string msg) ^ " " ^
                       (`#(quote_string (string_of_name new_name))) ^
                       `#(quote_string deps));
                exact tm_unit) in
              x)))
        in

        // Fast-path; just register the function as being a specialize node
        // but don't rewrite it or splice a new declaration.
        if false && List.length new_args = 0 then begin
          if not (has_inline_for_extraction f) then
            fail (string_of_name f_name ^ " should be inline_for_extraction");
          if not (Specialize? m) then
            fail (string_of_name f_name ^ " is marked as [@ inline_ ] but does not reach \
              any specializations");

          st, new_sigelts @ [ se_debug "Checking only a type:"; se_t ]
        end

        else

          // new_body is: fun (g1: g1_t i) ... (gn: gn_t i) x -> (e: f_t i)
          // i is free
          let new_body =
            fold_right (fun (_, bv) acc ->
              pack (Tv_Abs (mk_binder bv) acc)
            ) (zip new_args new_bvs) new_body
          in

          // Declaration for the new resulting function. We need to construct
          // the actual type of ``f``.
          // BUG: without the eta-expansion around mk_binder, "tactic got stuck".
          let new_body = pack (Tv_Abs (pack_binder inv_bv Q_Explicit) new_body) in
          let new_body =
            match index_bv with
            | Some index_bv -> pack (Tv_Abs (pack_binder index_bv Q_Implicit) new_body)
            | _ -> new_body
          in
          let new_typ =
            let new_binders = List.Tot.map (fun x -> mk_binder x) new_bvs in
            let new_binders = pack_binder inv_bv Q_Explicit :: new_binders in
            let app_inv (t: term): Tac term = pack (Tv_App t (pack (Tv_Var inv_bv), Q_Explicit)) in
            match index_bv with
            | Some index_bv ->
                mk_tot_arr
                  (pack_binder index_bv Q_Implicit :: new_binders)
                  (app_inv (pack (Tv_App f_typ (pack (Tv_Var index_bv), Q_Implicit))))
            | _ ->
                mk_tot_arr new_binders (app_inv f_typ)
          in
          let se = pack_sigelt (Sg_Let false (pack_fv new_name) [] new_typ new_body) in
          let se = set_sigelt_quals [ NoExtract; Inline_for_extraction ] se in
          let se = match original_opts with
            | Some original_opts -> add_check_with original_opts se
            | _ -> se
          in
          print (st.indent ^ "  let " ^ string_of_name new_name ^ ":\n" ^
            st.indent ^ term_to_string new_typ ^ "\n" ^
            st.indent ^ "=\n" ^
            st.indent ^ term_to_string new_body);

          st, new_sigelts @ [
            se_debug ("Checking type and definition [" ^ string_of_mapping m ^ "]:"); se_t; se
          ]

      | _ ->
          if has_attr f (`Meta.Attribute.specialize) then
            let inv_bv: bv = pack_bv ({
              bv_ppname = "p";
              bv_index = 355;
              bv_sort = `Type0;
            }) in

            // Assuming that this is a val, but we can't inspect it. Let's work around this.
            let t = pack (Tv_FVar (pack_fv f_name)) in
            let f_typ = tc (top_env ()) t in
            let f_typ, has_index =
              match inspect f_typ with
              | Tv_Arrow bv _ ->
                  if binder_is_legit f_name t_i bv then
                    lambda_over_index_and_p st f_name f_typ inv_bv, true
                  else
                    lambda_over_only_p inv_bv f_typ, false
              | _ ->
                  lambda_over_only_p inv_bv f_typ, false // fail (string_of_name f_name ^ " does not have an arrow type")
            in
            print (st.indent ^ "  Registering " ^ string_of_name f_name ^ " with type " ^
              term_to_string f_typ);
            let st = { st with seen = (f_name, (has_index, f_typ, Specialize, [])) :: st.seen } in
            st, []
          else
            st, []

and visit_many (t_i: term)
  (index_bv: option term)
  (inv_bv: term)
  (st: state)
  (bvs: list (name & bv))
  (es: list term):
  Tac (state & list term & list (name & bv) & list sigelt)
=
  let st, es, bvs, ses = fold_left (fun (st, es, bvs, ses) e ->
    let st, e, bvs, ses' = visit_body t_i index_bv inv_bv st bvs e in
    st, e :: es, bvs, ses @ ses'
  ) (st, [], bvs, []) es in
  let es = List.Tot.rev es in
  st, es, bvs, ses

and visit_body (t_i: term)
  (index_bv: option term)
  (inv_bv: term)
  (st: state) // state-passing
  (bvs: list (name & bv)) // state-passing
  (e: term):
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
      let es, qs = List.Pure.split es in
      let st, es, bvs, ses = visit_many t_i index_bv inv_bv st bvs es in
      let es = zip es qs in

      // If this is an application ...
      begin match inspect e with
      | Tv_FVar fv ->
          // ... of a top-level name ...
          let fv = inspect_fv fv in
          let st, ses' = visit_function t_i st fv in
          let ses = ses @ ses' in
          // visit_function fills out st.seen with an entry for this lid, if
          // this is something we wish to rewrite
          begin match List.Tot.assoc fv st.seen with
          | Some (has_index, _, map, fns) ->
              print (st.indent ^ "Rewriting application of " ^ string_of_name fv);

              let index_arg, es =
                if has_index then
                  match es with
                  | (e, Q_Implicit) :: es ->
                      Some e, es
                  | _ ->
                      fail "this application does not seem to start with an index"
                else
                  None, es
              in

              // A helper that says: I will need a specialized instance of `name`,
              // so allocate an extra parameter for this current function if
              // needed.
              let allocate_bv_for name bvs: Tac _ =
                match List.Tot.assoc name bvs with
                | Some bv ->
                    print (st.indent ^ string_of_name name ^ " already has a bv");
                    // fv needs to receive a specialized instance of name;
                    // it's already found in this function's own bvs
                    (pack (Tv_Var bv), Q_Explicit), bvs
                | None ->
                    // this is the first time the current function needs to
                    // receive a specialized instance of name; add it to this
                    // function's own bvs
                    let needs_index, typ, _, _ = assoc name st.seen in
                    if needs_index && not (Some? index_arg) then
                      fail ("Index inconsistency in bv for " ^ string_of_name name);

                    print (st.indent ^ "Allocating bv for " ^ string_of_name name ^ " at type " ^
                      "app <" ^ term_to_string typ ^ "> <" ^
                      (if needs_index then term_to_string (must index_arg) else "no-index") ^ ">");

                    let typ =
                      if needs_index then pack (Tv_App typ (must index_arg, Q_Implicit)) else typ
                    in
                    let typ = pack (Tv_App typ (inv_bv, Q_Explicit)) in
                    let bv: bv = pack_bv ({
                      bv_ppname = "arg_" ^ string_of_name name;
                      bv_index = 42;
                      bv_sort = typ
                    }) in
                    (pack (Tv_Var bv), Q_Explicit), (name, bv) :: bvs
              in

              begin match map with
              | Inline fv ->
                  // fv has been rewritten to take fns as extra arguments for the
                  //   specialize nodes reachable through the body of fv; we need
                  //   ourselves to take a dependency on those nodes
                  let extra_args, bvs = fold_left (fun (extra_args, bvs) name ->
                    let term, bvs = allocate_bv_for name bvs in
                    term :: extra_args, bvs
                  ) ([], bvs) fns in
                  let extra_args = List.rev extra_args in
                  let extra_args = (inv_bv, Q_Explicit) :: extra_args in
                  let extra_args =
                    // Inline nodes retain their index (if any).
                    if has_index then (must index_bv, Q_Implicit) :: extra_args else extra_args
                  in

                  let e = mk_app (pack (Tv_FVar (pack_fv fv))) (extra_args @ es) in
                  st, e, bvs, ses

              | Specialize ->
                  // Specialized nodes are received as parameters and no longer have the index.
                  let e, bvs = allocate_bv_for fv bvs in
                  let e = mk_app (fst e) es in
                  st, e, bvs, ses
              end

          | None ->
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
      let st, e, bvs, ses = visit_body t_i index_bv inv_bv st bvs e in
      let e = pack (Tv_Abs b e) in
      st, e, bvs, ses

  | Tv_Match scrut branches ->
      let st, scrut, bvs, ses = visit_body t_i index_bv inv_bv st bvs scrut in
      let pats, es = List.Tot.split branches in
      let st, es, bvs, ses' = visit_many t_i index_bv inv_bv st bvs es in
      let branches = zip pats es in
      st, pack (Tv_Match scrut branches), bvs, ses @ ses'

  | Tv_Let r attrs bv e1 e2 ->
      let st, e1, bvs, ses = visit_body t_i index_bv inv_bv st bvs e1 in
      let st, e2, bvs, ses' = visit_body t_i index_bv inv_bv st bvs e2 in
      let e = pack (Tv_Let r attrs bv e1 e2) in
      st, e, bvs, ses @ ses'

  | Tv_AscribedT e t tac ->
      let st, e, bvs, ses = visit_body t_i index_bv inv_bv st bvs e in
      let e = pack (Tv_AscribedT e t tac) in
      st, e, bvs, ses

  | Tv_AscribedC e c tac ->
      let st, e, bvs, ses = visit_body t_i index_bv inv_bv st bvs e in
      let e = pack (Tv_AscribedC e c tac) in
      st, e, bvs, ses

  | Tv_Arrow _ _
  | Tv_Type _
  | Tv_Uvar _ _
  | Tv_Refine _ _
  | Tv_Unknown ->
      // Looks like we ended up visiting a type argument of an application.
      st, e, bvs, []

[@plugin]
let specialize (t_i: term) (names: list term): Tac decls =
  let names = map (fun name ->
    match inspect name with
    | Tv_FVar fv -> inspect_fv fv
    | _ -> fail "error: argument to specialize is not a top-level name"
  ) names in
  let st = { seen = []; indent = "" } in
  let _, ses = fold_left (fun (st, ses) name ->
    let st, ses' = visit_function t_i st name in
    print (string_of_int (List.length ses') ^ " declarations generated");
    st, ses @ ses'
  ) (st, []) names in
  ses

// TODO:
// - quote and splice the internal state of the tactic as `tactic_state`; this way:
//   - a new tactic instantiate can re-load the state, then
//   - instantiate each one of the specialize nodes, and
//   - mark as private those that were not arguments to the tactic initially
// - figure out the bug in Example (might pop up later, 0b1611a5f03d9f91359eae54403da42957cfeb67)
// - figure out the issue with type annotations sending F* off the rails
//   (88c8ec01e066ab0adc550c2bdba4212ff5e7c5c9)
// - is there any way to not do as much work and skip re-checking some things?
// - the order of arguments is unspecified and gives surprising results; any way
//   we can make it more stable?
