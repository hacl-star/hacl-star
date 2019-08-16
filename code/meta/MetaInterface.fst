module MetaInterface

open FStar.Tactics
open FStar.Reflection

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
}

let rec string_of_name (n: name): Tot string =
  match n with
  | [] -> ""
  | n :: ns -> n ^ "." ^ string_of_name ns

let rec suffix_name (n: name) (s: string): Tac name =
  match n with
  | [ n ] -> [ n ^ s ]
  | n :: ns -> n :: suffix_name ns s
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
  exact (pack_ln (Tv_Abs (mk_binder bv) (pack_ln (Tv_Var bv))))
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
    // We don't need a three-state graph traversal since we automatically refuse
    // to visit a node marked with a let-rec.
    st, []

  else
    // Environment lookup.
    let f = lookup_typ (cur_env ()) f_name in
    let f = match f with Some f -> f | None -> fail "unexpected: name not in the environment" in
    let f_typ, f_body = match inspect_sigelt f with
      | Sg_Let r _ _ f_typ f_body ->
        if r then
          fail ("user error: " ^  string_of_name f_name ^ " is recursive")
        else
          f_typ, f_body
      | _ ->
        fail "unexpected: visited a node that's not a let"
    in

    // Build a new function with proper parameters
    let new_name = suffix_name f_name "_inline" in
    let st, new_body, new_args, new_sigelts = visit_body st f_body [] in
    let new_body = List.Tot.fold_right (fun (_, bv) acc ->
        pack_ln (Tv_Abs (mk_binder bv) acc)
      ) new_args new_body
    in
    let new_args, _ = List.Tot.split new_args in

    // Build updated state
    let m = if has_attr f (`MetaAttribute.specialize) then Specialize else Inline new_name in
    let st = { st with seen = (f_name, (f_typ, m, new_args)) :: st.seen } in
    st, new_sigelts

and visit_body (st: state) (e: term) (specialized: list (name & bv)):
  Tac (state & term & list (name & bv) & list sigelt)
=
  fail "todo"
