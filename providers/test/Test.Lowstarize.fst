module Test.Lowstarize

open FStar.Tactics
open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack

// We rely on a single user-level function: h, which indicates that the string
// is hex-encoded. Otherwise, the string becomes a call to C.String.of_literal.

assume new type hex_encoded
assume val h: string -> hex_encoded

// A bunch of helpers. TODO: fail gracefully if there is a character outside of the hex range.

noextract
let int_of_hex (c: FStar.Char.char): Tot (c:nat{c<16}) =
  match c with
  | '0' -> 0
  | '1' -> 1
  | '2' -> 2
  | '3' -> 3
  | '4' -> 4
  | '5' -> 5
  | '6' -> 6
  | '7' -> 7
  | '8' -> 8
  | '9' -> 9
  | 'a' | 'A' -> 10
  | 'b' | 'B' -> 11
  | 'c' | 'C' -> 12
  | 'd' | 'D' -> 13
  | 'e' | 'E' -> 14
  | 'f' | 'F' -> 15
  | _ -> let _ = FStar.IO.debug_print_string "illegal character" in admit ()

noextract
let uint8_of_hex c1 c2 =
  FStar.UInt8.uint_to_t FStar.Mul.(int_of_hex c1 * 16 + int_of_hex c2)

noextract
let rec as_uint8s acc (cs: list FStar.Char.char{List.Tot.length cs % 2 = 0}): Tot (list FStar.UInt8.t) (decreases cs) =
  match cs with
  | c1 :: c2 :: cs ->
      as_uint8s (uint8_of_hex c1 c2 :: acc) cs
  | [] ->
      List.rev acc


noextract
let destruct_string e =
  match inspect_ln e with
  | Tv_Const (C_String s) -> Some s
  | _ -> None

noextract
let is_some = function Some _ -> true | None -> false

noextract
let is_string e =
  is_some (destruct_string e)

noextract
let must (x: option 'a): Tac 'a =
  match x with
  | Some x -> x
  | None -> fail "must"

noextract
let rec destruct_list (e: term): Tac (option (list term)) =
  let hd, args = collect_app e in
  match inspect_ln hd, args with
  | Tv_FVar fv, [ _; hd, _; tl, _ ] ->
      if inspect_fv fv = cons_qn then
        Some (hd :: must (destruct_list tl))
      else
        None
  | Tv_FVar fv, _ ->
      if inspect_fv fv = nil_qn then
        Some []
      else
        None
  | _ ->
      None

noextract
let is_list e =
  match inspect_ln (fst (collect_app e)) with
  | Tv_FVar fv ->
      inspect_fv fv = nil_qn || inspect_fv fv = cons_qn
  | _ ->
      false

noextract
let mktuple_qns =
  [ mktuple2_qn; mktuple3_qn; mktuple4_qn; mktuple5_qn; mktuple6_qn;
    mktuple7_qn; mktuple8_qn ]

noextract
let destruct_tuple (e: term): option (list term) =
  let hd, args = collect_app e in
  match inspect_ln hd with
  | Tv_FVar fv ->
      if List.Tot.contains (inspect_fv fv) mktuple_qns then
        Some (List.Tot.concatMap (fun (t, q) ->
          match q with
          | Q_Explicit -> [t]
          | _ -> []
        ) args)
      else
        None
  | _ ->
      None

noextract
let is_tuple (e: term) =
  match inspect_ln (fst (collect_app e)) with
  | Tv_FVar fv ->
      List.Tot.contains (inspect_fv fv) mktuple_qns
  | _ ->
      false

noextract
let destruct_hex (e: term) =
  let hd, tl = collect_app e in
  if term_eq (`h) hd then begin
    assume (List.Tot.length tl > 0);
    destruct_string (fst (List.Tot.hd tl))
  end else
    None

noextract
let is_hex e =
  is_some (destruct_hex e)

// Main Tactic. This tactic fetches a top-level term and defines another,
// Low*-ized top-level term for it, where:
// - hex-encoded strings are lifted as top-level constant uint8 arrays
// - references to hex-encoded strings are replaced by a pair of the length
//   of the corresponding array, and a reference to that array
// - lists are lifted as top-level arrays (using gcmalloc_of_list)
// - strings that are not marked as hex-encoded are lifted to C.String.t
// - tuples are traversed transparently
// - everything else is left as-is
//
// TODO: instead of pairs, use a dependent type that ties together an array and
// its length

let gensym = string * nat

noextract
let fresh (uniq: gensym): Tac (gensym * name) =
  (fst uniq, snd uniq + 1), cur_module () @ [ fst uniq ^ string_of_int (snd uniq) ]

noextract
let mk_gcmalloc_of_list (uniq: gensym) (arg: term) (l: nat{l < pow2 32}): Tac (gensym * sigelt * term) =
  let def: term = pack (Tv_App
    (pack (Tv_App (`LowStar.Buffer.gcmalloc_of_list) (`HS.root, Q_Explicit)))
    (arg, Q_Explicit)
  ) in
  let uniq, name = fresh uniq in
  let fv: fv = pack_fv name in
  let t: term = pack Tv_Unknown in
  let se: sigelt = pack_sigelt (Sg_Let false fv [] t def) in
  let thanks_guido_for_the_workaround = pack (Tv_FVar fv) in
  uniq, se, `(`#thanks_guido_for_the_workaround, FStar.UInt32.uint_to_t (`@l))

noextract
let lowstarize_hex (uniq: gensym) (s: string): Tac (gensym * sigelt * term) =
  if String.length s % 2 <> 0 then
    fail ("The following string has a non-even length: " ^ s)
  else
    let constants = as_uint8s [] (String.list_of_string s) in
    let l = String.length s in
    assume (l < pow2 32);
    mk_gcmalloc_of_list uniq (quote constants) (l / 2)

// Dependency analysis bug: does not go inside quotations (#1496)

module Whatever = C.String

noextract
let lowstarize_string (s: string): Tac term =
  `(C.String.of_literal (`@s))

noextract
let rec lowstarize_expr (uniq: gensym) (e: term): Tac (gensym * list sigelt * term) =
  let _ = print ("about to normalize: " ^ term_to_string e ^ "\n") in
  let e = norm_term [ delta; zeta; iota; primops ] e in
  let _ = print ("hitting: " ^ term_to_string e ^ "\n") in
  if is_hex e then
    let uniq, se, e = lowstarize_hex uniq (must (destruct_hex e)) in
    uniq, [ se ], e
  else if is_string e then
    uniq, [], lowstarize_string (must (destruct_string e))
  else if is_list e then
    lowstarize_list uniq (must (destruct_list e))
  else if is_tuple e then
    lowstarize_tuple uniq (must (destruct_tuple e))
  else
    uniq, [], e

and lowstarize_list (uniq: gensym) (es: list term): Tac (gensym * list sigelt * term) =
  let uniq, ses, es = fold_left (fun (uniq, ses, es) e ->
    let uniq, se, e = lowstarize_expr uniq e in
    uniq, List.Tot.rev_acc se ses, e :: es
  ) (uniq, [], []) es in
  let es = List.rev es in
  let l = List.length es in
  assume (l < pow2 32);
  let uniq, se, e = mk_gcmalloc_of_list uniq (mk_list es) l in
  uniq, List.rev (se :: ses), e

and lowstarize_tuple (uniq: gensym) (es: list term): Tac (gensym * list sigelt * term) =
  let uniq, ses, es = fold_left (fun (uniq, ses, es) e ->
    let uniq, se, e = lowstarize_expr uniq e in
    uniq, List.Tot.rev_acc se ses, e :: es
  ) (uniq, [], []) es in
  let es = List.rev es in
  uniq, List.rev ses, mktuple_n es

noextract
let lowstarize_toplevel src dst: Tac unit =
  // lookup_typ does not lookup a type but any arbitrary term, hence the name
  let str = lookup_typ (cur_env ()) (cur_module () @ [ src ]) in
  let str = match str with Some str -> str | _ -> admit () in
  let def = match inspect_sigelt str with Sg_Let _ _ _ _ def -> def | _ -> admit () in
  let _, ses, def = lowstarize_expr (dst, 0) def in
  let fv: fv = pack_fv (cur_module () @ [ dst ]) in
  let t: term = pack Tv_Unknown in
  let se: sigelt = pack_sigelt (Sg_Let false fv [] t def) in
  exact (quote (normalize_term (ses @ [ se ])))

(* Tests *)
(*
// Some notes: empty lists are not allowed because they give inference errors!
noextract
let test_vectors = [
  h"000102030405060708", [ h"ff" ], "hello test string";
  h"090a0b0c0d0e0f10", [ h"fe" ], "another test string";
]

noextract
let test_vectors' = List.Tot.map (fun x -> x) test_vectors

#set-options "--lax"
%splice[] (fun () -> lowstarize_toplevel "test_vectors'" "low_test_vectors")
*)
