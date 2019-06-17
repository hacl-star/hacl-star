module Vale.Transformers.LiveAnalysis

open Vale.X64.Bytes_Code_s
open Vale.X64.Instruction_s
open Vale.X64.Instructions_s
open Vale.X64.Machine_Semantics_s
open Vale.X64.Machine_s
open Vale.X64.Print_s

open Vale.Transformers.PossiblyMonad
open Vale.Transformers.Locations
open Vale.Transformers.BoundedInstructionEffects

module L = FStar.List.Tot

(* TODO: Is there a built-in for this? *)
irreducible
let rec locations_difference (a b:locations) : (res:locations{
    forall x. {:pattern (L.mem x res)}
      (L.mem x res) = ((L.mem x a) && (not (L.mem x b)))
  }) =
  match a with
  | [] -> []
  | x :: xs ->
    if L.mem x b then (
      locations_difference xs b
    ) else (
      x :: locations_difference xs b
    )

(* TODO: Is there a built-in for this? *)
irreducible
let rec locations_union (a b:locations) : (res:locations{
    forall x. {:pattern (L.mem x res)}
      (L.mem x res) = (L.mem x a || L.mem x b)
  }) =
  match a with
  | [] -> (
      match b with
      | [] -> []
      | y :: ys ->
        if L.mem y ys then (
          locations_union [] ys
        ) else (
          y :: locations_union [] ys
        )
    )
  | x :: xs ->
    if L.mem x b then (
      locations_union xs b
    ) else (
      x :: locations_union xs b
    )

unfold let (+++) = locations_union
unfold let (---) = locations_difference

let live_of_ins (i:ins) (post:locations) : locations =
  let r, w = rw_set_of_ins i in
  (post --- w) +++ r

let live_of_ocmp (o:ocmp) (post:locations) : locations =
  post +++ locations_of_ocmp o

let rec live_of_code (c:code) (post:locations) : locations =
  match c with
  | Ins i -> live_of_ins i post
  | Block l -> live_of_codes l post
  | IfElse c t f ->
    live_of_ocmp c
      (live_of_code t post +++
       live_of_code f post)
  | While c b ->
    post +++
    live_of_ocmp c
      (live_of_code b post)

and live_of_codes (c:codes) (post:locations) : locations =
  match c with
  | [] -> post
  | x :: xs ->
    live_of_code x (live_of_codes xs post)
