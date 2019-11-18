module Vale.Lib.Meta
open FStar.Mul

let generic_injective_proof #a #b f g l =
  let helper (x x':a) : Lemma (f x == f x' ==> x == x') =
    if f x = f x' then
      if not (x = x') then (
        let y = f x in
        let y' = f x' in
        assert (y == y');
        let z = g y in
        let z' = g y' in
        assert (z == z');
        l x;
        assert (z == x);
        l x';
        assert (z' == x');
        ()
      ) else ()
    else
      ()
    in
  FStar.Classical.forall_intro_2 helper;
  ()


let exists_elim2 goal #a #b #p _ f =
  let open FStar.Classical in
  exists_elim goal () (fun (x:a{exists (y:b x). p x y}) ->
    exists_elim goal () (fun (y:b x{p x y}) ->
      f x y))

