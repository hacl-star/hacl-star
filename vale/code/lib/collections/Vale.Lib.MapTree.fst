module Vale.Lib.MapTree
open FStar.Mul

(** Balanced tree implementation *)

type tree (a:eqtype) (b:Type) =
  | Empty : tree a b
  | Node : a -> b -> nat -> tree a b -> tree a b -> tree a b

let height (#a:eqtype) (#b:Type) (t:tree a b) : nat =
  match t with
  | Empty -> 0
  | Node _ _ h _ _ -> h

let mkNode (#a:eqtype) (#b:Type) (key:a) (value:b) (l r:tree a b) : tree a b =
  let hl = height l in
  let hr = height r in
  let h = if hl > hr then hl else hr in
  Node key value (h + 1) l r

let rotate_l (#a:eqtype) (#b:Type) (t:tree a b) : tree a b =
  match t with
  | Node kl vl _ l (Node kr vr _ lr rr) -> mkNode kr vr (mkNode kl vl l lr) rr
  | _ -> t

let rotate_r (#a:eqtype) (#b:Type) (t:tree a b) : tree a b =
  match t with
  | Node kr vr _ (Node kl vl _ ll rl) r -> mkNode kl vl ll (mkNode kr vr rl r)
  | _ -> t

let balance (#a:eqtype) (#b:Type) (t:tree a b) : tree a b =
  match t with
  | Node _ _ _ l r ->
    let hl = height l in
    let hr = height r in
    if hl >= hr + 2 then rotate_r t else
    if hr >= hl + 2 then rotate_l t else
    t
  | _ -> t

let rec get (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (key:a) : option b =
  match t with
  | Empty -> None
  | Node k v h l r ->
    if key = k then Some v
    else if is_le key k then
      get is_le l key
    else
      get is_le r key

let rec put (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (key:a) (value:b) : tree a b =
  match t with
  | Empty -> mkNode key value Empty Empty
  | Node k v _ l r ->
    if key = k then mkNode k value l r
    else if is_le key k then
      balance (mkNode k v (put is_le l key value) r)
    else
      balance (mkNode k v l (put is_le r key value))

(** Invariants and proofs of get-put correctness *)

let is_lt_option (#a:eqtype) (is_le:a -> a -> bool) (x y:option a) : bool =
  match (x, y) with
  | (Some x, Some y) -> is_le x y && x <> y
  | _ -> true

let rec inv (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (lo hi:option a) =
  let (<) x y = is_lt_option is_le x y in
  match t with
  | Empty -> True
  | Node x _ _ l r ->
    let x = Some x in
    lo < x /\ x < hi /\ inv is_le l lo x /\ inv is_le r x hi

#push-options "--max_fuel 2 --max_ifuel 1"
let rec lemma_put_inv (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (key:a) (value:b) (lo hi:option a)
  : Lemma
    (requires
      is_cmp is_le /\
      inv is_le t lo hi /\
      is_lt_option is_le lo (Some key) /\
      is_lt_option is_le (Some key) hi
    )
    (ensures inv is_le (put is_le t key value) lo hi)
  =
  match t with
  | Empty -> ()
  | Node k v _ l r ->
    if key = k then ()
    else if is_le key k then
      lemma_put_inv is_le l key value lo (Some k)
    else
      lemma_put_inv is_le r key value (Some k) hi

let rec lemma_get_put_self (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (key:a) (value:b) (lo hi:option a) : Lemma
  (requires is_cmp is_le /\ inv is_le t lo hi)
  (ensures get is_le (put is_le t key value) key == Some value)
  =
  match t with
  | Empty -> ()
  | Node k v _ l r ->
    if key = k then ()
    else if is_le key k then
      lemma_get_put_self is_le l key value lo (Some k)
    else
      lemma_get_put_self is_le r key value (Some k) hi

let rec lemma_get_put_other (#a:eqtype) (#b:Type) (is_le:a -> a -> bool) (t:tree a b) (key kx:a) (value:b) (lo hi:option a)
  : Lemma
    (requires
      is_cmp is_le /\
      inv is_le t lo hi /\
      is_lt_option is_le lo (Some key) /\
      is_lt_option is_le (Some key) hi /\
      key =!= kx
    )
    (ensures get is_le (put is_le t key value) kx == get is_le t kx)
  =
  lemma_put_inv is_le t key value lo hi;
  match t with
  | Empty -> ()
  | Node k v _ l r ->
    if key = k then ()
    else if is_le key k then
      lemma_get_put_other is_le l key kx value lo (Some k)
    else
      lemma_get_put_other is_le r key kx value (Some k) hi
#pop-options

(** Map interface *)

#push-options "--max_fuel 1 --max_ifuel 2"
noeq
type map' (a:eqtype) b =
  | Map :
    is_le:(a -> a -> bool) ->
    t:tree a b ->
    default_v:b ->
    invs:squash (is_cmp is_le /\ inv is_le t None None) ->
    map' a b
#pop-options

let map = map'

let const a b is_le d =
  Map is_le Empty d ()

let sel #a #b (Map is_le t d _) key =
  match get is_le t key with Some v -> v | None -> d

let upd #a #b (Map is_le t d _) key value =
  let t' = put is_le t key value in
  lemma_put_inv is_le t key value None None;
  Map is_le t' d ()

let lemma_const a b is_le d key =
  ()

let lemma_sel_upd_self #a #b (Map is_le t _ _) key value =
  lemma_get_put_self is_le t key value None None 

let lemma_sel_upd_other #a #b (Map is_le t _ _) key kx value =
  lemma_get_put_other is_le t key kx value None None

