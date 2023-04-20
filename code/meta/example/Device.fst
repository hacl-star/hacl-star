module Device

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open LowStar.BufferOps

#set-options "--z3rlimit 100 --fuel 1 --ifuel 1 --__no_positivity --record_options --split_queries always"

(*** Linked lists *)
noeq
type ll_ (a: Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: ll_ a;
  data: a;
}

noeq
type ll (a: Type0) = {
  l: ll_ a;
  elems: Ghost.erased (list a); // Ghost representation of the list
  r : HS.rid; (* For footprint reasoning *)
}

/// Well-formedness
///
/// Pointers are live and [l] can be represented by [elems].
let rec ll_wf (#a : Type0) (h : HS.mem) (l : ll_ a) (elems : list a) :
  GTot Type (decreases elems) =
  B.live h l /\ (
  match Ghost.reveal elems with
  | [] ->
    B.g_is_null l
  | x :: elems' ->
    B.length l == 1 /\ (
    let { data=data; next=next } = B.get h l 0 in
    x == data /\
    ll_wf h next (G.hide elems')
  ))

let ll_inv (#a : Type0) (h: HS.mem) (l : ll a) : GTot Type =
  ll_wf h l.l l.elems

val footprint_: (#a: Type0) -> (h: HS.mem) -> (l: ll_ a) -> (n: list a) -> Ghost B.loc
  (requires (ll_wf h l n))
  (ensures (fun refs -> True))
  (decreases n)

let rec footprint_ #a h l n =
  if B.g_is_null l
  then B.loc_none
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint_ h next (G.hide (L.tl n)) in
    B.loc_union (B.loc_addr_of_buffer l) refs

val footprint : (#a: Type0) -> (h: HS.mem) -> (l: ll a) -> Ghost B.loc
  (requires (ll_inv h l))
  (ensures (fun refs -> True))

let footprint #a h l = footprint_ h l.l l.elems

/// Framing lemmas
let rec frame_ (#a: Type0) (l: ll_ a) (n: list a) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    ll_wf h0 l n /\
    B.loc_disjoint r (footprint_ h0 l n) /\
    B.modifies r h0 h1
  ))
  (ensures (
    ll_wf h1 l n /\
    footprint_ h1 l n == footprint_ h0 l n /\
    ll_wf h1 l n
  ))
  (decreases n)
  [ SMTPat (ll_wf h1 l n); SMTPat (B.modifies r h0 h1) ]
=
  if B.g_is_null l then
    ()
  else
    frame_ (B.deref h0 l).next (L.tl n) r h0 h1

let frame (#a: Type0) (l: ll a) (r: B.loc) (h0 h1: HS.mem): Lemma
  (requires (
    ll_inv h0 l /\
    B.loc_disjoint r (footprint h0 l) /\
    B.modifies r h0 h1
  ))
  (ensures (
    ll_inv h1 l /\
    footprint h1 l == footprint h0 l /\
    ll_inv h1 l
  ))
  [ SMTPat (ll_inv h1 l); SMTPat (B.modifies r h0 h1) ]
=
  frame_ l.l l.elems r h0 h1

let rec inv_loc_in_footprint_ (#a: Type0) (h:HS.mem) (l: ll_ a) (n: list a) :
  Lemma
    (requires (ll_wf h l n))
    (ensures (B.loc_in (footprint_ h l n) h))
    (decreases n) 
    [ SMTPat (ll_wf h l n) ] =
  if B.g_is_null l then
    ()
  else
    inv_loc_in_footprint_ h (B.deref h l).next (L.tl n)

let inv_loc_in_footprint (#a: Type0) (h:HS.mem) (l: ll a) :
  Lemma
    (requires (ll_inv h l))
    (ensures (B.loc_in (footprint h l) h))
    [ SMTPat (ll_inv h l) ] =
  inv_loc_in_footprint_ h l.l l.elems

(*** Map *)

inline_for_extraction noextract
let find_t (k a : Type) : Type =
  k ->
  l:ll (k * a) ->
  Stack (option a)
    (requires (fun h0 -> ll_inv h0 l))
    (ensures (fun h0 _ h1 -> True))

inline_for_extraction noextract
noeq type map (a : Type) = {
  k : Type;
  find : find_t k a;
}

inline_for_extraction noextract
noeq type eq_index = {
  k: Type0;
  t: Type0
} 

/// Auxiliary definitions
inline_for_extraction
let alloc #a (init : a) :
  ST.StackInline (B.buffer a)
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    B.live h1 b /\
    B.alloc_post_mem_common b h0 h1 (Seq.create 1 init) /\
    B.length b = 1 /\
    B.frameOf b = HS.get_tip h0 /\
    B.frameOf b <> HyperStack.root    
  )) =
  B.alloca init 1ul

inline_for_extraction
let upd
  (#a:Type0) (#rrel #rel:B.srel a)
  (b:B.mbuffer a rrel rel)
  (v:a) :
  Stack unit
    (requires (fun h -> B.live h b /\ 0 < B.length b /\
                      rel (B.as_seq h b) (Seq.upd (B.as_seq h b) 0 v)))
    (ensures (fun h _ h' -> (not (B.g_is_null b)) /\
                          B.modifies (B.loc_buffer b) h h' /\
                          B.live h' b /\
                          B.as_seq h' b == Seq.upd (B.as_seq h b) 0 v))
  = B.upd b 0ul v

[@Meta.Attribute.specialize]
assume val eq: #i:eq_index -> i.k -> i.k -> bool

(** Auxiliary definition for [find] *)
inline_for_extraction noextract
[@Meta.Attribute.specialize]
let find (#i : eq_index) (x : i.k) (ls : ll (i.k * i.t)) :
  Stack (option i.t)
  (requires (fun h0 -> ll_inv h0 ls))
  (ensures (fun h0 _ h1 -> True))
  =
  (**) let h00 = ST.get () in
  (**) assert (B.loc_in (footprint h00 ls) h00);
  (* Push a new frame for stack allocation *)
  push_frame ();
  (* Stack allocation *)
  let lsp = alloc ls.l in
  (* This pointer is ghost, and will disappear at extraction: we need it
     to track the pure view of the list *)
  let glsp = alloc ls.elems in
  let b = alloc true in
  let inv h =
    let l = B.deref h lsp in
    let elems = G.reveal (B.deref h glsp) in
    ll_wf h l elems /\
    B.live h lsp /\
    B.live h glsp /\
    B.live h b /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer lsp) /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer glsp) /\
    B.loc_disjoint (footprint_ h l elems) (B.loc_buffer b) /\
    True
  in
  let test_pre h0 =
    inv h0
  in
  let test_post x h1 =
    inv h1 /\
    x = B.deref h1 b
  in
  [@inline_let]
  let test () : Stack bool (requires test_pre) (ensures (fun h0 b h1 -> test_post b h1)) =
    !* b
  in
  [@inline_let]
  let body () : Stack unit
    (requires (fun h0 -> test_post true h0))
    (ensures (fun h0 _ h1 -> test_pre h1)) =
    (**) let h0 = ST.get () in
    let ls = !* lsp in
    (* Check if we reached the end of the list *)
    if B.is_null ls then
      begin
      (* End of the list: exit *)
      upd b false
      end
    else
      begin
      (* Get the current element and the tail *)
      let { data=data; next=tl } = !* ls in
      let (x', _) = data in
      (* Check the key *)
      if eq x x' then
        (* Found: exit the loop *)
        upd b false
      else
        begin
        (* Not found: update the pointers and continue *)
        let els = !* glsp in
        (**) begin
        (**) let etl = (Cons?.tl els) in
        (**) assert (ll_wf h0 ls els);
        (**) assert (ll_wf h0 tl etl)
        (**) end;
        B.upd lsp 0ul tl;
        (**) let h1 = ST.get () in
        B.upd glsp 0ul (Cons?.tl els); (* This is ghost *)
        (**) let hf = ST.get () in
        (**) begin
        (**) let h = hf in
        (**) let l = B.deref h lsp in
        (**) let elems = G.reveal (B.deref h glsp) in
        (**) assert (B.loc_includes (footprint_ h0 l elems) (footprint_ hf l elems))
        (**) end
        end
      end
  in
  (**) let h01 = ST.get () in
  (**) assert (footprint h01 ls == footprint h00 ls);
  C.Loops.while #test_pre #test_post test body;
  (* Retrieve the found element, if there is *)
  let ls = !* lsp in
  let o: option i.t =
    if B.is_null ls then
      None
    else
      begin
      let { data=data; next=tl } = !* ls in
      let (_, y) = data in
      Some y
      end
  in
  (* Pop the frame (invalidates the stack allocated pointers) *)
  pop_frame ();
  (* Return *)
  o

%splice [ device_find_higher ] (Meta.Interface.specialize (`eq_index) [
  `find
])

(*** Map Instantiation *)
type bytes = Seq.seq FStar.UInt8.t
type ckey = Seq.seq FStar.UInt8.t

let i:eq_index = { k=string; t=ckey}
let ifind = device_find_higher #i True (=)

(*** Device *)

let pid_t = Type0

[@Meta.Attribute.specialize]
assume val find_peer : #pid:pid_t -> k:pid -> dv:ll (pid * ckey) ->
  Stack (option ckey)
    (requires (fun h0 -> ll_inv h0 dv))
    (ensures (fun h0 _ h1 -> True))

[@Meta.Attribute.specialize]
assume val enc : ckey -> bytes -> bytes

[@Meta.Attribute.specialize]
assume val dec : ckey -> bytes -> option bytes

[@Meta.Attribute.specialize]
let send : (#pid : pid_t) ->
  (k:pid) ->
  (dv:ll (pid * ckey)) ->
  (plain:bytes) ->
  Stack (option bytes)
    (requires (fun h0 -> ll_inv h0 dv))
    (ensures (fun _ _ _ -> True))
  = fun #pid k dv plain ->
  match find_peer #pid k dv with
  | None -> None
  | Some sk -> Some (enc sk plain)

[@Meta.Attribute.specialize]
let recv : (#pid : pid_t) ->
  (k:pid) ->
  (dv:ll (pid * ckey)) ->
  (cipher:bytes) ->
  Stack (option bytes)
    (requires (fun h0 -> ll_inv h0 dv))
    (ensures (fun _ _ _ -> True))
  = fun #pid k dv cipher ->
  match find_peer #pid k dv with
  | None -> None
  | Some sk -> dec sk cipher

%splice [ device_send_higher; device_recv_higher ] (Meta.Interface.specialize (`pid_t) [
  `send;
  `recv
])

(*** Device Instantiation *)
(* Using identity for encryption/decryption for presentation purposes.

   In practice, any function from Spec.* in Hacl* would do.
 *)
let id_enc (k : ckey) (plain : bytes) = plain
let id_dec (k : ckey) (cipher : bytes) = Some cipher

let isend = device_send_higher #string True id_enc ifind
let irecv = device_recv_higher #string True id_dec ifind
