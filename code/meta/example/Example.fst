module Example

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST
open LowStar.BufferOps

#set-options "--z3rlimit 25 --fuel 0 --ifuel 1"

/// Meta parameters for the map
noeq type meta = {
  k : Type0; (* The type of the key *)
  eq : k -> k -> bool; (* Equality test for the key *)
  t : Type0; (* The type of values *)
}

/// Associative list
type al (m : meta) : Type0 = list (m.k & m.t)

/// Lookup
let rec lookup (m : meta) (k : m.k) (ls : al m) : option m.t =
  match ls with
  | [] -> None
  | (k', x) :: ls' ->
    if m.eq k k' then Some x else lookup m k ls'

type name = string
assume type sym_key
assume type bytes
assume val encrypt (k : sym_key) (plain : bytes) : bytes
assume val decrypt (k : sym_key) (cipher : bytes) : option bytes

noeq type keypair = {
  enc_key : sym_key;
  dec_key : sym_key;
}

let dv_meta : meta = {
  k = name;
  eq = (fun x y -> x = y);
  t = keypair;
}

/// Peer library
noeq type device = {
  peers : al dv_meta;
  // Other fields...
}

let lookup_peer_keys (peer_name : name) (dv : device) : option keypair =
  lookup dv_meta peer_name dv.peers

let send_message_to_peer (peer_name : name) (dv : device) (plain : bytes) : option bytes =
  match lookup_peer_keys peer_name dv with
  | None -> None
  | Some kp -> Some (encrypt kp.enc_key plain)

let send_message_from_peer (peer_name : name) (dv : device) (cipher : bytes) : option bytes =
  match lookup_peer_keys peer_name dv with
  | None -> None
  | Some kp -> decrypt kp.dec_key cipher

/// Non-recursive version of lookup, but with intermediate let-bindings for test_pre, etc.
let lookup_loop (m : meta) (k : m.k) (ls : al m) :
  Stack (option m.t)
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
  =  
  push_frame ();
  let ptr = B.alloca ls 1ul in
  let test_pre = fun h0 -> B.live h0 ptr in
  let test_post = fun b h1 -> B.live h1 ptr /\ b = Cons? (B.get h1 ptr 0) in
  let test () : Stack bool (requires test_pre) (ensures (fun h0 b h1 -> test_post b h1)) =
    Cons? (!* ptr)
  in
  let body () : Stack unit
    (requires (fun h0 -> test_post true h0))
    (ensures (fun h0 _ h1 -> test_pre h1)) =
    let tl = Cons?.tl (!* ptr) in
    B.upd ptr 0ul tl
  in
  C.Loops.while #test_pre #test_post test body;
  let x =
    match !* ptr with
    | [] -> None
    | hd :: _ -> Some hd
  in
  pop_frame ();
  x

/// Auxiliary definitions
inline_for_extraction
let ref #a (init : a) :
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

inline_for_extraction
let while #test_pre #test_post = C.Loops.while #test_pre #test_post

inline_for_extraction noextract
let fst (x, _) = x

inline_for_extraction noextract
let snd (_, y) = y

// Our index captures all the possible choices of specialization. Here, our code
// may be specialized for any choice of key and value types...
inline_for_extraction noeq
type index_t = {
  key: eqtype;
  value: Type0
}

// (some derived types from the index)
inline_for_extraction
let assoc_list_t (i: index_t) = list (i.key & i.value)
inline_for_extraction
let key_eq_t (i: index_t) = i.key -> i.key -> bool

// ... as long as the user can, later, provide an equality function. Two options
// here: either we put this in an fsti, and have an implementation underneath
// that guarantees that the type is inhabited (hard to explain). Or we just say
// that it's ok to have assume val, if we made a mistake, then no one will be
// able to call lookup_loop1.

[@Meta.Attribute.specialize]
assume val key_eq: (#i: index_t) -> key_eq_t i

/// No intermediate let-bindings
[@Meta.Attribute.specialize]
let lookup_loop1 #i (k: i.key) (ls: assoc_list_t i):
  Stack (option i.value)
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
  =  
  push_frame ();
  let b = ref true in
  let lsp = ref ls in
  let test_pre = fun h0 -> B.live h0 b /\ B.live h0 lsp in
  let test_post = fun bv h1 -> B.live h1 b /\ B.live h1 lsp /\ bv = B.get h1 b 0 in
  while
    ((fun () -> !* b)
      <: unit -> Stack bool (requires test_pre) (ensures (fun h0 bv h1 -> test_post bv h1)))
    ((fun () ->
      let ls = !* lsp in
      match ls with
      | [] -> upd b false
      | (k', _) :: tl ->
        if key_eq k k' then upd b false
        else upd lsp tl)
      <: unit -> Stack unit
        (requires (fun h0 -> test_post true h0))
        (ensures (fun h0 _ h1 -> test_pre h1)));
  let ls = !* lsp in
  pop_frame ();
  match ls with
  | [] -> None
  | (_, x) :: _ -> Some x

%splice [ example_lookup_loop1_higher ] (Meta.Interface.specialize (`index_t) [
  `lookup_loop1
])

inline_for_extraction
let concrete_index: index_t = { key = int; value = string }
let concrete_key_eq: key_eq_t concrete_index = (=)
let concrete_lookup_loop1 = example_lookup_loop1_higher #concrete_index True concrete_key_eq
