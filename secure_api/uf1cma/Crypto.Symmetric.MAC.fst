(*--build-config
options: --__temp_no_proj Crypto.Symmetric.MAC --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 0 --z3rlimit 20 --use_hints --include ../../code/bignum --include ../../code/experimental/aesgcm --include ../../code/lib/kremlin --include ../../code/poly1305 --include ../../code/salsa-family --include ../../secure_api/aead --include ../../secure_api/prf --include ../vale --include ../uf1cma --include ../utils --include ../../specs --include ../../../kremlin/kremlib --include ../../../FStar/ulib/hyperstack
--*)
(**
  This module multiplexes between different real implementations of polynomial
  MACs. It is oblivious to the static vs one-time allocation of the r part of
  the key (the point where the polynomial is evaluated).

  It has functions to allocate keys and compute MACs incrementally on
  stack-based accumulators (start; update; finish), as a refinement of
  their ghost polynomial specification.
*)
module Crypto.Symmetric.MAC

open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag
open FStar.Buffer // no need?

module GS = Spec.GF128
module GF = Crypto.Symmetric.GF128

//17-02-11 now switched from 32-bit to 64-bit; can we keep both?

//17-02-11 Please at least document such notations! Besides Spec.Poly1305 is also used below.
module PS_ = Hacl.Spec.Poly1305_64
module PS = Hacl.Spe.Poly1305_64
module PL = Hacl.Impl.Poly1305_64

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type id = id * UInt128.t //NS: why not this definition : i:id & iv (alg i)
inline_for_extraction let alg ((i,_):id) : macAlg =
 macAlg_of_id i

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

type text = Seq.seq (lbytes 16) // Used to be seq elem, then seq (lbytes 16)

val text_to_PS_text: t:text -> Tot (t':PS_.text{
  Seq.length t == Seq.length t' /\
  (forall (i:nat).{:pattern Seq.index t' i}
    i < Seq.length t ==> Seq.index t i == Seq.index t' i)})
  (decreases (Seq.length t))
let rec text_to_PS_text t =
  if Seq.length t = 0 then Seq.createEmpty
  else
    Seq.cons (Seq.head t) (text_to_PS_text (Seq.tail t))

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

(** Field element *)
let elem i = (* dependent; used only ideally *)
  match alg i with
  | POLY1305 -> Spec.Poly1305.elem
  | GHASH    -> GS.elem

private
let zero i : elem i =
  match alg i with
  | POLY1305 -> Spec.Poly1305.zero
  | GHASH    -> GS.zero

(** Private representation of a field element as a buffer *)

(* 16-10-26 for the time being, we avoid value-dependent types (after
   erasure and flag inlining) for Kremlin. We may later compile those
   to untagged unions. We also use a top-level refinement, so that
   case analysis applies without pattern matching.

   See 35380a8a for an older, more type-dependent version *)

unfold inline_for_extraction
let limb = function
  | POLY1305 -> UInt64.t
  | GHASH    -> UInt128.t

private unfold inline_for_extraction
let limb_length = function
  | POLY1305 ->  3
  | GHASH    -> 1

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0"

inline_for_extraction unfold
type buffer_of a = b:Buffer.buffer (limb a){Buffer.length b == limb_length a}

#reset-options "--z3rlimit 100 --initial_ifuel 1 --max_ifuel 1"
inline_for_extraction type pub_elemB (i:id) =
  buffer_of (alg i)

//  (match alg i with
//  | POLY1305 -> buffer_of POLY1305
//  | GHASH -> buffer_of GHASH)

//b:_buffer{
//    POLY1305? (alg i) <==> B_POLY1305? b /\
//    GHASH? (alg i) <==> B_GHASH? b
//  }
//  { (match alg i with
//  | POLY1305 -> B_POLY1305? b
//  | GHASH    -> B_GHASH? b) }

abstract type elemB (i:id) = pub_elemB i

noextract val reveal_elemB : #i:id -> elemB i -> GTot (pub_elemB i)
let reveal_elemB #i e = e

#reset-options "--z3rlimit 100 --initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
val as_buffer: #i:id -> elemB i -> GTot (buffer_of (alg i))
let as_buffer #i e =
  reveal_elemB e

val live: mem -> #i:id -> elemB i -> Type0
let live h #i b = Buffer.live h (as_buffer b)

//17-02-11 should red_45 and red_44 really be part of the poly1305 API??
//17-02-11 what's the purpose of norm vs norm_r?

val norm: mem -> #i:id -> b:elemB i -> Type0
let norm h #i b =
  match alg i with
  | POLY1305 -> Buffer.live h b /\ Hacl.Spec.Bignum.AddAndMultiply.red_45 (as_seq h b)
    //Crypto.Symmetric.Poly1305.Bigint.norm h b // implies live
  | GHASH -> Buffer.live h b

val norm_r: mem -> #i:id -> b:elemB i -> Type0
let norm_r h #i b =
  let b = reveal_elemB b in
  match alg i with
  | POLY1305 -> Buffer.live h b /\ Hacl.Spec.Bignum.AddAndMultiply.red_44 (as_seq h b)
    //Crypto.Symmetric.Poly1305.Bigint.norm h b // implies live
  | GHASH -> Buffer.live h b

(** message words (not necessarily a full word. *)
let wlen = 16ul

type word = b:Seq.seq u8{Seq.length b <= UInt32.v wlen}

type word_16 = lbytes (UInt32.v wlen)

(** Mutable representation of (partial) words as buffers *)
type wordB = b:Buffer.buffer u8{Buffer.length b <= UInt32.v wlen}

type wordB_16 = lbuffer (UInt32.v wlen)

noextract val sel_word: h:mem -> b:wordB{Buffer.live h b} -> GTot word
let sel_word h b = Buffer.as_seq h b

noextract val sel_elem: h:mem -> #i:id -> b:elemB i{live h b} -> GTot (elem i)
let sel_elem h #i b =
  let b = reveal_elemB b in
  match alg i with
  | POLY1305 -> PS_.selem (as_seq h b)
  | GHASH -> GF.sel_elem h b

#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val frame_norm: h0:mem -> h1:mem -> #i:id -> b:elemB i{live h1 b} -> Lemma
  (requires (norm h0 b /\
    Buffer.as_seq h0 (as_buffer b) == Buffer.as_seq h1 (as_buffer b)))
  (ensures  (norm h1 b))
let frame_norm h0 h1 #i b =
  match alg i with
  | POLY1305 -> ()
    (* Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 (as_buffer b) (as_buffer b) *)
  | _ -> ()

val eq_sel_elem: h:mem -> #i:id -> b1:elemB i{live h b1} -> b2:elemB i{live h b2} -> Lemma
 (requires (Buffer.as_seq h (as_buffer b1) == Buffer.as_seq h (as_buffer b2)))
 (ensures  (sel_elem h b1 == sel_elem h b2))
let eq_sel_elem h #i b1 b2 =
  match alg i with
  | POLY1305 -> ()
    (* Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h h *)
    (*   (as_buffer b1) (as_buffer b2) (limb_length POLY1305) *)
  | _ -> ()

val frame_sel_elem: h1:mem -> h2:mem -> #i:id -> b:elemB i{live h1 b /\ live h2 b} -> Lemma
 (requires (Buffer.as_seq h1 (as_buffer b) == Buffer.as_seq h2 (as_buffer b)))
 (ensures  (sel_elem h1 b == sel_elem h2 b))
let frame_sel_elem h1 h2 #i b =
  match alg i with
  | POLY1305 -> ()
    (* Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h1 h2 *)
    (*   (as_buffer b) (as_buffer b) (limb_length POLY1305) *)
  | _ -> ()

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --max_ifuel 1 --initial_ifuel 1"
(** Create and initialize an element (used for r) *)
val rcreate: rgn:HH.rid{HS.is_eternal_region rgn} -> i:id -> ST (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 ->
    HS.modifies (Set.singleton rgn) h0 h1 /\
    HS.modifies_ref rgn TSet.empty h0 h1 /\
    ~(HS.((Buffer.content (as_buffer r)).mm)) /\
    Buffer.frameOf (as_buffer r) == rgn /\
    ~(live h0 r) /\ live h1 r))
let rcreate rgn i =
  match alg i with
  | POLY1305 ->
    let b : Buffer.buffer UInt64.t = FStar.Buffer.rcreate rgn 0UL 3ul in b
  | GHASH ->
    let b : Buffer.buffer UInt128.t = FStar.Buffer.rcreate rgn (FStar.Int.Cast.uint64_to_uint128 0UL) 1ul in b

val create: i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 ->
     let b = as_buffer r in
     ~(Buffer.contains h0 b) /\
     norm h1 r /\
     sel_elem h1 r = zero i /\
     Buffer.frameOf b = HS.(h0.tip) /\ // /\ Map.domain h1.h == Map.domain h0.h
     Buffer.modifies_0 h0 h1 ))

let create i =
  match alg i with
  | POLY1305 ->
      let b : Buffer.buffer UInt64.t = FStar.Buffer.create 0uL 3ul in
      PL.poly1305_start b;
      b
      (* hide in Poly1305.fst? *)
      (* let b = FStar.Buffer.create 0uL 5ul in *)
      (* let h1 = ST.get() in  *)
      (* Crypto.Symmetric.Poly1305.Bigint.eval_null h1 b 5; *)
      (* assert(Crypto.Symmetric.Poly1305.Bigint.norm h1 b); *)
      (* B_POLY1305 b *)
  | GHASH ->
      let b : Buffer.buffer UInt128.t =
        FStar.Buffer.create (FStar.Int.Cast.uint64_to_uint128 0UL) 1ul in
      let h1 = ST.get() in
      GF.fzero_lemma (Seq.index (as_seq h1 b) 0);
      b

// TODO: generalize length, add functional spec
(** Encode raw bytes of static key as a field element *)
val encode_r: #i:id -> b:elemB i -> raw:lbuffer 16{Buffer.disjoint (as_buffer b) raw} -> Stack unit
  (requires (fun h -> live h b /\ Buffer.live h raw))
  (ensures  (fun h0 _ h1 ->
    norm_r h1 b /\
    Buffer.live h1 raw /\
    Buffer.modifies_1 (as_buffer b) h0 h1))
let encode_r #i b raw =
  match alg i with
  | POLY1305 -> PL.poly1305_encode_r b raw
      (* PL.clamp raw;  *)
      (* PL.toField b raw *)
  | GHASH ->
      //let h0 = ST.get () in
      //assert (Buffer.modifies_1 raw h0 h0); // Necessary for triggering right lemmas
      let i = GF.load128_be raw in
      let b' : Buffer.buffer UInt128.t = b in
      b'.(0ul) <- i

// TODO: generalize to word
(** Encode a word of a message as a field element *)
val encode: i:id -> w:word_16 -> GTot (elem i)
let encode i w =
  match alg i with
  | POLY1305 -> Spec.Poly1305.encode w
  | GHASH    -> GS.encode w

(* (\** Encode a word of a message as a field element in a buffer *\) *)
(* private val encodeB: i:id -> w:wordB_16 -> StackInline (elemB i) *)
(*   (requires (fun h -> Buffer.live h w)) *)
(*   (ensures  (fun h0 b h1 -> Buffer.live h1 w /\ live h1 b /\ norm h1 b *)
(*     /\ Buffer.modifies_0 h0 h1 *)
(*     /\ ~(Buffer.contains h0 (as_buffer b)) *)
(*     /\ sel_elem h1 b == encode i (sel_word h1 w))) *)
(* let encodeB i w = *)
(*   match alg i with  *)
(*   | POLY1305 -> *)
(*       let b = Buffer.create 0UL 5ul in *)
(*       PL.toField_plus_2_128 b w; *)
(*       B_POLY1305 b *)
(*   | GHASH -> *)
(*       let buf = Buffer.create 0uy 16ul in *)
(*       let h0 = ST.get () in *)
(*       Buffer.blit w 0ul buf 0ul 16ul; *)
(*       let h1 = ST.get () in *)
(*       Seq.lemma_eq_intro (sel_word h0 w) (Seq.slice (Buffer.as_seq h0 w) 0 16); *)
(*       Seq.lemma_eq_intro (Buffer.as_seq h1 b) (Seq.slice (Buffer.as_seq h1 b) 0 16); *)
(*       let v = GF.load128_be w in *)
(*       let b = Buffer.create v 1ul in *)
(*       B_GHASH b *)

(** Polynomial evaluation *)
noextract val poly: #i:id -> cs:text -> r:elem i -> Tot (elem i)
let poly #i cs r =
  match alg i with
  | POLY1305 -> Spec.Poly1305.poly (text_to_PS_text cs) r
  | GHASH    -> GS.poly (text_to_PS_text cs) r


(** Create and initialize the accumulator *)
val start: #i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 ->
     let b = as_buffer r in
       ~(Buffer.contains h0 b)
     /\ norm h1 r
     /\ sel_elem h1 r = zero i
     /\ Buffer.frameOf b = HS.(h0.tip) // /\ Map.domain h1.h == Map.domain h0.h
     /\ Buffer.modifies_0 h0 h1 ))
//16-11-27 factor out this kind of post?

let start #i = create i

noextract val field_add: #i:id -> elem i -> elem i -> Tot (elem i)
let field_add #i a b =
  match alg i with
  | POLY1305 -> Spec.Poly1305.fadd a b
  | GHASH    -> GS.op_Plus_At a b

noextract val field_mul: #i:id -> elem i -> elem i -> Tot (elem i)
let field_mul #i a b =
  match alg i with
  | POLY1305 -> Spec.Poly1305.fmul a b
  | GHASH    -> GS.op_Star_At a b

noextract let op_Plus_At #i e1 e2 = field_add #i e1 e2
noextract let op_Star_At #i e1 e2 = field_mul #i e1 e2

#reset-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

val poly_empty: #i:id -> t:text{Seq.length t == 0} -> r:elem i ->
  Lemma (poly #i t r == zero i)
let poly_empty #i t r =
  match alg i with
  | POLY1305 -> ()
    (* PL.poly_empty (text_to_PS_text t) r *)
  | GHASH    -> ()
    (* GS.poly_empty t r *)

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

//17-02-11 rename? relocate?
private val poly_cons_: x:word -> xs:PS_.text -> r:PS_.elem ->
  Lemma Spec.Poly1305.(poly (Seq.cons x xs) r == (encode x +@ poly xs r) *@ r)

let poly_cons_ x xs r =
  let xxs = Seq.cons x xs in
  Seq.lemma_len_append (Seq.create 1 x) xs;
  Seq.lemma_eq_intro (Seq.tail xxs) xs;
  PS.poly_def_1 xxs r

#reset-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

val poly_cons: #i:id -> x:word_16 -> xs:text -> r:elem i ->
  Lemma (poly #i (Seq.cons x xs) r == (poly #i xs r +@ encode i x) *@ r)
let poly_cons #i x xs r =
        assert (Seq.equal (text_to_PS_text (Seq.cons x xs))
                          (Seq.cons x (text_to_PS_text xs)));
  match alg i with
  | POLY1305 -> 
	poly_cons_ x (text_to_PS_text xs) r
  | GHASH    -> 
        GS.poly_cons x (text_to_PS_text xs) r;
        GS.add_comm (GS.poly (text_to_PS_text xs) r) (GS.encode x)

#reset-options "--z3rlimit 50 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

(** Process one message block and update the accumulator *)
val update: #i:id -> r:elemB i -> a:elemB i -> w:wordB_16 -> Stack unit
  (requires (fun h -> live h r /\ live h a /\ Buffer.live h w
    /\ norm_r h r /\ norm h a
    /\ Buffer.disjoint_2 (as_buffer r) (as_buffer a) w
    /\ Buffer.disjoint (as_buffer a) w))
  (ensures  (fun h0 _ h1 ->
    live h0 a /\ live h0 r /\ Buffer.live h0 w /\ live h1 a ///\ live h1 r
    /\ norm h1 a
    /\ Buffer.modifies_1 (as_buffer a) h0 h1
    /\ sel_elem h1 a == (sel_elem h0 a +@ encode i (sel_word h0 w)) *@ sel_elem h0 r))

#reset-options "--z3rlimit 300 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let update #i r a w =
  push_frame();
  let h0 = ST.get () in
  (match alg i with
  | POLY1305 ->
    let a' : Buffer.buffer UInt64.t = a in
    let r' : Buffer.buffer UInt64.t = r in
    let _ = PL.poly1305_update (Ghost.hide Seq.createEmpty) (PL.mk_state r' a') w in
    ()
    (* begin *)
    (*   push_frame(); *)
    (*   let e = Buffer.create 0UL 5ul in *)
    (*   PL.toField_plus_2_128 e w; *)
    (*   let h1 = ST.get () in *)
    (*   Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 a a; *)
    (*   Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 r r; *)
    (*   (\* assert (PL.sel_elem h1 e == encode i (sel_word h0 w)); *\) *)
    (*   PL.add_and_multiply a e r; *)
    (*   let h2 = ST.get () in *)
    (*   assert (PL.sel_elem h2 a == (PL.sel_elem h1 a +@ PL.sel_elem h1 e) *@ PL.sel_elem h1 r); *)
    (*   Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h0 h1 r r 5; *)
    (*   Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h0 h1 a a 5; *)
    (*   pop_frame(); *)
    (*   let h3 = ST.get () in *)
    (*   Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h2 h3 a a 5 *)
    (* end *)
  | GHASH ->
    let a' : Buffer.buffer UInt128.t = a in
    let r' : Buffer.buffer UInt128.t = r in
    let e = Buffer.create GF.zero_128 1ul in
    e.(0ul) <- GF.load128_be w;
    GF.add_and_multiply a' e r'
  ); pop_frame()

let taglen = 16ul
type tag = lbytes (UInt32.v taglen)
type tagB = lbuffer (UInt32.v taglen)

(** Complete MAC-computation specifications *)
noextract val mac: #i:id -> cs:text -> r:elem i -> s:tag -> GTot tag
let mac #i cs r s =
  match alg i with
  | POLY1305 -> Spec.Poly1305.finish (Spec.Poly1305.poly (text_to_PS_text cs) r) s
  | GHASH    -> GS.mac (text_to_PS_text cs) r s

val finish: #i:id -> s:tagB -> a:elemB i -> t:tagB -> Stack unit
  (requires (fun h ->
    Buffer.live h s /\
    norm h a /\
    Buffer.live h t /\
    Buffer.disjoint_2 (as_buffer a) s t /\ Buffer.disjoint s t))
  (ensures  (fun h0 _ h1 -> live h0 a /\ Buffer.live h0 s
    /\ live h1 a
    /\ Buffer.live h1 s
    /\ Buffer.live h1 t
    /\ Buffer.modifies_2 (as_buffer a) t h0 h1
    /\ (
    let tv = Buffer.as_seq h1 t in
    let sv = Buffer.as_seq h0 s in
    let av = sel_elem h0 a in
    match alg i with
    | POLY1305 -> Seq.equal tv (Spec.Poly1305.finish av sv)
    | GHASH    -> Seq.equal tv (GS.finish av sv) )))

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
private val lemma_modifies_3_2_finish: #a:Type -> #a':Type -> h:mem -> h':mem -> h'':mem -> b:buffer a -> b':buffer a' -> Lemma
  (requires (Buffer.live h b /\ Buffer.live h b' /\ Buffer.modifies_0 h h' /\ Buffer.modifies_2 b b' h' h''))
  (ensures (Buffer.modifies_3_2 b b' h h''))
let lemma_modifies_3_2_finish #a #a' h h' h'' b b' =
  lemma_reveal_modifies_0 h h';
  lemma_reveal_modifies_2 b b' h' h'';
  lemma_intro_modifies_3_2 b b' h h''

let finish #i s a t =
  let h0 = ST.get() in
  match alg i with
  | POLY1305 ->
    push_frame();
    let a' : Buffer.buffer UInt64.t = a in
    let h = ST.get() in
    Math.Lemmas.lemma_mod_plus_distr_l (PS_.selem (as_seq h a)) (little_endian (as_seq h t)) (pow2 128);
    let dummy_r = Buffer.create 0uL 3ul in
    let dummy_m = Buffer.create 42uy 0ul in
    let h' = ST.get() in
    PL.poly1305_finish_ (Ghost.hide Seq.createEmpty) (PL.mk_state dummy_r a') t dummy_m 0uL s;
    let h'' = ST.get() in
    lemma_modifies_3_2_finish h h' h'' a t;
    pop_frame();
    let h1 = ST.get() in
    Buffer.modifies_popped_3_2 a t h0 h h'' h1;
    cut (FStar.Endianness.little_endian (as_seq h1 t) = ((PS_.selem (as_seq h0 a)) + FStar.Endianness.little_endian (as_seq h0 s)) % pow2 128);
    cut (FStar.Endianness.little_endian (as_seq h1 t) = ((PS_.selem (as_seq h0 a)) + FStar.Endianness.little_endian (as_seq h0 s)) % pow2 128);
    FStar.Endianness.lemma_little_endian_inj (Buffer.as_seq h1 t) (Spec.Poly1305.finish (PS_.selem (as_seq h0 a)) (as_seq h0 s))
  | GHASH ->
    let a' : Buffer.buffer UInt128.t = a in
    GF.finish a' s;
    GF.store128_be t a'.(0ul)

//17-02-11 new lemma
val lemma_poly_finish_to_mac:
  i:id -> ht:mem -> t:tagB -> a:elem i -> hs:mem -> s:tagB -> log:text -> r:elem i ->
  Lemma (requires (Buffer.live ht t /\ Buffer.live hs s
    /\ a == MAC.poly log r
    /\ (match alg i with
    | POLY1305 -> Seq.equal (Buffer.as_seq ht t) (Spec.Poly1305.finish a (Buffer.as_seq hs s))
    | GHASH    -> Seq.equal (Buffer.as_seq ht t) (GS.finish a (Buffer.as_seq hs s) ))
    ))
       (ensures (Buffer.live ht t /\ Buffer.live hs s
         /\ Buffer.as_seq ht t == MAC.mac log r (Buffer.as_seq hs s)))
let lemma_poly_finish_to_mac i ht t a hs s log r = ()
