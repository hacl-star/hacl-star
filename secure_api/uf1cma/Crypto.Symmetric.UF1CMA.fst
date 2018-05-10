(**

   This file states our probabilistic security assumption on
   polynomial MACs, and provides an idealized implementation,
   while being abstract on the underlying field.
*)
module Crypto.Symmetric.UF1CMA

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer

(* open Crypto.Symmetric.Poly1305.Spec *)
(* open Crypto.Symmetric.Poly1305 / avoid? *)
(* module PS_ = Hacl.Spec.Poly1305_64 *)
module PS_ = Hacl.Spe.Poly1305_64
module PS = Spec.Poly1305
module PL = Hacl.Impl.Poly1305_64

open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag

module HS = FStar.HyperStack
module MAC = Crypto.Symmetric.MAC


//16-12-19 should go to HyperStack?


// should go elsewhere
let erid = r:rid{is_eternal_region r}

type alg = macAlg

let alg_of_id = macAlg_of_id

(** Length of the single-use part of the key *)
let keylen (i:id) =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | CHACHA20_POLY1305 -> 32ul

(** Length of optional static auth key (when using AES) *)
let skeylen (i:id) =  // can't refine with {skeyed i} here
  match aeadAlg_of_id i with
  | AES_128_GCM       -> 16ul
  | AES_256_GCM       -> 16ul
  | _                 ->  0ul // dummy; never allocated.

(** Does the algorithm use a static key? *)
let skeyed (i:id) =
  match aeadAlg_of_id i with
  | AES_128_GCM       -> true
  | AES_256_GCM       -> true
  | CHACHA20_POLY1305 -> false

type skey (rgn:rid) (i:id) =
  b:lbuffer (UInt32.v (skeylen i)){Buffer.frameOf b == rgn /\ (~ (HS.is_mm (Buffer.content b)))}

//16-10-16 can't make it abstract?
(** Conditionally-allocated abstract key (accessed only in this module) *)
type akey' (rgn:rid) (i:id) =
  | Nothing
  | Just    of skey rgn i
let akey (rgn:rid) (i:id) = a:akey' rgn i{Just? a <==> skeyed i}
// using an option type for KreMLin. Was: if skeyed i then skey rgn i else unit
// using a hand-rolled maybe-type for KreMLin to avoid an auto-gen'd monorphic instance from appearing in the top-level interface in C

val get_skey: #r:rid -> #i:id{skeyed i} -> akey r i -> Tot (skey r i)
let get_skey #rgn #i (Just k) = k

val mk_akey: #r:rid -> #i:id -> _:skey r i{skeyed i} -> Tot (akey r i)
let mk_akey #r #i sk = Just sk

val mk_akey_null: #r:rid -> #i:id -> _:unit{~(skeyed i)} -> Tot (akey r i)
let mk_akey_null #r #i _ = Nothing

val akey_gen: r:erid -> i:id -> ST (akey r i)
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r Set.empty h0 h1 /\
      ((get_skey #r #i k) `unmapped_in` h0) /\
      live h1 (get_skey #r #i k)
    else h0 == h1))
let akey_gen r i =
  if skeyed i then
    let k:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    // FIXME(adl) is this supposed to be random?
    // e.g. Bytes.random (skeylen i) k;
    Just k
  else Nothing

#reset-options "--max_fuel 0 --z3rlimit 40"

val akey_coerce: r:erid -> i:id -> kb:lbuffer (UInt32.v (skeylen i)) -> ST (akey r i)
  (requires (fun h -> live h kb))
  (ensures  (fun h0 k h1 ->
    if skeyed i then
      HS.modifies (Set.singleton r) h0 h1 /\
      HS.modifies_ref r Set.empty h0 h1 /\
      ((get_skey #r #i k) `unmapped_in` h0) /\
      live h1 (get_skey #r #i k)
    else h0 == h1))
let akey_coerce r i kb =
  if skeyed i then
    // FIXME(adl) leaks, but only once per AEAD instance
    let sk:skey r i = Buffer.rcreate r 0uy (skeylen i) in
    let h1 = ST.get () in
    Buffer.blit kb 0ul sk 0ul (skeylen i);
    let h2 = ST.get () in
    lemma_reveal_modifies_1 sk h1 h2;
    Just sk
  else Nothing

#reset-options

(** One-time MAC instance *)
type id = MAC.id

(**
 * Also used in miTLS ('model' may be better than 'ideal');
 * could be loaded from another module.
 * This flag enables conditional idealization by keeping additional data:
 * - this should not affect the code behavior
 * - this may cause the code not to compile to KreMLin/C
 *)
unfold let authId ((i,_):id) = safeHS i && mac1 i

// Do we need authId i ==> ideal?

// the index is the base index (controlling agility and idealization)
// plus the value of the unique IV for this MAC
// TODO make it a dependent pair to support agile IV types

(** Authenticated payload: a sequence of words *)
type text = Seq.seq (lbytes 16)

(** One-time MAC log, None or Some (m, MAC(m)), stores nonce for framing purposes *)
type log (i:id) = n:UInt128.t{n == snd i} * option (text * (lbytes 16))

let log_cmp (#i:id) :Preorder.preorder (log i) =
  fun (a b: log i) ->
  match snd a, snd b with
  | Some (l,t) , Some (l',t') -> l == l' /\ t == t' // avoid inversion
  | None, _                   -> True
  | _                         -> False

let ideal_log (i:id) (r:erid) = m_rref r (log i) log_cmp

let log_ref (i:id) (r:erid) = if mac_log then (ideal_log i r) else unit

let ilog (#i:id) (#r:erid) (l:log_ref i r{mac_log}) : Tot (ideal_log i r) = l

noeq type state (i:id) =
  | State:
    #region: erid ->
    r: MAC.elemB i{
      let b = MAC.as_buffer r in Buffer.frameOf b == region /\ (~ (HS.is_mm (Buffer.content b)))} ->
    s: PL.wordB_16{frameOf s == region /\ disjoint (MAC.as_buffer r) s /\ (~ (HS.is_mm (Buffer.content s)))} ->
    log: log_ref i region ->
    state i

let live_ak #r (#i:id) m (ak:akey r (fst i)) =
  skeyed (fst i) ==> live m (get_skey #r #(fst i) ak)

let mac_is_fresh (i:id) (region:erid) m0 (st:state i) m1 =
   ((MAC.as_buffer st.r) `unused_in` m0) /\
   (st.s `unused_in` m0) /\
   (mac_log ==> HS.unused_in (ilog st.log) m0)

let mac_is_unset (i:id) (region:erid) (st:state i) m =
   st.region == region /\
   MAC.norm_r m st.r /\
   Buffer.live m st.s /\
   (mac_log ==>
      HS.contains m (ilog st.log) /\
      snd (HS.sel m (ilog st.log)) == None)

let genPost (i:id) (region:erid) m0 (st:state i) m1 =
  mac_is_fresh i region m0 st m1 /\
  mac_is_unset i region st m1

#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
// Brittle proof. Merging the branches of the first conditional breaks it
val alloc: region:erid -> i:id
  -> ak:akey region (fst i)
  // Could live in a different region, but this simplifies the spec
  // FIXME(adl): k should be stack allocated to avoid more memory leaks,
  // relaxing the region condition
  -> k:lbuffer (UInt32.v (keylen (fst i))) // {frameOf k == region}
  -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures  (fun m0 st m1 ->
    genPost i region m0 st m1 /\
    Buffer.modifies_1 k m0 m1))
let alloc region i ak k =
  let h0 = ST.get () in
  // FIXME(adl) these 2 allocations leak on every encryption!
  // mitigated with unsound_free below
  let r = MAC.rcreate region i in
  let s = FStar.Buffer.rcreate region 0uy 16ul in
  let h1 = ST.get () in
  assert_norm (UInt32.v 16ul == 16);
  if skeyed (fst i) then
    begin
    let rb = get_skey #region #(fst i) ak in
    let sb = k in
    MAC.encode_r r rb;
    let h2 = ST.get () in
    lemma_reveal_modifies_1 (MAC.as_buffer r) h1 h2;
    lemma_intro_modifies_1 k h0 h2;
    Buffer.blit sb 0ul s 0ul 16ul;
    let h3 = ST.get () in
    lemma_reveal_modifies_1 s h2 h3;
    lemma_intro_modifies_1 k h0 h3
    end
  else
    begin
    let rb = sub k 0ul  16ul in
    let sb = sub k 16ul 16ul in
    MAC.encode_r r rb;
    let h2 = ST.get () in
    lemma_reveal_modifies_1 (MAC.as_buffer r) h1 h2;
    lemma_intro_modifies_1 k h0 h2;
    Buffer.blit sb 0ul s 0ul 16ul;
    let h3 = ST.get () in
    lemma_reveal_modifies_1 s h2 h3;
    lemma_intro_modifies_1 k h0 h3
    end;
  if mac_log then
    begin
    let log = ST.ralloc #(log i) #log_cmp region (snd i, None) in
    let h4 = ST.get() in
    lemma_intro_modifies_1 k h0 h4;
    State #i #region r s log
    end
   else
    begin
    let h4 = ST.get() in
    lemma_intro_modifies_1 k h0 h4;
    State #i #region r s ()
    end

// FIXME(adl) 09/04/2018
// The allocation code above leaks memory because of ralloc
// Unfortunately, r and s must be allocated in eternal regions because
// they are stored in idealization tables. We can't let this allocation leak
// because it is used for QUIC packet encryption, so we
let unsound_free (i:id) (st:state i) : ST unit
  (requires fun h0 -> True) // ~(safeHS i)
  (ensures fun h0 () h1 -> h0 == h1)
  =
  assume false;
  if not (mac1 (fst i)) then // OK to deallocate because the state is not stored in a table
   begin
    let State r s log = st in
    FStar.Buffer.rfree s;
    MAC.unsound_free r // despite the elemB abstraction in MAC this is a buffer
   end

(* Currently mitigated externally
let unsound_free_akey (region:erid) (i:id) (ak:akey region (fst i)) : ST unit
  (requires fun h0 -> True) // ~(safeHS i)
  (ensures fun h0 () h1 -> h0 == h1)
  =
  assume false;
  match ak with
  | Nothing -> ()
  | Just kb -> FStar.Buffer.rfree kb
*)

#set-options " --initial_ifuel 0 --max_ifuel 0"

val gen: region:erid -> i:id -> ak:akey region (fst i) -> ST (state i)
  (requires (fun m0 -> live_ak m0 ak))
  (ensures (fun m0 st m1 ->
    genPost i region m0 st m1 /\
    modifies_one region m0 m1 /\
    modifies_ref region Set.empty m0 m1 ))
let gen region i ak =
  let len = keylen (fst i) in
  let k = FStar.Buffer.create 0uy len in
  let h1 = ST.get() in
  random (UInt32.v len) k;
  assert (live_ak h1 ak);
  let st =  alloc region i ak k in
  let h3 = ST.get() in
  lemma_reveal_modifies_1 k h1 h3;
  st

val coerce: region:erid -> i:id{~(authId i)}
  -> ak:akey region (fst i)
  -> k:lbuffer (UInt32.v (keylen (fst i))) //{frameOf k == region}
  -> ST (state i)
  (requires (fun m0 -> live m0 k /\ live_ak m0 ak))
  (ensures (fun m0 st m1 ->
    genPost i region m0 st m1 /\
    modifies_1 k m0 m1))
let coerce region i ak k =
  alloc region i ak k


(** Hash accumulators (several per instance)

  A partial multiplicative MAC computation
  (considered secret, declassified only via mac and declassify)

  We need to isolate the state of partial MAC computations.
  The key state is now clamped
  We use state-passing in the spec (to be reviewed)
  Not sure what to record for separation.
*)

(** Should be abstract, but causes code duplication *)
let irtext (r:rid) = if mac_log then (x:ST.reference text{HS.frameOf x == r}) else unit

noeq abstract type accBuffer (i:id) =
  | Acc: a:MAC.elemB i ->
         l:irtext (Buffer.frameOf (MAC.as_buffer a)) ->
         accBuffer i

let alog (#i:id) (acc:accBuffer i{mac_log}) : ST.reference text =
  acc.l

noextract val abuf: #i:id -> acc:accBuffer i -> GTot (MAC.elemB i)
noextract let abuf #i acc = acc.a

let acc_inv (#i:id) (st:state i) (acc:accBuffer i) h : Type0 =
  MAC.norm_r h st.r /\ MAC.norm h acc.a /\
  disjoint (MAC.as_buffer st.r) (MAC.as_buffer acc.a) /\
  (mac_log ==> (
    let log = HS.sel h (alog acc) in
    let a = MAC.sel_elem h acc.a in
    let r = MAC.sel_elem h st.r in
    HS.contains h (alog acc) /\
    disjoint_ref_1 (MAC.as_buffer acc.a) (alog acc) /\
    disjoint_ref_1 (MAC.as_buffer st.r)  (alog acc) /\
    a == MAC.poly log r))

val frame_acc_inv: #i:id -> st:state i -> acc:accBuffer i -> h0:mem -> h1:mem -> Lemma
  (requires
     (acc_inv st acc h0 /\
      MAC.live h1 acc.a /\ MAC.live h1 st.r /\
      (mac_log ==>
        HS.contains h1 (alog acc) /\
        HS.sel h0 (alog acc) == HS.sel h1 (alog acc)) /\
        as_seq h0 (MAC.as_buffer acc.a) == as_seq h1 (MAC.as_buffer acc.a) /\
        as_seq h0 (MAC.as_buffer st.r)  == as_seq h1 (MAC.as_buffer st.r)))
  (ensures (acc_inv st acc h1))
let frame_acc_inv #i st acc h0 h1 =
  MAC.frame_norm h0 h1 acc.a;
  MAC.frame_norm h0 h1 st.r;
  MAC.frame_sel_elem h0 h1 acc.a;
  MAC.frame_sel_elem h0 h1 st.r


// not framed, as we allocate private state on the caller stack
val start: #i:id -> st:state i -> StackInline (accBuffer i)
  (requires (fun h -> MAC.norm_r h st.r))
  (ensures  (fun h0 a h1 ->
    Buffer.frameOf (MAC.as_buffer a.a) == h1.tip /\
    ((MAC.as_buffer (abuf a)) `Buffer.unused_in` h0) /\
    (mac_log ==>
      HS.sel h1 (alog a) = Seq.createEmpty /\
      ((alog a) `HS.unused_in` h0)) /\
    acc_inv st a h1 /\
    modifies_0 h0 h1))

#set-options " --initial_ifuel 1 --max_ifuel 1"

let start #i st =
  let h0 = ST.get () in
  let a = MAC.start #i in
  let h1 = ST.get () in
  lemma_reveal_modifies_0 h0 h1;
  if mac_log then
    let log = salloc #text #(Heap.trivial_preorder text) Seq.createEmpty in
    let h2 = ST.get () in
    // Needed to prove disjointness of st.r and log
    assert (HS.sel h2 (Buffer.content (MAC.as_buffer st.r)) =!= Seq.createEmpty);
    lemma_intro_modifies_0 h0 h2;
    MAC.frame_sel_elem h1 h2 a;
    MAC.poly_empty #i (HS.sel h2 log) (MAC.sel_elem h2 st.r);
    Acc #i a log
  else
    Acc #i a ()


let modifies_buf_and_ref (#a:Type) (#b:Type)
  (buf:Buffer.buffer a)
  (ref:reference b{frameOf buf == HS.frameOf ref}) h0 h1 : GTot Type0 =
  HS.modifies_one (HS.frameOf ref) h0 h1 /\
  HS.modifies_ref (HS.frameOf ref) (Set.union (Set.singleton (HS.as_addr ref))
                                              (Set.singleton (Buffer.as_addr buf))) h0 h1 /\
  (forall (#t:Type) (buf':Buffer.buffer t).
    (frameOf buf' == HS.frameOf ref /\ Buffer.live h0 buf' /\
    Buffer.disjoint buf buf' /\ Buffer.disjoint_ref_1 buf' ref) ==>
    equal h0 buf' h1 buf')

(* TODO: begin here *)

(** From the current memory state, returns the word corresponding to a wordB *)
noextract val sel_word: h:mem -> b:PL.wordB{live h b} -> GTot word
let sel_word h b = as_seq h b

(** Only used when mac_log is true *)
private noextract val _read_word: len:u32 -> b:PL.wordB{length b == UInt32.v len}
  -> s:Seq.seq UInt8.t -> i:u32{UInt32.v i <= UInt32.v len} -> ST word
  (requires (fun h -> live h b /\ Seq.slice (sel_word h b) 0 (UInt32.v i) == s))
  (ensures  (fun h0 s h1 -> h0 == h1 /\ live h1 b /\ s == sel_word h1 b))
let rec _read_word len b s i =
  let h = ST.get () in
  if UInt32.v i = UInt32.v len then
    begin
    Seq.lemma_eq_intro s (sel_word h b);
    s
    end
  else
    begin
    let x = b.(i) in
    let s' = FStar.Seq.(s @| Seq.create 1 x) in
    Seq.lemma_eq_intro s' (Seq.slice (sel_word h b) 0 (UInt32.v i + 1));
    _read_word len b s' (FStar.UInt32.(i +^ 1ul))
    end

noextract val read_word: len:u32 -> b:PL.wordB{length b == UInt32.v len} -> ST word
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 b /\ r == (sel_word h1 b)))
let read_word len b =
  let h = ST.get() in
  let s0 = Seq.createEmpty #UInt8.t in
  Seq.lemma_eq_intro s0 (Seq.slice (sel_word h b) 0 0);
  _read_word len b s0 0ul

(* TODO: end here *)


// update [was add]; could add finalize (for POLY1305 when last block < 16).
val update: #i:id -> st:state i -> acc:accBuffer i -> w:lbuffer 16 ->
  Stack unit
  (requires (fun h ->
    acc_inv st acc h /\
    Buffer.live h w /\
    Buffer.disjoint (MAC.as_buffer acc.a) w /\
    Buffer.disjoint (MAC.as_buffer st.r) w /\
    (mac_log ==> Buffer.disjoint_ref_1 w (alog acc))))
  (ensures  (fun h0 _ h1 ->
     acc_inv st acc h1 /\
     Buffer.live h0 w /\
     (if mac_log then
       HS.sel h1 (alog acc) ==
       Seq.cons (Buffer.as_seq h0 w) (HS.sel h0 (alog acc)) /\
       (let buf = MAC.as_buffer acc.a in
        let rid = frameOf buf in
        modifies_buf_and_ref buf (alog acc) h0 h1)
     else
       Buffer.modifies_1 (MAC.as_buffer acc.a) h0 h1) ))

#reset-options "--z3rlimit 100"
let update #i st acc w =
  let h0 = ST.get () in
  if mac_log then
    begin
    let v = read_word 16ul w in
    let vs = !(alog acc) in
    (alog acc) := Seq.cons v vs;
    let h1 = ST.get () in
    MAC.frame_sel_elem h0 h1 st.r;
    MAC.frame_sel_elem h0 h1 acc.a;
    MAC.poly_cons #i v vs (MAC.sel_elem h0 st.r)
    end;
  let h1 = ST.get () in
  MAC.update st.r acc.a w;
  let h2 = ST.get () in
  lemma_reveal_modifies_1 (MAC.as_buffer acc.a) h1 h2;
  MAC.frame_sel_elem h1 h2 st.r
#reset-options


let pairwise_distinct (r1:HS.rid) (r2:HS.rid) (r3:HS.rid) =
  r1 <> r2 /\ r2 <> r3 /\ r3 <> r1

let modifies_bufs_and_ref (#a:Type) (#b:Type) (#c:Type) (#rel:Preorder.preorder c)
  (buf1:Buffer.buffer a) (buf2:Buffer.buffer b)
  (ref:mreference c rel{pairwise_distinct (frameOf buf1) (frameOf buf2) (HS.frameOf ref)}) h0 h1 : GTot Type0 =
  HS.modifies (Set.union (Set.singleton (frameOf buf1))
                         (Set.union (Set.singleton (frameOf buf2))
			            (Set.singleton (HS.frameOf ref)))) h0 h1 /\
  HS.modifies_ref (HS.frameOf ref) (Set.singleton (HS.as_addr ref)) h0 h1 /\
  Buffer.modifies_buf_1 (frameOf buf1) buf1 h0 h1 /\
  Buffer.modifies_buf_1 (frameOf buf2) buf2 h0 h1

let mac_ensures
  (i:id) (st:state i) (acc:accBuffer i)
  (tag:MAC.tagB{pairwise_distinct (frameOf (MAC.as_buffer (abuf acc))) (frameOf tag) st.region})
  (h0:mem) (h1:mem) =
  Buffer.live h1 st.s /\
  MAC.live h1 st.r /\
  Buffer.live h1 tag /\
  acc_inv st acc h0 /\ (
  if mac_log then
    let vs = HS.sel h1 (alog acc) in
    let r = MAC.sel_elem h1 st.r in
    let s = Buffer.as_seq h1 st.s in
    let t = MAC.mac vs r s in
    let log = ilog st.log in
    let buf = MAC.as_buffer (abuf acc) in
    Buffer.as_seq h1 tag == t /\ (
    if authId i then
      HS.contains h1 log /\
      HS.sel h1 log == (snd i, Some (vs, t)) /\
      modifies_bufs_and_ref buf tag log h0 h1
    else
      Buffer.modifies_2 (MAC.as_buffer (abuf acc)) tag h0 h1)
  else
    Buffer.modifies_2 (MAC.as_buffer (abuf acc)) tag h0 h1)

val mac:
  #i:id ->
  st:state i ->
  acc:accBuffer i ->
  tag:lbuffer 16{pairwise_distinct (frameOf (MAC.as_buffer (abuf acc))) (frameOf tag) st.region} ->
  Stack unit
  (requires (fun h0 ->
    acc_inv st acc h0 /\
    Buffer.live h0 tag /\
    Buffer.live h0 st.s /\
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag /\
    Buffer.disjoint_2 (MAC.as_buffer st.r) st.s tag /\
    Buffer.disjoint st.s tag /\
    (mac_log ==> frameOf tag <> HS.frameOf (alog acc) \/
                 Buffer.disjoint_ref_1 tag (alog acc)) /\
    (authId i ==> snd (HS.sel h0 (ilog st.log)) == None)))
  (ensures (fun h0 _ h1 -> mac_ensures i st acc tag h0 h1))


#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0"
let mac #i st acc tag =
  let h0 = ST.get () in
  MAC.finish st.s acc.a tag;
  let h1 = ST.get () in
  if mac_log then
    begin
    let t = read_word 16ul tag in // load_bytes 16ul tag in
    lemma_reveal_modifies_2 (MAC.as_buffer acc.a) tag h0 h1;
    let vs = !(alog acc) in
    assert (log_cmp #i (snd i, None) (snd i, Some (vs, t)));
    ST.recall #(log i) #log_cmp (ilog st.log);
    if authId i then
      ST.op_Colon_Equals #(log i) #log_cmp (ilog st.log) (snd i, Some (vs, t));
    let h2 = ST.get () in
    MAC.frame_sel_elem h0 h1 st.r;
    MAC.frame_sel_elem h1 h2 st.r;
    MAC.frame_sel_elem h1 h2 acc.a;
    let vs = HS.sel h2 (alog acc) in
    let r = MAC.sel_elem h2 st.r in
    let s = Buffer.as_seq h2 st.s in
    let t = MAC.mac vs r s in
    MAC.lemma_poly_finish_to_mac i h2 tag (MAC.sel_elem h0 acc.a) h0 st.s vs r
    end
#reset-options


let verify_liveness (#i:id) (st:state i) (tag:MAC.tagB) (h:mem) =
  Buffer.live h st.s /\
  MAC.live h st.r /\
  Buffer.live h tag

let verify_ok (#i:id) (st:state i) (acc:accBuffer i) (tag:MAC.tagB)
  (h0:mem) (b:bool) =
  verify_liveness st tag h0 /\
  (if mac_log then
    let vs = HS.sel h0 (alog acc) in
    let r = MAC.sel_elem h0 st.r in
    let s = Buffer.as_seq h0 st.s in
    let t = MAC.mac vs r s in
    let verified = Seq.eq t (MAC.sel_word h0 tag) in
    if authId i then
      match snd (HS.sel h0 (ilog st.log)) with
      | Some (vs',t') ->
        let correct = t = t' && Seq.eq vs vs' in
        b == (verified && correct)
      | None -> b == false
    else b == verified
  else True)

let verify_ensures (#i:id) (st:state i) (acc:accBuffer i) (tag:MAC.tagB)
  (h0:mem) (b:bool) (h1:mem) =
  Buffer.modifies_1 (MAC.as_buffer acc.a) h0 h1 /\
  verify_liveness st tag h1 /\
  verify_ok st acc tag h0 b

(** Auxiliary lemma to propagate `ilog st.log` and `alog acc` in `verify` *)
private val modifies_verify_aux: #a:Type -> #b:Type -> #c:Type -> #d:Type ->
  #r:erid -> #rel:Preorder.preorder c -> mref:ST.m_rref r c rel -> ref:HS.reference d ->
  buf1:Buffer.buffer a -> buf2:Buffer.buffer b ->
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> Lemma
  (requires (
    disjoint_ref_2 buf1 mref ref /\
    disjoint_ref_1 buf2 mref /\
    frameOf buf2 == h1.tip /\
    fresh_frame h0 h1 /\ modifies_0 h1 h2 /\ modifies_2 buf1 buf2 h2 h3))
  (ensures (
    (HS.contains h0 mref ==> (HS.contains h3 mref /\ HS.sel h0 mref == HS.sel h3 mref)) /\
    (HS.contains h0 ref    ==> (HS.contains h3 ref    /\ HS.sel h0 ref == HS.sel h3 ref))))
#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
let modifies_verify_aux #a #b #c #d #r #rel mref ref buf1 buf2 h0 h1 h2 h3 =
  lemma_reveal_modifies_0 h1 h2;
  lemma_reveal_modifies_2 buf1 buf2 h2 h3

val verify:
  #i:id ->
  st:state i ->
  acc:accBuffer i ->
  tag:MAC.tagB ->
  Stack bool
  (requires (fun h0 ->
    acc_inv st acc h0 /\
    verify_liveness st tag h0 /\
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag))
  (ensures (fun h0 b h1 -> verify_ensures st acc tag h0 b h1))
#reset-options "--z3rlimit 400"
let verify #i st acc tag =
  // FIXME(adl) workaround for normalization bug
  if (*authId i*) safeHS (fst i) && mac1 (fst i) then ST.recall #(log i) #log_cmp (ilog st.log);
  let h0 = ST.get () in
  push_frame ();
  let h1 = ST.get () in
  let computed = Buffer.create 0uy 16ul in
  let h2 = ST.get () in
  MAC.finish st.s acc.a computed;
  let h3 = ST.get () in
  // TODO: should use constant-time comparison
  let verified = Buffer.eqb computed tag 16ul in
  let b =
    if mac_log then
      begin
      MAC.frame_sel_elem h0 h2 st.r;
      MAC.frame_sel_elem h2 h3 st.r;
      MAC.frame_sel_elem h0 h2 acc.a;
      ST.recall #(log i) #log_cmp (ilog st.log);
      modifies_verify_aux (ilog st.log) (alog acc) (MAC.as_buffer acc.a) computed
        h0 h1 h2 h3;
      let t = read_word 16ul computed in
      let vs = !(alog acc) in
      MAC.lemma_poly_finish_to_mac i h3 computed (MAC.sel_elem h0 acc.a) h0 st.s vs (MAC.sel_elem h0 st.r);
      if authId i then
        begin
        let log = !(ilog st.log) in // Don't inline it below; doesn't work
        match snd log with
        | Some (vs',t') ->
          let correct = t = t' && Seq.eq vs vs' in
          verified && correct
        | _ -> false
        end
      else verified
      end
    else verified
  in
  pop_frame ();
  b
