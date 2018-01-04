module Crypto.AEAD.Main

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.UInt32
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module I = Crypto.Indexing
module Plain = Crypto.Plain

(* Several constants that the interface relies on *)
type eternal_region =
     rgn:HS.rid {HS.is_eternal_region rgn}

type lbuffer (l:nat) =
     b:Buffer.buffer UInt8.t {Buffer.length b == l}

let ivlen (a:I.cipherAlg) =
    12ul

let taglen =
    16ul

let iv (alg:I.cipherAlg) =
     let open FStar.Mul in
     n:UInt128.t { UInt128.v n < pow2 (8 * v (ivlen alg)) }

let aadmax =
    assert_norm (2000 <= pow2 32 - 1);
    2000ul // more than enough for TLS

type aadlen_32 =
     l:UInt32.t {l <=^ aadmax}

val keylen      : I.id -> UInt32.t
val statelen    : I.id -> UInt32.t

let bytes = FStar.Bytes.bytes
let lbytes  (l:nat) = b:bytes  {Seq.length (Bytes.reveal b) == l}
type adata = b:bytes {Seq.length (Bytes.reveal b) <= v aadmax}
type cipher (i:I.id) (l:nat) = lbytes (l + v taglen)

inline_for_extraction
val entry : i:I.id -> Type0
let nonce (i:I.id) = iv (I.cipherAlg_of_id i)
val mk_entry (#i:I.id) :
    nonce:nonce i ->
    ad:adata ->
    #l:Plain.plainLen ->
    p:Plain.plain i l ->
    c:cipher i (Seq.length (Plain.as_bytes p)) ->
    GTot (entry i)
val entry_injective (#i:I.id)
                    (n:nonce i) (n':nonce i)
                    (ad:adata) (ad':adata)
                    (#l:Plain.plainLen) (#l':Plain.plainLen)
                    (p:Plain.plain i l) (p':Plain.plain i l')
                    (c:cipher i (Seq.length (Plain.as_bytes p))) (c':cipher i (Seq.length (Plain.as_bytes p')))
  : Lemma (let e  = mk_entry n ad p c in
           let e' = mk_entry n' ad' p' c' in
           (e == e' <==> (n == n' /\ ad == ad' /\ l == l' /\ p == p' /\ c == c')))
val nonce_of_entry (#i:_) (e:entry i) : GTot (nonce i)

let safeMac (i:I.id) = Flag.safeHS i && Flag.mac1 i
let safeId  (i:I.id) = Flag.safeId i

val aead_state     : I.id -> I.rw -> Type0
val log_region: #i:_ -> #rw:_ -> aead_state i rw -> eternal_region
val prf_region: #i:_ -> #rw:_ -> aead_state i rw -> eternal_region
val log       : #i:_ -> #rw:_ -> s:aead_state i rw{safeMac i} -> HS.mem -> GTot (Seq.seq (entry i))

let address   = nat
let addr_unused_in (r:HS.rid) (a:address) (m0:HS.mem) =
  let open FStar.HyperStack in
  FStar.Monotonic.Heap.addr_unused_in a (Map.sel m0.h r)
let contains_addr (rid:HS.rid) (a:address) (m:HS.mem) =
  ~ (addr_unused_in rid a m)
let fresh_addresses (rid:HS.rid) (addrs:FStar.TSet.set address) (m0:HS.mem) (m1:HS.mem) =
  forall a. a `FStar.TSet.mem` addrs ==>
       addr_unused_in rid a m0 /\
       contains_addr  rid a m1

let fp = FStar.Ghost.erased FStar.Pointer.Base.loc
val footprint     : #i:_ -> #rw:_ -> aead_state i rw -> GTot fp
val modifies_fp (fp:fp) (h0:HS.mem) (h1:HS.mem): Type0
val preserves_fp (fp:fp) (h0:HS.mem) (h1:HS.mem) : Type0

//Leaving this abstract for now; but it should imply Crypto.AEAD.Invariant.safelen i len (otp_offset i)
val safelen     : I.id -> nat -> bool
let ok_plain_len_32 (i:I.id) = l:UInt32.t{safelen i (v l)}

val invariant : #i:_ -> #rw:_ -> aead_state i rw -> HS.mem -> Type0
val frame_invariant: #i:_ -> #rw:_ -> st:aead_state i rw -> h0:HS.mem -> h1:HS.mem ->
    Lemma (invariant st h0 /\ preserves_fp (footprint st) h0 h1 ==>
           invariant st h1)

//val as_set': #a:Type -> list a -> Tot (TSet.set a)
let rec as_set (#a:Type) (l:list a) : TSet.set a =
  match l with
  | [] -> TSet.empty
  | hd::tl -> TSet.union (TSet.singleton hd) (as_set tl)

//unfold let as_set (#a:Type) (l:list a) : TSet.set a = normalize_term (as_set' l)

(*** The main stateful API ***)

(** Allocating a writer **)
val gen (i:I.id)
        (prf_rgn:eternal_region)
        (log_rgn:eternal_region{HS.disjoint prf_rgn log_rgn})
  : ST (aead_state i I.Writer)
    (requires (fun h -> True))
    (ensures (fun h0 s h1 ->
             log_region s == log_rgn /\
             prf_region s == prf_rgn /\
             (exists fresh.
                fresh_addresses prf_rgn fresh h0 h1 // /\
                // footprint s == as_set [(log_rgn, AllRefs); (prf_rgn, SomeRefs fresh)]
             ) /\
             (safeMac i ==> log s h1 == Seq.createEmpty) /\
             invariant s h1
    ))


(** Building a reader from a writer **)

// (* A reader never writes to the log_region, but may write to the prf_region *)
// let read_footprint (#i:_) (wr:aead_state i I.Writer) : GTot fp =
//   FStar.TSet.filter (fun (rs:(HS.rid * refs_in_region)) -> fst rs == prf_region wr)
//                     (footprint wr)

val genReader
           (#i: I.id)
           (wr: aead_state i I.Writer)
 : ST (aead_state i I.Reader)
  (requires (fun h -> invariant wr h))
  (ensures  (fun h0 rd h1 ->
               HS.modifies Set.empty h0 h1 /\
               invariant rd h1 /\
               log_region rd == log_region wr /\
               prf_region rd == prf_region wr//  /\
               // footprint  rd == read_footprint wr
 ))


(** [coerce]: Only needed for modeling the adversary *)
val coerce
         (i: I.id)
       (rgn: eternal_region)
       (key: lbuffer (v (keylen i)))
      : ST  (aead_state i I.Writer)
  (requires (fun h ->
             ~ (Flag.prf i) /\
             Buffer.live h key))
  (ensures  (fun h0 st h1 ->
               HS.modifies Set.empty h0 h1 /\
               invariant st h1))

(** [leak]: Only needed for modeling the adversary *)
val leak
      (#i: I.id)
      (st: aead_state i I.Writer)
    : ST (lbuffer (v (statelen i)))
  (requires (fun _ -> ~(Flag.prf i)))
  (ensures  (fun h0 _ h1 ->
               HS.modifies Set.empty h0 h1 /\
               invariant st h1))

// enc_dec_separation: Calling AEAD.encrypt/decrypt requires this separation
let enc_dec_separation (#i:_) (#rw:_) (st:aead_state i rw)
                       (#aadlen:nat) (aad: lbuffer aadlen)
                       (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                       (#cipherlen: nat) (cipher:lbuffer cipherlen) =
    Buffer.disjoint aad cipher /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher /\
    HS.disjoint_regions (Set.as_set [Buffer.frameOf (Plain.as_buffer plain);
                                     Buffer.frameOf cipher;
                                     Buffer.frameOf aad])
                        (Set.as_set [log_region st;
                                     prf_region st]) /\
    Buffer.frameOf cipher <> HS.root /\
    Buffer.frameOf aad <> HS.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HS.root
    (* HS.is_eternal_region (Buffer.frameOf cipher) /\ // why? *)
    (* HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\ //why? *)
    (* HS.is_eternal_region (Buffer.frameOf aad) /\ //why? *)

let enc_dec_liveness (#i:_) (#rw:_) (st:aead_state i rw)
                     (#aadlen:nat) (aad: lbuffer aadlen)
                     (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                     (#cipherlen: nat) (cipher:lbuffer cipherlen) (h:HS.mem) =
    let open HS in
    Buffer.live h aad /\
    Buffer.live h cipher /\
    Plain.live h plain /\
    log_region st `is_in` h.h /\
    prf_region st `is_in` h.h

let entry_of
          (#i: I.id)
           (n: iv (I.cipherAlg_of_id i))
     (#aadlen: aadlen_32)
         (aad: lbuffer (v aadlen))
   (#plainlen: ok_plain_len_32 i)
       (plain: Plain.plainBuffer i (v plainlen))
  (cipher_tag: lbuffer (v plainlen + v taglen))
           (h: HS.mem) : GTot (entry i) =
  let aad = Buffer.as_seq h aad in
  let p = Plain.sel_plain h plainlen plain in
  let c = Buffer.as_seq h cipher_tag in
  mk_entry n (FStar.Bytes.hide aad) p (FStar.Bytes.hide c)

let entry_for_nonce (#i:_) (#rw:_) (n:nonce i) (st:aead_state i rw) (h:HS.mem{safeMac i})
  : GTot (option (entry i)) =
    Seq.ghost_find_l (fun e -> nonce_of_entry e = n) (log st h)

let fresh_nonce (#i:_) (#rw:_) (n:nonce i) (st:aead_state i rw) (h:HS.mem{safeMac i}): GTot bool =
  None? (entry_for_nonce n st h)

val encrypt
          (i: I.id)
         (st: aead_state i I.Writer)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
      (plain: Plain.plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST unit
  (requires (fun h ->
               enc_dec_separation st aad plain cipher_tag /\
               enc_dec_liveness st aad plain cipher_tag h /\
               invariant st h /\
               (safeMac i ==> fresh_nonce n st h)))
  (ensures (fun h0 _ h1 ->
               // modifies_fp FStar.Pointer.Base.(loc_union (footprint st) (loc_buffer cipher_tag)) h0 h1 /\
               enc_dec_liveness st aad plain cipher_tag h1 /\
               invariant st h1 /\
               (safeMac i ==>
                   log st h1 ==
                   Seq.snoc (log st h0) (entry_of n aad plain cipher_tag h1))))

val decrypt
          (i: I.id)
         (st: aead_state i I.Reader)
          (n: iv (I.cipherAlg_of_id i))
     (aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
   (plainlen: ok_plain_len_32 i)
      (plain: Plain.plainBuffer i (v plainlen))
 (cipher_tag: lbuffer (v plainlen + v taglen))
            : ST bool
  (requires (fun h ->
               enc_dec_separation st aad plain cipher_tag /\
               enc_dec_liveness st aad plain cipher_tag h /\
               invariant st h))
  (ensures (fun h0 verified h1 ->
               invariant st h1 /\
               enc_dec_liveness st aad plain cipher_tag h1 /\
               // modifies_fp FStar.Pointer.Base.(loc_union (footprint st) (loc_buffer (Plain.as_buffer plain))) h0 h1 /\
               (safeId i ==> entry_for_nonce n st h1 == Some (entry_of n aad plain cipher_tag h1))))
