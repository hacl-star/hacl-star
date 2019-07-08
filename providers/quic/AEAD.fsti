(**
  This interfaces provides an abstraction for the verified Hacl* Crypto.AEAD.Main module,
  using FStar.Bytes rather than buffers.
*)
module AEAD
module HS = FStar.HyperStack //Added automatically

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
//module Plain = Crypto.Plain

open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


type safeid = i:I.id{Flag.safeId i}
type unsafeid = i:I.id{~ (Flag.safeId i)}

let safeMac (i:I.id) = Flag.safeHS i && Flag.mac1 i
let safeId  (i:I.id) = Flag.safeId i

let ivlen (alg:I.cipherAlg) = 12ul

let taglen = 16ul

let iv (alg:I.cipherAlg) =
  let open FStar.Mul in
  n:U128.t { U128.v n < pow2 (8 * v (ivlen alg)) }

let aadmax =
  assert_norm (2000 <= pow2 32 - 1);
  2000ul // arbitrary; enough for TLS

type aadlen_32 = l:U32.t {l <=^ aadmax}



type plainLen = l:nat{l + v taglen < pow2 32}

type plainLenMin (lmin:plainLen) = l:plainLen{l >= lmin}



noeq type plain_pkg =
  | PlainPkg:
    min_len: plainLen ->
    plain: (i:I.id -> plainLenMin min_len -> eqtype) ->
    as_bytes: (i:I.id -> l:plainLenMin min_len -> plain i l -> GTot (lbytes l)) ->
    repr: (i:unsafeid -> l:plainLenMin min_len -> p:plain i l -> Tot (b:lbytes l{b == as_bytes i l p})) ->
    plain_pkg

noeq type nonce_pkg =
  | NoncePkg:
    nonce: (i:I.id -> t:Type0{hasEq t}) ->
    as_bytes: (i:I.id -> nonce i -> GTot (iv (I.cipherAlg_of_id i))) ->
    repr: (i:I.id{~ (safeId i)} -> n:nonce i -> Tot (r:iv (I.cipherAlg_of_id i){r == as_bytes i n})) ->
    nonce_pkg
    
    
noeq type info' = {
  alg: I.aeadAlg;
  prf_rgn: subrgn tls_tables_region;
  log_rgn: subrgn tls_tables_region;
  plain: plain_pkg;
  nonce:nonce_pkg;
}


type info (i:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

let plainLenM (#i:I.id) (u:info i) = plainLenMin (PlainPkg?.min_len u.plain)

let plain (#i:I.id) (u:info i) (l:plainLenM u) =
  (PlainPkg?.plain u.plain) i l
 
let plain_as_bytes (#i:I.id) (#u:info i) (#l:plainLenM u) (p:plain u l) : GTot (lbytes l) = 
  (PlainPkg?.as_bytes u.plain) i l p
  
let plain_repr (#i:unsafeid) (#u:info i) (#l:plainLenM u) (p:plain u l) : Tot (r:lbytes l{r == plain_as_bytes p}) =
  (PlainPkg?.repr u.plain) i l p

//let nonce_tag (#i:I.id) (u:info i) : t:Type0{hasEq t} = NoncePkg?.tag u.nonce

let nonce (#i:I.id) (u:info i) : t:Type0{hasEq t} = NoncePkg?.nonce u.nonce i

val keylen   : #i:I.id -> u:info i -> U32.t

val statelen : #i:I.id -> u:info i -> U32.t

type cipher (i:I.id) (u:info i) (l:plainLenM u) =
  lbytes (l + (UInt32.v taglen))

type cipher32 (i:I.id) (l:U32.t{UInt.size (v l + 16) 32}) = lbytes32 (l +^ taglen)

//type nonce (i:I.id) = iv (I.cipherAlg_of_id i)

type adata = b:bytes{length b <= v aadmax}

type entry (i:I.id) (u:info i) =
  | Entry:
    n: nonce u ->
    ad: adata ->
    #l: plainLenM u ->
    p: plain u l ->
    c: cipher i u l ->
    entry i u


val aead_writer: i:I.id -> Type0
val aead_reader: #i:I.id -> w:aead_writer i -> Type0

val wgetinfo: #i:I.id -> aead_writer i -> Tot (info i)
val rgetinfo: #i:I.id -> #w:aead_writer i -> aead_reader w -> Tot (u:info i{u == wgetinfo w})


val wlog: #i:safeid -> w:aead_writer i -> mem -> GTot (Seq.seq (entry i (wgetinfo w)))

let rlog (#i:safeid) (#w: aead_writer i) (r:aead_reader w) (h:mem) =
  wlog w h

let address = nat

let addr_unused_in (rid:rid) (a:address) (m0:mem) =
  Monotonic.Heap.addr_unused_in a (Map.sel (HS.get_hmap m0) rid)

let contains_addr (rid:rid) (a:address) (m:mem) =
  ~(addr_unused_in rid a m)

let fresh_addresses (rid:rid) (addrs:Set.set address) (m0:mem) (m1:mem) =
  forall a. a `Set.mem` addrs ==>
       addr_unused_in rid a m0 /\
       contains_addr  rid a m1

(** Downward closure of [prf_region i] *)
val shared_footprint: rset

(** Downward closure of [log_region i] *)
val wfootprint: #i:I.id -> aead_writer i -> 
  GTot (s:rset{Set.disjoint s shared_footprint})

(* A reader never writes to the log_region, but may write to the prf_region *)
let rfootprint (#i:I.id) (#w:aead_writer i) (r:aead_reader w) : GTot rset =
  assume false;
  Set.singleton (wgetinfo w).prf_rgn
  

//  TSet.filter (fun (r:HS.rid) -> r == prf_region wr)
//                    (footprint wr)


//Leaving this abstract for now; but it should imply Crypto.AEAD.Invariant.safelen i len (otp_offset i)
val safelen: I.id -> nat -> GTot bool

let ok_plain_len_32 (i:I.id) = l:U32.t{safelen i (v l)}

val winvariant : #i:I.id -> aead_writer i -> mem -> Type0
//let rinvariant (#i:I.id) (#w:aead_writer i) (r:aead_reader w) (h:mem) =
//  winvariant w h

val wframe_invariant: #i:I.id -> w:aead_writer i -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
    (requires (winvariant w h0 /\
      modifies_one ri h0 h1 /\
      ~(Set.mem ri (wfootprint w)) /\
      ~(Set.mem ri shared_footprint)))
    (ensures winvariant w h1)

val frame_log: #i:I.id -> w:aead_writer i -> l:Seq.seq (entry i (wgetinfo w)) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
    (requires
      safeId i /\
      wlog w h0 == l /\
      modifies_one ri h0 h1 /\
      ~(Set.mem ri (wfootprint w)))
    (ensures wlog w h1 == l)

(*** The main stateful API ***)

(** Allocating a writer **)
val gen (i:I.id) (u:info i) : ST (aead_writer i)
  (requires (fun h -> disjoint u.prf_rgn u.log_rgn))
  (ensures  (fun h0 w h1 ->
    wgetinfo w == u /\
    modifies_none h0 h1 /\ // allocates only
    (exists fresh.
      fresh_addresses u.prf_rgn fresh h0 h1 /\
      wfootprint w == Set.singleton u.log_rgn /\
      shared_footprint == Set.singleton u.prf_rgn) /\
      (safeId i ==> wlog w h1 == Seq.empty) /\
        winvariant w h1
      ))

(** Building a reader from a writer **)


val genReader (#i: I.id) (w: aead_writer i) : ST (aead_reader w)
  (requires (fun h -> winvariant w h))
  (ensures  (fun h0 r h1 ->
    modifies Set.empty h0 h1 /\
    winvariant w h1)
  )

(*
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
    (* is_eternal_region (Buffer.frameOf cipher) /\ // why? *)
    (* is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\ //why? *)
    (* is_eternal_region (Buffer.frameOf aad) /\ //why? *)

let enc_dec_liveness (#i:_) (#rw:_) (st:aead_state i rw)
                     (#aadlen:nat) (aad: lbuffer aadlen)
                     (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                     (#cipherlen: nat) (cipher:lbuffer cipherlen) (h:mem) =
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
           (h: mem) : GTot (entry i) =
  let aad = Buffer.as_seq h aad in
  let p = Plain.sel_plain h plainlen plain in
  let c = Buffer.as_seq h cipher_tag in
  mk_entry n aad p c
*)

let nonce_filter (#i:I.id) (#w:aead_writer i) (n:nonce (wgetinfo w)) (e:entry i (wgetinfo w)) : bool =
  Entry?.n e = n

let wentry_for_nonce (#i:I.id) (w:aead_writer i) (n:nonce (wgetinfo w)) (h:mem)
  : Ghost (option (entry i (wgetinfo w))) (requires safeId i) (ensures fun _ -> True) =
  Seq.find_l (nonce_filter #i #w n) (wlog w h)

let fresh_nonce (#i:I.id) (w:aead_writer i) (n:nonce (wgetinfo w)) (h:mem)
  : Ghost bool (requires safeId i) (ensures fun _ -> True) =
  None? (wentry_for_nonce w n h)

(*let just_one_buffer (#a:Type) (b:Buffer.buffer a) : GTot fp =
   as_set [(Buffer.frameOf b, SomeRefs (as_set [Buffer.as_addr b]))]
*)

val encrypt
  (i: I.id)
  (w: aead_writer i)
  (n: nonce (wgetinfo w))
  (aad: adata)
  (l: plainLenM (wgetinfo w))
  (p: plain (wgetinfo w) l)
  : ST (cipher i (wgetinfo w) l)
  (requires (fun h0 ->
    winvariant w h0 /\
    (safeId i ==> fresh_nonce w n h0)))
  (ensures (fun h0 c h1 ->
    modifies (Set.union (wfootprint w) shared_footprint) h0 h1 /\
    winvariant w h1 /\
    (safeId i ==>
      wlog w h1 == Seq.snoc (wlog w h0) (Entry n aad p c))))

val decrypt
  (i: I.id)
  (#w: aead_writer i)
  (r: aead_reader w)
  (aad:adata)
  (n: nonce (rgetinfo r))
  (l:plainLenM (wgetinfo w))
  (c:cipher i (wgetinfo w) l)
  : ST (option (plain (rgetinfo r) l))
  (requires (fun h0 ->
    winvariant w h0))
  (ensures fun h0 res h1 ->
    winvariant w h1 /\
    modifies (Set.union (rfootprint r) shared_footprint) h0 h1 /\
    (safeId i ==>
      (match wentry_for_nonce w n h0 with
      | None -> None? res
      | Some (Entry _ aad' #l' p' c') ->
        (if aad' = aad && c' = c && l = l' then res = Some p'
        else None? res)
      )
    )
  )

