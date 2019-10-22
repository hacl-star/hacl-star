module QUICStream
module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Plain = Crypto.Plain


open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


type prfid = Flag.prfid
type quicid = Flag.quicid

let safeId (i:I.id) = Flag.safeId i
let safePNE (j:prfid) = Flag.safePNE j
let safeQUIC (k:quicid) = Flag.safeQUIC k

type pnlen = nl:nat{nl >= 1 /\ nl <= 4}

type headerlen = hl:nat{hl >= 1 /\ hl <= pow2 32 - 1}

type quic_header (k:quicid) (hl:headerlen) =
  | Short_header: (b:lbytes hl) -> quic_header k hl
  | Long_header: (b:lbytes hl) -> quic_header k hl

let bytes_of_quic_header (#k:quicid) (#hl:headerlen) (hd:quic_header k hl) : lbytes hl =
  match hd with
    | Short_header b -> b
    | Long_header b -> b

let pne_plain (j:prfid) (l:PNE.pne_plainlen) : (t:Type0{hasEq t}) = lbytes l

let pne_as_bytes (j:prfid) (l:PNE.pne_plainlen) (n:pne_plain j l) : GTot (lbytes l) = n

let pne_repr (j:prfid {~ (safePNE j)}) (l:PNE.pne_plainlen) (n:pne_plain j l) :
  Tot (b:lbytes l{b == pne_as_bytes j l n}) = n

#reset-options "--z3rlimit 50"

let pne_plain_pkg = PNE.PNEPlainPkg pne_plain pne_as_bytes pne_repr

let samplelen = 16

type plainlen = l:nat{l + v AEAD.taglen <= pow2 32 - 1}

type pnplainlen = l:nat{l + v AEAD.taglen <= pow2 32 - 1 /\ l + v AEAD.taglen >= samplelen + 4}

type quic_protect (k:quicid) (l:pnplainlen) =
  lbytes (l + v AEAD.taglen) 

type quic_packet (k:quicid) (hl:headerlen) (l:pnplainlen{hl + l + v AEAD.taglen <= pow2 32 - 1}) =
  quic_header k hl * quic_protect k l

type cipher (i:I.id) (l:plainlen) = lbytes (l + v AEAD.taglen)

let max_ctr = pow2 62 - 1


(* plain pkg *)
val plain: i:I.id -> l:plainlen -> t:Type0{hasEq t}

val plain_as_bytes : i:I.id -> l:plainlen -> p:plain i l -> GTot (lbytes l)

val mk_plain: i:I.id -> l:plainlen -> b:lbytes l -> p:plain i l{~(AEAD.safeId i) ==> plain_as_bytes i l p == b}

val plain_repr : i:I.id{~(AEAD.safeId i)} -> l:plainlen -> p:plain i l -> b:lbytes l{b == plain_as_bytes i l p}

let aead_plain_pkg = AEAD.PlainPkg 0 plain plain_as_bytes plain_repr

type qiv (k:quicid) = AEAD.iv (I.cipherAlg_of_id (fst k))

(* nonce pkg *)

val nonce (i:I.id) : (t:Type0{hasEq t})

val nonce_as_bytes (i:I.id) (n:nonce i) : GTot (AEAD.iv (I.cipherAlg_of_id i))

val nonce_repr (i:I.id{~(safeId i)}) (n:nonce i) :
  Tot (b:AEAD.iv (I.cipherAlg_of_id i){b == nonce_as_bytes i n})

let aead_nonce_pkg =
  AEAD.NoncePkg nonce nonce_as_bytes nonce_repr


type sample = PNE.sample

type epn (nl:pnlen) = lbytes nl

type rpn = n:U64.t{U64.v n <= max_ctr}

let rpn_of_nat (j:nat{j<= max_ctr}) : rpn =
  U64.uint_to_t j

type npn (j:prfid) (nl:pnlen) = lbytes nl

//get the first byte of the (unprotected) header + the pn = what needs to be protected by pne
val pne_plain_of_header_pn (#k:quicid) (#hl:headerlen) (hd:quic_header k hl) (#nl:pnlen) (n:npn (snd k) nl) :  pne_plain (snd k) (nl+1)

//reconstruct the unprotected header (using the protected header), and the pn, from the protected header and pn
val header_pn_of_pne_plain (#k:quicid) (#hl:headerlen) (ph:quic_header k hl) (#ll:PNE.pne_plainlen) (pp:pne_plain (snd k) ll) : quic_header k hl * npn (snd k) (ll-1)

//val pheader_epn_of_pne_cipher (#k:quicid) (#hl:headerlen) (hd:quic_header k hl) (l:PNE.pne_plainlen) (c:PNE.pne_cipher l) : quic_header k hl * (nl:pnlen & epn nl)

//get the protected first byte from the (protected) header + the epn = a cipher for pne
val pne_cipher_of_pheader_epn (#k:quicid) (#hl:headerlen) (ph:quic_header k hl) (#nl:pnlen) (ne:epn nl) :
  c:PNE.pne_cipher (nl + 1)

//get the pne ciphertext assuming the largest possible pn length (ie 4)
val pne_cipherpad_of_pheader_quicprotect (#k:quicid) (#hl:headerlen) (ph:quic_header k hl) (#nll:pnplainlen) (qp:quic_protect k nll) :
  c:PNE.pne_cipherpad

val npn_encode : (j:prfid) -> (r:rpn) -> (nl:pnlen) -> (n:npn j nl)

val npn_decode : (#j:prfid) -> (#nl:pnlen) -> (n:npn j nl) -> (expected_pn:rpn) -> rpn

val create_nonce : #i:I.id -> #alg:I.cipherAlg{alg == I.cipherAlg_of_id i} ->
  iv: AEAD.iv alg -> r:rpn -> Tot (nonce i)


val stream_writer: (k:quicid) -> Type0
val stream_reader: #k:quicid -> w:stream_writer k -> Type0

val writer_aead_state : (#k:quicid) -> (w:stream_writer k) ->
  aw:AEAD.aead_writer (fst k)
  {(AEAD.wgetinfo aw).AEAD.plain == aead_plain_pkg /\
  (AEAD.wgetinfo aw).AEAD.nonce == aead_nonce_pkg} 
val reader_aead_state : #k:quicid -> #w:stream_writer k -> r:stream_reader w ->
  ar:AEAD.aead_reader (writer_aead_state w)
  {(AEAD.rgetinfo ar).AEAD.plain == aead_plain_pkg /\
  (AEAD.rgetinfo ar).AEAD.nonce == aead_nonce_pkg} 

val writer_pne_state : #k:quicid -> w:stream_writer k -> PNE.pne_state (snd k) pne_plain_pkg
val reader_pne_state : #k:quicid -> #w:stream_writer k -> r:stream_reader w -> PNE.pne_state (snd k) pne_plain_pkg

val invariant: #k:quicid -> w:stream_writer k -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 
val rinvariant: #k:quicid -> #w:stream_writer k -> r:stream_reader w -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 

val wctrT: #k:quicid -> w:stream_writer k -> mem -> GTot (n:nat{n<=max_ctr})
val wctr: #k:quicid -> w:stream_writer k -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt64.v c = wctrT w h1)

val writer_iv: #k:quicid -> w:stream_writer k -> qiv k
val reader_iv: #k:quicid -> #w:stream_writer k -> r:stream_reader w ->
  iv:qiv k{iv = writer_iv w}

val expected_pnT: #k:quicid -> #w:stream_writer k -> r:stream_reader w -> h:mem ->
  GTot rpn
val expected_pn: #k:quicid -> #w:stream_writer k -> r:stream_reader w -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\
    (c == expected_pnT #k #w r h0))


let wincrementable (#k:quicid) (w:stream_writer k) (h:mem) =
  wctrT w h < max_ctr



type info' = {
  alg: I.aeadAlg;
  shared: subrgn tls_tables_region;
  local: subrgn tls_tables_region;
  parent: subrgn tls_tables_region;
}

type info (k:quicid) =
  info:info'{I.aeadAlg_of_id (fst k) == info.alg}

val shared_footprint: #k:quicid -> w:stream_writer k -> GTot rset

val footprint: #k:quicid -> w:stream_writer k -> GTot (s:rset{Set.disjoint s (shared_footprint w)})

let rshared_footprint (#k:quicid) (#w:stream_writer k) (r:stream_reader w): GTot rset =
  shared_footprint w

val rfootprint: #k:quicid -> #w:stream_writer k -> r:stream_reader w -> GTot (s:rset{Set.disjoint s (rshared_footprint r)})
 

val frame_invariant: #k:quicid -> w:stream_writer k -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w))))
  (ensures invariant w h1)

val rframe_invariant: #k:quicid -> #w:stream_writer k -> r:stream_reader w -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (rinvariant r h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r))) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures rinvariant r h1)


val wframe_log: #k:quicid{safeId (fst k)} -> w:stream_writer k -> l:Seq.seq (AEAD.entry (fst k) (AEAD.wgetinfo (writer_aead_state w))) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    invariant w h0 /\
    AEAD.wlog (writer_aead_state w) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures invariant w h1 ==> AEAD.wlog (writer_aead_state w) h1 == l)

val rframe_log: #k:quicid{safeId (fst k)} -> #w:stream_writer k -> r:stream_reader w -> l:Seq.seq (AEAD.entry (fst k) (AEAD.rgetinfo (reader_aead_state r))) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    invariant w h0 /\
    AEAD.rlog (reader_aead_state r) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures invariant w h1 ==> AEAD.rlog (reader_aead_state r) h1 == l)


val wframe_pnlog: #k:quicid -> w:stream_writer k -> l:Seq.seq (PNE.entry (snd k) pne_plain_pkg) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    safePNE (snd k) /\
    PNE.table (writer_pne_state w) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures PNE.table (writer_pne_state w) h1 == l)

val rframe_pnlog: #k:quicid ->  #w:stream_writer k -> r:stream_reader w -> l:Seq.seq (PNE.entry (snd k) pne_plain_pkg) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    safePNE (snd k) /\
    PNE.table (reader_pne_state r) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures PNE.table (reader_pne_state r) h1 == l)


val create: k:quicid -> u:info k ->
  ST (stream_writer k)
  (requires fun h0 -> 
    disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1 /\
    (safeId (fst k) /\ safePNE (snd k)) ==>
    (AEAD.wlog (writer_aead_state w) h1 == Seq.empty /\
    PNE.table (writer_pne_state w) h1 == Seq.empty /\
    wctrT w h1 == 0)
  )

(*val coerce: i:I.id -> u:info i ->
  ST (stream_writer i)
  (requires fun h0 -> 
    ~ (Flag.safeId i) /\ disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
    footprint w == Set.singleton u.local /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1)
*)

val createReader: parent:rgn -> #k:quicid -> w:stream_writer k ->
  ST (stream_reader w)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant w h1 /\
    rinvariant r h1 /\
    modifies_none h0 h1 /\
    (safeId (fst k) /\ safePNE (snd k)) ==>
      expected_pnT r h1 == U64.uint_to_t 0)

//split the epn+cipher, given the length of the epn
val split (#k:quicid) (#l:pnplainlen) (nec:quic_protect k l) (nl:pnlen) :
  epn nl * cipher (fst k) (l-nl) 

val sample_quic_protect (#k:quicid) (#l:pnplainlen) (nec:quic_protect k l) : PNE.sample

#reset-options "--z3rlimit 50"


val encrypt
  (#k:quicid)
  (w:stream_writer k)
  (#hl:headerlen)
  (hd:quic_header k hl)
  (nl:pnlen {hl + nl <= v AEAD.aadmax})
  (#l:plainlen {hl + nl + l + v AEAD.taglen <= pow2 32 - 1 /\
    nl + l + v AEAD.taglen >= samplelen + 4})
  (p:plain (fst k) l):
  ST (quic_packet k hl (nl + l))
  (requires fun h0 ->
    wincrementable w h0 /\
    invariant w h0)
  (ensures fun h0 (ph,nec) h1 ->
    let (i,j) = k in
    let aw = writer_aead_state w in
    let ps = writer_pne_state w in
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    (safeQUIC k ==> (
      let (ne,c) = split #k #(nl+l) nec nl in
      let rpn = rpn_of_nat (wctrT w h0) in
      let npn = npn_encode j rpn nl in
      let alg = I.cipherAlg_of_aeadAlg ((AEAD.wgetinfo aw).AEAD.alg) in
      let nce:AEAD.nonce (AEAD.wgetinfo aw) = create_nonce #i #alg (writer_iv w) rpn in
      let ad:AEAD.adata = Bytes.append (bytes_of_quic_header hd) npn in
      let s:PNE.sample = sample_quic_protect nec in
      let nn = pne_plain_of_header_pn hd npn in
      let cc = pne_cipher_of_pheader_epn ph ne in 
      AEAD.wlog aw h1 ==
        Seq.snoc
          (AEAD.wlog aw h0)
          (AEAD.Entry #i #(AEAD.wgetinfo aw) nce ad #l p c) /\
           PNE.table ps h1 ==
              Seq.snoc
                (PNE.table ps h0)
                (PNE.Entry #j #pne_plain_pkg s #(nl+1) nn cc))) /\
    modifies (Set.union (footprint w) (shared_footprint w)) h0 h1)



val decrypt
  (#k:quicid)
  (#w:stream_writer k)
  (r:stream_reader w)
  (#hl:headerlen {hl+5 <= v AEAD.aadmax})
  (#nll:pnplainlen{hl + nll + v AEAD.taglen <= pow2 32 - 1})
  (qp:quic_packet k hl nll) :
  ST (option (l:plainlen & plain (fst k) l))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    let (i,j) = k in
    let ar = reader_aead_state r in
    let aw = writer_aead_state w in
    let ps = reader_pne_state r in
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (None? res ==> expected_pnT r h1 == expected_pnT r h0) /\
    (safeQUIC k ==>
      (let (ph,nec) = qp in
      let s = sample_quic_protect nec in
      let cp = pne_cipherpad_of_pheader_quicprotect ph nec in
      match PNE.entry_for_sample_cipherpad s cp ps h0 with
        | None -> None? res
        | Some (PNE.Entry  _ #ll n cc) ->
          let nl:pnlen = ll - 1 in
          let (hd,npn) = header_pn_of_pne_plain #k #hl ph #ll n in 
	  let rpn = npn_decode #j #nl npn (expected_pnT r h0) in
          let alg = I.cipherAlg_of_aeadAlg ((AEAD.rgetinfo ar).AEAD.alg) in
          let n = create_nonce #i #alg (reader_iv r) rpn in
          let ad:AEAD.adata = Bytes.append (bytes_of_quic_header hd) npn in
          match AEAD.wentry_for_nonce aw n h0 with
	    | None -> None? res
	    | Some (AEAD.Entry _  ad' #l' p' c')  -> 
	      if ad' = ad && l' = nll - nl && snd (split nec nl) = c' then 
	        (res = Some (|l',p'|) /\
                  (if U64.v rpn >= U64.v (expected_pnT r h0) && U64.v rpn < max_ctr then
                    expected_pnT r h1 = rpn_of_nat (U64.v rpn + 1)
                  else
                    expected_pnT r h1 = expected_pnT r h0))                  
	        else None? res
      )
    )
  )

(*)


 (*   (None? res ==> pnlog r h1 == pnlog r h0) /\    
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      match (Seq.find_l (epn_filter i j nl ne) lg) with
        | None -> res = None
        | Some (Entry _ rpn ad' #l' p _ c') ->
	  let npn = npn_encode j rpn nl in
          if (ad' = ad && l' = l && c' = c then
              (res = Some p /\ pnlog r h1 == Seq.snoc (pnlog r h0) rpn)
          else
            res = None)))
*)
(*
  (Flag.safePNE j ==>
    match entry_for_ne r ne h0 with
    | None -> None? res
    | Some (Entry nl' rpn' ad' l' p' _ c') ->
      if c' = c then
        let npn = 
      else None? res
  | Entry:
    nl:pnlen ->
    pn:rpn ->
    ad:AEAD.adata ->
    #l:plainlen ->
    p:plain i l ->
    ne:epn nl ->
    c:cipher i l ->
    stream_entry i j
*)
(*)
    (Flag.safePNE j ==>
      let s = PNE.sample_cipher c in
      match PNE.entry_for_sample s (pne_state r) h0 with
      | None -> None? res
      | Some (Entry _ nl' ne' npn) ->
        if nl = nl' && ne = ne' then
	  let rpn = npn_decode #nl npn (highest_pn_or_zero r h0) in
	  let n = encode_nonce rpn nl static_iv in
	  match AEAD.entry_for_nonce (aead_state r) n h0 with
	  | None -> None? res
	  | Some (_, ad', l', p', c')  ->
	    if ad' = empty_bytes && l' = l && c' = c then
	      res = Some p'
	    else None? res
	else None? res

(*      let npn = 'find nl ne in pnetable' in
      let rpn = 'decode npn maxpn' in
      match 'find rpn in enctable' with
        ne' -> ne' =? ne

      let rpn = 'find nl ne in enctable' in
        rpn =? decode (encode rpn nl) maxpn
*)

(*
N(nl, rpn) = encode(nl)<<62 + rpn

N(nl1, rpn1) = N(nl2, rpn2) ==> nl1 = nl2 /\ rpn1 = rpn2

decode(npn, nl, highest_pn) = (highest_pn & ~nl) | npn

y-2^(8*len(x)-1) < decode x y < y + 2^(8*len(x)-1)
