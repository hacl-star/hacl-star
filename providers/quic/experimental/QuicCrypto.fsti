module QuicCrypto

module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

module H = EverCrypt.Hash
module HKDF = EverCrypt.HKDF
module AEAD = EverCrypt.AEAD
module C = EverCrypt.Cipher

module SAEAD = Spec.AEAD
module SH = Spec.Hash
module SHD = Spec.Hash.Definitions
module SQ = Spec.QUIC

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U8 = FStar.UInt8

(*
This file defines the interface for the packet stream encryption
functionality. It provides functional correctness with respect
to the spec in Spec.QUIC of single packet encryption, automatic
management of the packet stream (using a counter for sending packets
and a reference to the highest packet number successfully decrypted
sequence number for incoming packets), and cryptographic security
of the stream of packets.
*)

#set-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1"

// Controls erasure of ideal state
val model: bool

// Crypto index, erased to unit when model is off
val id: eqtype

// Controls the idealization, false when model is off
// Internally, safe is defined as honest /\ ideal
// we assume that honesty is implicit in this interface
// (i.e. we idealize everything that can be)
val safe: id -> t:Type{t ==> model}
val is_safe: i:id -> ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> safe i))

val defined: id -> Type
val fresh: id -> mem -> Type
val is_fresh: i:id -> ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> if b then defined i else fresh i h1)

// Location for the shared, global ideal state
val global_loc: B.loc

// State of the packet encryption stream functionality
[@CAbstractStruct]
val state_s: id -> Type0
let state (i:id) = B.pointer (state_s i)

val freeable_s: #i:id -> state_s i -> Type0
let freeable (#i:id) (h:HS.mem) (p:state i) =
  B.freeable p /\ freeable_s (B.deref h p)
let preserves_freeable (#i:id) (s:state i) (h0 h1:HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

// Local footprint of an instance, excludes shared global state
val footprint_s: #i:id -> state_s i -> GTot B.loc
let footprint (#i:id) (s:state i) (m:HS.mem) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

val inv_s: #i:id -> state_s i -> HS.mem -> Type0
let inv (#i:id) (s:state i) (m:HS.mem) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  inv_s (B.get m s 0) m

val inv_loc_in_footprint (#i:id) (s:state i) (m:HS.mem)
  : Lemma (requires (inv s m))
  (ensures ((footprint s m) `B.loc_in` m))
  [SMTPat (inv s m)]

val frame_inv: #i:id -> s:state i -> m0:HS.mem -> l:B.loc -> m1:HS.mem ->
  Lemma (requires inv s m0 /\ B.loc_disjoint l (footprint s m0) /\ B.modifies l m0 m1)
  (ensures inv s m1 /\ footprint s m0 == footprint s m1)

// Ghost access to the index algorithms (when model is on)
val hash_of_id: id -> Ghost SQ.ha (requires model) (ensures fun _ -> True)
val aead_of_id: id -> Ghost SQ.ea (requires model) (ensures fun _ -> True)

// Concrete partof the index (agility parameters)
noeq type info = {
  region: rid;
  ha: SQ.ha;
  ea: SQ.ea;
}

// Additionaly, the concrete info must be consistent with crypto index
type info0 (i:id) = a:info{model ==> (hash_of_id i == a.ha /\ aead_of_id i == a.ea)}

type role =
| Client
| Server

type rw =
| Writer
| Reader

// Mchine integer version of the QUIC header types
type u1 = n:U8.t{n = 0z \/ n = 1z}
type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}
let add3 (k:u4) : n:U8.t{U8.v n <= 18} = if k = 0uy then 0uy else U8.(k +^ 3uy)
type vlsize = n:U8.t{U8.v n == 1 \/ U8.v n == 2 \/ U8.v n == 4 \/ U8.v n == 8}

// New streams use the same packet number space in QUIC,
// we record the initial packet number of the stream and
// use it as an offset in the packet stream
val initial_pn: #i:id -> state i -> mem -> GTot SQ.nat62
val lemma_initial_pn_constant:
  #i:id -> s:state i -> h0:mem -> h1: mem -> Lemma
  (requires inv s h0 /\ inv s h1)
  (ensures initial_pn s h0 == initial_pn s h1)

// pn s Writer returns the current writing packet number
// pn s Reader returns the highest packet number successfully decrypted
val pnT: #i:id -> s:state i -> rw -> h:mem -> Ghost SQ.nat62 (requires True)
  (ensures fun pn -> pn >= initial_pn s h)
val pn: #i:id -> s:state i -> rw:rw -> ST u62
  (requires fun h0 ->  B.live h0 s /\ inv s h0)
  (ensures fun h0 ctr h1 -> h0 == h1 /\ U64.v ctr == pnT s rw h1)

let incrementable (#i:id) (s:state i) (h:mem) =
  pnT s Writer h + 1 < pow2 62

// Information stored in a QUIC header
noeq type header =
  | Short:
    spin: u1 ->
    phase: u1 ->
    cid_len: U8.t{let l = U8.v cid_len in l == 0 \/ (4 <= l /\ l <= 18)} ->
    cid: B.lbuffer U8.t (U8.v cid_len) ->
    header
  | Long:
    typ: u2 ->
    version: U32.t ->
    dcil: u4 ->
    scil: u4 ->
    dcid: B.lbuffer U8.t (U8.v (add3 dcil)) ->
    scid: B.lbuffer U8.t (U8.v (add3 scil)) ->
    plain_len: U32.t{U32.v plain_len < SQ.max_cipher_length} ->
    header

let live_header (h:header) (m:mem) =
  match h with
  | Short _ _ _ cid -> m `B.live` cid
  | Long _ _ _ _ dcid scid _ -> m `B.live` dcid /\ m `B.live` scid

// Converts a concrete header into a spec equivalent
let spec_header (h:header) (m:HS.mem) : GTot SQ.header =
  match h with
  | Short spin phase cid_len cid ->
    SQ.Short (spin<>0uy) (phase<>0uy) (B.as_seq m cid)
  | Long typ version dcil scil dcid scid plain_len ->
    SQ.Long (U8.v typ) (U32.v version) (U8.v dcil) (U8.v scil)
    (B.as_seq m dcid) (B.as_seq m scid) (U32.v plain_len)

// Packets as recorded by the sender in the ideal log
type entry (i:id) =
| Packet:
  pn_len: SQ.nat2 ->
  header: SQ.header ->
  plain: SQ.pbytes ->
  packet: SQ.packet ->
  entry i

// Idealization relies on a global table of ideal state
// (included in the footprint of every instance)
val itable: i:id -> h:mem -> GTot (S.seq (entry i))

// Part of the invariant, the size of the log at index i
// is related to the counter state of any instance at index i
val lemma_itable_length:
  #i:id ->
  s:state i->
  h:mem -> Lemma
  (requires inv s h)
  (ensures S.length (itable i h) == pnT s Writer h - initial_pn s h)

val lemma_itable_frame: i:id -> h0:mem -> l:B.loc -> h1:mem ->
  Lemma (requires B.modifies l h0 h1 /\ B.loc_disjoint l global_loc)
  (ensures itable i h0 == itable i h1)
let modifies_itable (i:id) (h0:mem) (h1:mem) =
  (forall (j:id{i <> j}). itable j h0 == itable j h1)

(*
Create a new packet encryption instance from a TLS traffic secret.
This will perform all the key derivations for the client and server key.
Note that QUIC will create 3 separate instances for the 0-RTT key,
the handshake encryption key, and the 1-RTT data key.
*)
val coerce:
  i: id -> // Erased
  a: info0 i ->
  initial_pn: u62 ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  secret: B.buffer U8.t {B.length secret = SHD.hash_length a.ha} ->
  ST error_code
    (requires fun h0 -> ~(safe i) /\
      B.g_is_null (B.deref h0 dst) /\
      is_eternal_region a.region /\
      SQ.keysized a.ha (B.length secret) /\
      B.live h0 dst /\ B.live h0 secret)
    (ensures fun h0 e h1 ->
      match e with
      | Success ->
        let s = B.deref h1 dst in
        SQ.supported_hash a.ha /\
        not (B.g_is_null s) /\
        inv s h1 /\
        B.modifies (B.loc_buffer dst) h0 h1 /\
        B.fresh_loc (footprint s h1) h0 h1 /\
        B.loc_region_only true a.region `B.loc_includes` footprint s h1 /\
        pnT s Reader h1 == U64.v initial_pn /\
        pnT s Writer h1 == U64.v initial_pn /\
        freeable h1 s
      | _ -> B.modifies B.loc_none h0 h1)

val create:
  i: id -> // Erased
  a: info0 i ->
  initial_pn: u62 ->
  dst: B.pointer (B.pointer_or_null (state_s i)) ->
  ST error_code
    (requires fun h0 -> safe i /\
      B.g_is_null (B.deref h0 dst) /\
      is_eternal_region a.region /\
      B.live h0 dst)
    (ensures fun h0 e h1 ->
      match e with
      | Success ->
        let s = B.deref h1 dst in
        SQ.supported_hash a.ha /\
        not (B.g_is_null s) /\
        inv s h1 /\
        B.modifies (B.loc_buffer dst) h0 h1 /\
        B.fresh_loc (footprint s h1) h0 h1 /\
        B.loc_region_only true a.region `B.loc_includes` footprint s h1 /\
        pnT s Reader h1 == U64.v initial_pn /\
        pnT s Writer h1 == U64.v initial_pn /\
        itable i h1 == S.empty /\
        freeable h1 s
      | _ -> B.modifies B.loc_none h0 h1)

val infoT: #i:id -> s:state i -> h:mem -> GTot (info0 i)
val get_info: #i:id -> s:state i -> ST (info0 i)
  (requires fun h0 -> inv s h0) (ensures fun h0 a h1 -> h0 == h1 /\ a == infoT s h0)

val leakT: #i:id -> s:state i -> h:mem ->
  Ghost (SQ.lbytes (SHD.hash_length (infoT s h).ha)) 
  (requires inv s h /\ ~(safe i))
  (ensures fun b -> SQ.keysized (infoT s h).ha (S.length b))

let if_safe (i:id) (t:Type) (f:Type) =
  (safe i ==> t) /\ (~(safe i) ==> f)

(* QUIC HKDF labels, move to Spec.QUIC? *)
val label_key : SQ.lbytes 3
val label_iv : SQ.lbytes 2
val label_hp : SQ.lbytes 2

val encrypt:
  #i:id -> // Erased
  s: state i ->
  h: header ->
  plain_len: U32.t{3 <= U32.v plain_len /\ U32.v plain_len < SQ.max_plain_length} ->
  plain: B.lbuffer U8.t (U32.v plain_len) ->
  pn_len: u2 ->
  out: B.buffer U8.t ->
  ST error_code
  (requires fun h0 -> B.live h0 plain /\ B.live h0 out /\
    inv s h0 /\ live_header h h0 /\ incrementable s h0 /\
    (let clen = U32.v plain_len + SAEAD.tag_length (infoT s h0).ea in
    let len = clen + SQ.header_len (spec_header h h0) (U8.v pn_len) in
    (Long? h ==> U32.v (Long?.plain_len h) = clen) /\
    B.length out == len))
  (ensures fun h0 r h1 ->
    let fp = B.loc_union (B.loc_buffer out)
      (B.loc_union global_loc (footprint s h0)) in
    B.modifies fp h0 h1 /\
    modifies_itable i h0 h1 /\
    (match r with
    | Success ->
      inv s h1 /\
      pnT s Writer h1 == pnT s Writer h0 + 1 /\
      (safe i ==>
       begin (* Ideal case *)
        let log0 = itable i h0 in
        let log1 = itable i h1 in
        log1 == S.append log0
          (S.create 1 (Packet (U8.v pn_len) (spec_header h h0)
            (B.as_seq h0 plain) (B.as_seq h1 out)))
       end) /\
      ~(safe i) ==>
       begin (* Concrete case *)
        let a = infoT s h0 in
        let s0 = leakT s h0 in
        let k = SQ.derive_secret a.ha s0 label_key (SAEAD.key_length a.ea) in
        let iv = SQ.derive_secret a.ha s0 label_iv 12 in
        let pne = SQ.derive_secret a.ha s0 label_hp (SQ.ae_keysize a.ea) in
        let plain : SQ.pbytes = B.as_seq h0 plain in
        let packet : SQ.packet = B.as_seq h1 out in
        let ctr = pnT s Writer h0 in
        packet == SQ.encrypt a.ea k iv pne (U8.v pn_len) ctr (spec_header h h0) plain
       end
    | _ -> True))

noeq type result = {
  pn_len: u2;
  pn: u62;
  plain_len: n:U32.t{let l = U32.v n in 3 <= l /\ l < SQ.max_plain_length};
  plain: B.buffer U8.t;
}

let max (x y: nat) = if x >= y then x else y

val decrypt:
  #i:id -> // Erased
  s: state i ->
  len: U32.t{21 <= U32.v len /\ U32.v len < pow2 32} ->
  packet: B.lbuffer U8.t (U32.v len) ->
  cid_len: u4 ->
  header: B.pointer header ->
  out: B.pointer result ->
  ST error_code
  (requires fun h0 -> B.live h0 packet /\ B.live h0 header /\ B.live h0 out /\
    inv s h0 /\ (Long? (B.deref h0 header) ==> cid_len = 0z))
  (ensures fun h0 r h1 ->
    B.modifies (B.loc_union (footprint s h0)
      (B.loc_buffer header `B.loc_union` B.loc_buffer out)) h0 h1 /\
    (match r with
    | Success ->
      let o = B.deref h1 out in
      let h = B.deref h1 header in
      let pn = U64.v o.pn in
      let last = pnT s Reader h0 in
      inv s h1 /\ pn >= initial_pn s h0 /\
      pnT s Reader h1 == max (pnT s Reader h0) (U64.v o.pn) /\
      B.length o.plain == U32.v o.plain_len /\
      (safe i ==>
       begin (* Ideal case *)
        let log0 = itable i h0 in
        let log1 = itable i h1 in
        log0 == log1 /\
        pn - initial_pn s h0 < S.length log0 /\
        S.index log0 (pn - initial_pn s h0) ==
          (Packet (U8.v o.pn_len) (spec_header h h1)
            (B.as_seq h0 o.plain) (B.as_seq h0 packet))
       end) /\
      ~(safe i) ==>
       begin (* Concrete case *)
        let a = infoT s h0 in
        let s0 = leakT s h0 in

        let k = SQ.derive_secret a.ha s0 label_key (SAEAD.key_length a.ea) in
        let iv = SQ.derive_secret a.ha s0 label_iv 12 in
        let pne = SQ.derive_secret a.ha s0 label_hp (SQ.ae_keysize a.ea) in
        let plain : SQ.pbytes = B.as_seq h0 o.plain in
        let packet : SQ.packet = B.as_seq h0 packet in
        let last = pnT s Reader h0 in
        SQ.decrypt a.ea k iv pne last (U8.v cid_len) packet
          == SQ.Success (U8.v o.pn_len) (U64.v o.pn) (spec_header h h1) plain
       end
    | _ -> True))

