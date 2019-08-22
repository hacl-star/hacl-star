module QuicCrypto

module G = FStar.Ghost
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack

open FStar.HyperStack
open FStar.HyperStack.ST

open EverCrypt.Helpers
open EverCrypt.Error

module M = LowStar.Modifies
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

#set-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1"

[@CAbstractStruct]
val state_s: Type0
let state = B.pointer state_s

val freeable_s: state_s -> Type0
let freeable (h:HS.mem) (p:state) =
  B.freeable p /\ freeable_s (B.deref h p)
let preserves_freeable (s:state) (h0 h1:HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

val footprint_s: state_s -> GTot B.loc
let footprint (m:HS.mem) (s:state) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

val inv_s: HS.mem -> state_s -> Type0
let inv (m:HS.mem) (s:state) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  inv_s m (B.get m s 0)

val inv_loc_in_footprint (s:state) (m:HS.mem)
  : Lemma (requires (inv m s))
  (ensures ((footprint m s) `M.loc_in` m))
  [SMTPat (inv m s)]

val frame_inv: l:B.loc -> s:state -> m0:HS.mem -> m1:HS.mem ->
  Lemma (requires inv m0 s /\ B.loc_disjoint l (footprint m0 s) /\ B.modifies l m0 m1)
  (ensures inv m1 s /\ footprint m0 s == footprint m1 s)

// Erased to unit when model is off
val id: eqtype
val safe: id -> Type
val is_safe: i:id ->
  ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> safe i))

val hash_of_id: id -> GTot SQ.ha
val aead_of_id: id -> GTot SQ.ea

type role =
| Client
| Server

type rw =
| Writer
| Reader

// pn s Writer returns the current writing packet number
// pn s Reader returns the highest packet number successfully decrypted
val pnT: state_s -> rw -> mem -> GTot nat
val pn: s:state -> rw:rw -> ST nat
  (requires fun h0 ->  B.live h0 s /\ inv h0 s)
  (ensures fun h0 ctr h1 -> h0 == h1 /\
    ctr == pnT (B.deref h0 s) rw h1)

noeq type info = {
  region: rid;
  ha: SHD.hash_alg;
  ea: SAEAD.alg;
}

type info0 (i:id) = a:info{hash_of_id i == a.ha /\ aead_of_id i == a.ea}

// Mchine integer version of the QUIC header types
type u1 = n:U8.t{n = 0z \/ n = 1z}
type u2 = n:U8.t{U8.v n < 4}
type u4 = n:U8.t{U8.v n < 16}
type u62 = n:UInt64.t{UInt64.v n < pow2 62}
let add3 (k:u4) : n:U8.t{U8.v n <= 18} = if k = 0uy then 0uy else U8.(k +^ 3uy)
type vlsize = n:U8.t{U8.v n == 1 \/ U8.v n == 2 \/ U8.v n == 4 \/ U8.v n == 8}

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

// Converts a concrete header into a spec equivalent
let spec_header (h:header) (m:HS.mem) : GTot SQ.header =
  match h with
  | Short spin phase cid_len cid ->
    SQ.Short (spin<>0uy) (phase<>0uy) (B.as_seq m cid)
  | Long typ version dcil scil dcid scid plain_len ->
    SQ.Long (U8.v typ) (U32.v version) (U8.v dcil) (U8.v scil)
    (B.as_seq m dcid) (B.as_seq m scid) (U32.v plain_len)

// Packets as recorded by the sender in the ideal log
type entry =
| Packet:
  pn_len: SQ.nat2 ->
  h: SQ.header ->
  p: SQ.pbytes ->
  entry

(*
Create a new packet encryption instance from a TLS traffic secret.
This will perform all the key derivations for the client and server key.

Note that QUIC will create 3 separate instances for the 0-RTT key,
the handshake encryption key, and the 1-RTT data key.
*)
val coerce:
  i: id -> // Erased
  a: info0 i ->
  dst: B.pointer (B.pointer_or_null state_s) ->
  secret: B.buffer U8.t {B.length secret = SHD.hash_length a.ha} ->
  ST error_code
    (requires fun h0 -> is_eternal_region a.region /\
      B.live h0 dst /\ B.live h0 secret)
    (ensures fun h0 e h1 ->
      match e with
      | Success ->
        let s = B.deref h1 dst in
	SQ.supported_hash a.ha /\
        not (B.g_is_null s) /\
	inv h1 s /\
        M.modifies (M.loc_buffer dst) h0 h1 /\
        M.fresh_loc (footprint h1 s) h0 h1 /\
        M.loc_region_only true a.region `M.loc_includes` footprint h1 s /\
	pnT (B.deref h1 s) Reader h1 == 0 /\
	pnT (B.deref h1 s) Writer h1 == 0 /\
        freeable h1 s
      | _ -> M.modifies M.loc_none h0 h1)

type long_packet_type =
  | Initial
  | EarlyData
  | Handshke
  | Retry


noeq type header =
  | Short:
    spin: U8.t ->
    phase: U8.t ->
    cid: B.buffer U8.t{
      let l = B.length cid in
      l == 0 \/ (4 <= l /\ l <= 18)} ->
    header
  | Long:
    typ: long_packet_type ->
    version: U32.t ->
    dcil: U8.t{U8.v dcil < pow2 4} ->
    scil: U8.t{U8.v scil < pow2 4} ->
    dcid: B.buffer U8.t{B.length dcid = SQ.add3 (U8.v dcil)} ->
    scid: B.buffer U8.t{B.length scid = SQ.add3 (U8.v scil)} ->
    plain_len: U32.t{U32.v plain_len <= SQ.max_plain_length} ->
    header

let spec_header (h:header) (m:mem) : GTot SQ.header =
  match h with
  | Short spin phase cid ->
    SQ.Short
      (spin=1z)
      (phase=1z)
      (LowStar.Buffer.as_seq m cid)
  | Long typ version dcil scil dcid scid len ->
    admit()

//val writer_log: s:state -> h:HS.mem -> GTot (S.seq (S.seq SQ.bytes))

(*

val encrypt:
  st: state ->
  
  

val decrypt:

val rekey:

val free:
*)
