module Crypto.AEAD.Main

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All
open FStar.UInt32
open Crypto.AEAD
module HS = FStar.HyperStack
module I = Crypto.Indexing
module PRF = Crypto.Symmetric.PRF

let keylen i = PRF.keylen i
let statelen i = PRF.statelen i
inline_for_extraction
let entry i = Invariant.aead_entry i
let mk_entry #i n ad #l p c = Invariant.AEADEntry n (FStar.Bytes.reveal ad) l p (FStar.Bytes.reveal c)
let entry_injective (#i:I.id)
                    (n:nonce i) (n':nonce i)
                    (ad:adata) (ad':adata)
                    (#l:Plain.plainLen) (#l':Plain.plainLen)
                    (p:Plain.plain i l) (p':Plain.plain i l')
                    (c:cipher i (Seq.length (Plain.as_bytes p))) (c':cipher i (Seq.length (Plain.as_bytes p')))
  : Lemma (let e  = mk_entry n ad p c in
           let e' = mk_entry n' ad' p' c' in
           (e == e' <==> (n == n' /\ ad == ad' /\ l == l' /\ p == p' /\ c == c')))
  = ()
let nonce_of_entry (#i:_) (e:entry i) = Crypto.AEAD.Invariant.AEADEntry?.nonce e

let aead_state i rw = Invariant.aead_state i rw
let log_region #i #rw st = Invariant.AEADState?.log_region st
let prf_region #i #rw st = Invariant.AEADState?.log_region st //TODO: FIXME!!

let log #i #rw s h =
  HS.sel h (Invariant.st_ilog s)

let fp' = FStar.Pointer.Base.loc
// inline_for_extraction let fp = FStar.Ghost.erased fp'
(* let footprint #i #rw s = TSet.empty //TODO: FIXME! *)
(* let hh_modifies_t (_:FStar.TSet.set HS.rid) (h0:HS.mem) (h1:HS.mem) = True //TODO: FIXME! *)
let footprint #i #rw s = FStar.Ghost.hide FStar.Pointer.Base.loc_none        //TODO: FIXME!
let modifies_fp (fp:fp) (h0:HS.mem) (h1:HS.mem): Type0 = True  //TODO: FIXME!
let preserves_fp (fp:fp) (h0:HS.mem) (h1:HS.mem) : Type0 = True //TODO: FIXME!

let safelen (i:I.id) (n:nat) = Invariant.safelen i n (Invariant.otp_offset i)
let invariant #i #rw s h = Invariant.inv s h
let frame_invariant #i #rw st h0 h1 = admit() //TODO: FIXME!

let gen i prf_rgn log_rgn =
    assume false;
    Crypto.AEAD.gen i log_rgn

let genReader #i st =
    assume false;
    Crypto.AEAD.genReader #i st

let coerce i rgn key =
    assume false;
    Crypto.AEAD.coerce i rgn key

let leak #i st
  = assume false;
    Crypto.AEAD.leak #i st


let encrypt i st n aadlen aad plainlen plain cipher_tag
  = assume false;
    Crypto.AEAD.encrypt i st n aadlen aad plainlen plain cipher_tag

let decrypt i st n aadlen aad plainlen plain cipher_tag
  = assume false;
    Crypto.AEAD.Decrypt.decrypt i st n aadlen aad plainlen plain cipher_tag
