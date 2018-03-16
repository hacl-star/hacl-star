module Box.AE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open Crypto.Symmetric.Bytes
open Box.Plain

module ODH = Box.ODH
module KEY = Box.Key
module MR = FStar.Monotonic.RRef
module MM = FStar.Monotonic.Map


// Definition AE package
abstract noeq type encryption_scheme (key_length:nat) (nonce_length:nat) =
  | ES:
    gen: (unit -> lbytes key_length) ->
    enc: (n:lbytes nonce_length -> k:lbytes key_length -> p:bytes -> c:bytes) ->
    dec: (n:lbytes nonce_length -> k:lbytes key_length -> c:bytes -> option (p:bytes)) ->
    correctness: (n:lbytes nonce_length -> k:lbytes key_length -> p:bytes -> Lemma
    (requires True)
    (ensures (
      let dec_result = dec n k (enc n k p) in
      Some? dec_result
      /\ Some?.v dec_result == p
    ))
    ) ->
    encryption_scheme key_length nonce_length

abstract noeq type ae_parameters (pp:plain_package) =
  | GP:
    nonce_length:nat ->
    key_length:nat ->
    scheme: (encryption_scheme key_length nonce_length) ->
    b:bool{get_flag pp = b} ->
    ae_parameters pp

let nonce (#pp:plain_package) (ap:ae_parameters pp) = lbytes ap.nonce_length
let ciphertext = bytes

let message_log_key (#pp:plain_package) (ap:ae_parameters pp) = (nonce ap*ciphertext)
let message_log_value (#id:eqtype) (i:id) (pp:plain_package) = protected_plain pp i
let message_log_range (#pp:plain_package) (ap:ae_parameters pp) (#id:eqtype) (i:id) (k:message_log_key ap) = message_log_value i pp
let message_log_inv (#pp:plain_package) (ap:ae_parameters pp) (#id:eqtype) (i:id) (f:MM.map' (message_log_key ap) (message_log_range #pp ap i)) = True

let message_log (#pp:plain_package) (#id:eqtype) (rgn:MR.rid) (ap:ae_parameters pp) (i:id) =
  MM.t rgn (message_log_key ap) (message_log_range ap i) (message_log_inv ap i)


noeq abstract type ae_package (#pp:plain_package) (ap:ae_parameters pp) (#id:eqtype) (#i:id) (kp:KEY.key_package ap.key_length i) =
  | AE:
    rgn:MR.rid ->
    log:message_log rgn ap i ->
    ae_package ap #id #i kp

let zero_bytes (n:nat) = Seq.create n (UInt8.uint_to_t 0)

val encrypt: #id:eqtype -> #i:id -> #pp:plain_package -> #aparams:ae_parameters pp -> #kp:KEY.key_package aparams.key_length i -> ap:ae_package aparams kp -> n:nonce aparams -> p:protected_plain pp i -> ST ciphertext
  (requires (fun h0 ->
    (forall c . MM.fresh ap.log (n,c) h0)
  ))
  (ensures (fun h0 c h1 ->
    ((KEY.hon kp /\ aparams.b) ==>
      (c = aparams.scheme.enc n (KEY.get kp) (zero_bytes (length p))))
    /\ ((~(KEY.hon kp) \/ ~aparams.b) ==>
      (c = aparams.scheme.enc n (KEY.get kp) (repr #pp kp p)))
    /\ MR.witnessed (MM.contains ap.log (n,c) p)
    /\ modifies (Set.singleton ap.rgn) h0 h1
  ))
let encrypt #id #i #pp #aparams #kp ap n p =
  let k = KEY.get kp in
  let c =
    if KEY.hon kp && aparams.b then
      let p' = zero_bytes (length p) in
      aparams.scheme.enc n k p'
    else
      aparams.scheme.enc n k (repr #pp kp p)
  in
  MR.m_recall ap.log;
  MM.extend ap.log (n,c) p;
  c

val decrypt: #id:eqtype -> #i:id -> #pp:plain_package -> #aparams:ae_parameters pp -> #kp:KEY.key_package aparams.key_length i -> ap:ae_package aparams kp -> n:nonce aparams -> c:ciphertext -> ST (option (p:protected_plain pp i))
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 p h1 ->
    ((KEY.hon kp /\ aparams.b) ==>
      (match p with
       | Some p' -> MM.contains ap.log (n,c) p' h0
       | None -> MM.fresh ap.log (n,c) h0
      ))
    /\ ((~(KEY.hon kp) \/ ~aparams.b) ==>
      (match aparams.scheme.dec n (KEY.get kp) c with
       | Some p' -> Some? p /\ Some?.v p == coerce #pp kp p'
       | None -> None? p
      ))
    /\ h0 == h1
  ))
let decrypt #id #i #pp #aparams #kp ap n c =
  if KEY.hon kp && aparams.b then
    match MM.lookup ap.log (n,c) with
    | Some p -> Some p
    | None -> None
  else
    match aparams.scheme.dec n (KEY.get kp) c with
    | Some p -> Some (coerce #pp kp p)
    | None -> None
