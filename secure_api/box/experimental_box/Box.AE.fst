module Box.AE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain

module KEY = Box.Key
module MM = FStar.Monotonic.Map

// KEY Package definition

assume val random_bytes: n:(n:nat{n<=32}) -> lbytes n

noeq abstract type key (key_length:(n:nat{n<=32}))(#id:eqtype) (i:id) =
     | Key:
       raw: lbytes key_length ->
       h:bool ->
       key key_length #id i

val hon: #id:eqtype -> #key_length:(n:nat{n<=32}) -> #i:id -> k:key key_length i -> b:bool{b = k.h}
let hon #id #i #kl k =
 k.h

val get: #id:eqtype -> #key_length:(n:nat{n<=32}) -> #i:id -> k:key key_length i{hon k = false} -> raw:lbytes key_length{raw = k.raw}
let get #id #i #kl k =
 k.raw

val gen: #id:eqtype -> key_length:(n:nat{n<=32}) -> i:id -> k:key key_length i
let gen #id key_length i =
 Key (random_bytes key_length) true

val set: #id:eqtype -> #key_length:(n:nat{n<=32}) -> i:id -> lbytes key_length -> k:key key_length i
let set #id #key_length i raw =
  Key raw false

val get_ae_key_package: id:eqtype -> key_length:(n:nat{n<=32}) -> KEY.key_package #id key_length (key key_length #id)
let get_ae_key_package id key_length =
  KEY.KP (hon #id #key_length) (get #id #key_length) (gen key_length) set


// Definition AE package
noeq type encryption_scheme (key_length:(n:nat{n<=32})) (nonce_length:(n:nat{n<=32})) =
  | ES:
    gen: (unit -> lbytes key_length) ->
    enc: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> c:bytes) ->
    dec: (c:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> option (p:bytes)) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
//    ) ->
    encryption_scheme key_length nonce_length

abstract noeq type ae_parameters (#id:eqtype) (#key_length:(n:nat{n<=32})) (kp:KEY.key_package #id key_length (key key_length #id)) (pp:plain_package) =
  | GP:
    nonce_length:(n:nat{n<=32}) ->
    scheme: (encryption_scheme key_length nonce_length) ->
    b:bool{get_flag pp = b} ->
    ae_parameters #id #key_length kp pp

//let nonce (#id:eqtype) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id #key_length key) (#pp:plain_package) (ap:ae_parameters kp pp) = lbytes ap.nonce_length
let nonce (nl:(n:nat{n<=32})) = lbytes nl
let ciphertext = bytes

let message_log_key (nonce_length:(n:nat{n<=32})) = (nonce nonce_length*ciphertext)
let message_log_value (#id:eqtype) (i:id) (pp:plain_package) = protected_plain pp i
let message_log_range (#id:eqtype) (i:id) (pp:plain_package) (nonce_length:(n:nat{n<=32})) (k:message_log_key nonce_length) = message_log_value i pp
let message_log_inv (#pp:plain_package) (#nonce_length:(n:nat{n<=32})) (#id:eqtype) (i:id) (f:MM.map' (message_log_key nonce_length) (message_log_range i pp nonce_length)) = True

let message_log (#pp:plain_package) (#id:eqtype) (rgn:erid) (nonce_length:(n:nat{n<=32})) (i:id) =
  MM.t rgn (message_log_key nonce_length) (message_log_range i pp nonce_length) (message_log_inv i)

noeq abstract type ae_package (#pp:plain_package) (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (ap:ae_parameters kp pp) =
  | AE:
    rgn:erid ->
    log:message_log #pp #id rgn ap.nonce_length i ->
    ae_package #pp #id #i #key_length #kp ap

let zero_bytes (n) : bytes = Seq.create n (UInt8.uint_to_t 0)

val encrypt: #id:eqtype -> #i:id -> #pp:plain_package -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package #id key_length (key key_length #id) -> #aparams:ae_parameters kp pp ->  ap:ae_package #pp #id #i aparams -> k:key key_length i -> n:nonce aparams.nonce_length -> p:protected_plain pp i -> ST ciphertext
  (requires (fun h0 ->
    (forall c . MM.fresh ap.log (n,c) h0)
  ))
  (ensures (fun h0 c h1 ->
    ((KEY.(kp.hon k) /\ aparams.b) ==>
      (c = aparams.scheme.enc (zero_bytes (length p)) k.raw n))
    /\ ((~(KEY.(kp.hon k)) \/ ~aparams.b) ==>
      (c = aparams.scheme.enc (repr #pp kp k p) k.raw n))
    /\ witnessed (MM.contains ap.log (n,c) p)
    /\ modifies (Set.singleton ap.rgn) h0 h1
  ))
let encrypt #id #i #pp #key_length #kp #aparams ap k n p =
  let c =
    if KEY.(kp.hon k) && aparams.b then
      let p' = zero_bytes (length p) in
      //let p' = zero_bytes (length p) in
      aparams.scheme.enc p' k.raw n
    else
      aparams.scheme.enc (repr #pp kp k p) k.raw n
  in
  recall ap.log;
  MM.extend ap.log (n,c) p;
  c

val decrypt: #id:eqtype -> #i:id -> #pp:plain_package -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package #id key_length (key key_length #id) -> #aparams:ae_parameters kp pp -> ap:ae_package #pp #id #i aparams -> k:key key_length i -> n:nonce aparams.nonce_length -> c:ciphertext -> ST (option (p:protected_plain pp i))
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 p h1 ->
    ((KEY.(kp.hon k) /\ aparams.b) ==>
      (match p with
       | Some p' -> MM.contains ap.log (n,c) p' h0
       | None -> MM.fresh ap.log (n,c) h0
      ))
    /\ ((~(KEY.(kp.hon k)) \/ ~aparams.b) ==>
      (match aparams.scheme.dec c k.raw n with
       | Some p' -> Some? p /\ Some?.v p == coerce #pp kp k p'
       | None -> None? p
      ))
    /\ h0 == h1
  ))
let decrypt #id #i #pp #key_length #kp #aparams ap k n c =
  if KEY.(kp.hon k) && aparams.b then
    match MM.lookup ap.log (n,c) with
    | Some p ->
      // No idea why we need this.
       let h0 = HyperStack.ST.get() in
       assert(MM.contains ap.log (n,c) p h0);
       Some p
    | None -> None
  else
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (coerce #pp kp k p)
    | None -> None
