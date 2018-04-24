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

val create_ae_key_package: id:eqtype -> key_length:(n:nat{n<=32}) -> KEY.key_package #id key_length (key key_length #id)
let create_ae_key_package id key_length =
  KEY.KP (hon #id #key_length) (get #id #key_length) (gen key_length) set


// Definition AE package
noeq type encryption_scheme (key_length:(n:nat{n<=32})) (nonce_length:(n:nat{n<=32})) =
  | ES:
    valid_plain_length:(nat -> bool) ->
    valid_cipher_length:(nat -> bool) ->
    gen: (unit -> lbytes key_length) ->
    enc: (p:bytes{valid_plain_length (Seq.length p)} -> k:lbytes key_length -> n:lbytes nonce_length -> c:bytes{valid_cipher_length (Seq.length c)}) ->
    dec: (c:bytes{valid_cipher_length (Seq.length c)} -> k:lbytes key_length -> n:lbytes nonce_length -> option (p:bytes{valid_plain_length (Seq.length p)})) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
//    ) ->
    encryption_scheme key_length nonce_length

abstract type flag = bool
assume val b: flag

noeq type ae_parameters =
  | GP:
    keylength:(n:nat{n<=32}) ->
    nonce_length:(n:nat{n<=32}) ->
//    b:flag ->
    scheme: (encryption_scheme keylength nonce_length) ->
    ae_parameters

val get_ae_flagGT: aparams:ae_parameters -> GTot (b:Type0)
let get_ae_flagGT aparams =
  b2t b

let valid_ae_plain_package (aparams:ae_parameters) (pp:plain_package) = pp == PP (get_ae_flagGT aparams) aparams.scheme.valid_plain_length
//let nonce (#id:eqtype) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id #key_length key) (#pp:plain_package) (ap:ae_parameters kp pp) = lbytes ap.nonce_length
let nonce (aparams:ae_parameters) = lbytes aparams.nonce_length
let ciphertext (aparams:ae_parameters) = c:bytes{aparams.scheme.valid_cipher_length (Seq.length c)}

let message_log_key (aparams:ae_parameters) = (nonce aparams*ciphertext aparams)
let message_log_value (#id:eqtype) (i:id) (pp:plain_package) = protected_plain pp i
let message_log_range (#id:eqtype) (i:id) (pp:plain_package) (aparams:ae_parameters) (k:message_log_key aparams) = message_log_value i pp
let message_log_inv (#pp:plain_package) (#aparams:ae_parameters) (#id:eqtype) (i:id) (f:MM.map' (message_log_key aparams) (message_log_range i pp aparams)) = True

let message_log (#pp:plain_package) (#id:eqtype) (rgn:erid) (aparams:ae_parameters) (i:id) =
  MM.t rgn (message_log_key aparams) (message_log_range i pp aparams) (message_log_inv i)

noeq abstract type ae_package (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (kp:KEY.key_package #id key_length (key key_length #id)) (aparams:ae_parameters{aparams.keylength = key_length}) (pp:plain_package{valid_ae_plain_package aparams pp}) =
  | AE:
    rgn:erid ->
    log:message_log #pp #id rgn aparams i ->
    ae_package #id #i #key_length kp aparams pp

let get_ap_rgn (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (#aparams:ae_parameters{aparams.keylength = key_length}) (#pp:plain_package{valid_ae_plain_package aparams pp}) (ap:ae_package #id #i #key_length kp aparams pp)= ap.rgn

let recall_log (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (#aparams:ae_parameters{aparams.keylength = key_length}) (#pp:plain_package{valid_ae_plain_package aparams pp}) (ap:ae_package #id #i #key_length kp aparams pp) = recall ap.log

val get_ap_log: (#id:eqtype) -> (#i:id) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package #id key_length (key key_length #id)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> (#pp:plain_package{valid_ae_plain_package aparams pp}) -> (ap:ae_package #id #i #key_length kp aparams pp) -> GTot (message_log #pp #id ap.rgn aparams i)
let get_ap_log #id #i #key_length #kp #aparams #pp ap = ap.log

let nonce_is_unique (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (#aparams:ae_parameters{aparams.keylength = key_length}) (#pp:plain_package{valid_ae_plain_package aparams pp}) (ap:ae_package #id #i #key_length kp aparams pp) (n:nonce aparams) (h0:mem) =
  forall c . MM.fresh ap.log (n,c) h0

val create_ae_package:(rgn:erid) -> (#id:eqtype) -> (#i:id) -> (#key_length:(n:nat{n<=32})) -> (kp:KEY.key_package #id key_length (key key_length #id)) -> (aparams:ae_parameters{aparams.keylength = key_length}) -> (pp:plain_package{valid_ae_plain_package aparams pp}) -> ST (ae_package #id #i #key_length kp aparams pp)
  (requires (fun h0 -> True))
  (ensures (fun h0 ap h1 ->
    modifies (Set.singleton rgn) h0 h1
    /\ (forall n . nonce_is_unique ap n h1)
    /\ extends ap.rgn rgn
    /\ contains h1 ap.log
  ))
let create_ae_package (rgn:erid) (#id:eqtype) (#i:id) (#key_length:(n:nat{n<=32})) (kp:KEY.key_package #id key_length (key key_length #id)) (aparams:ae_parameters{aparams.keylength = key_length}) (pp:plain_package{valid_ae_plain_package aparams pp}) =
  let rgn = new_region rgn in
  let log = MM.alloc #rgn #(message_log_key aparams) #(message_log_range #id i pp aparams) #(message_log_inv #pp #aparams #id i) in
  AE #id #i #key_length #kp #aparams #pp rgn log

val zero_bytes: (valid_length:(n:nat -> bool)) -> (n:nat{valid_length n}) -> p:lbytes n{valid_length (Seq.length p)}
let zero_bytes valid_length n = Seq.create n (UInt8.uint_to_t 0)

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
val encrypt: #id:eqtype -> #i:id -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package #id key_length (key key_length #id) -> #aparams:ae_parameters{key_length = aparams.keylength} -> #pp:plain_package{ valid_ae_plain_package aparams pp} ->  ap:ae_package #id #i #key_length kp aparams pp -> k:key key_length i -> n:nonce aparams -> p:protected_plain pp i -> ST (ciphertext aparams)
  (requires (fun h0 ->
    (nonce_is_unique ap n h0)
  ))
  (ensures (fun h0 c h1 ->
    ((KEY.(kp.hon k) /\ get_ae_flagGT aparams) ==>
      (c = aparams.scheme.enc (zero_bytes (pp.valid_length) (length p)) k.raw n))
      // Not sure why I can't use aparams.b here instead of get_ae_flagGT...
    /\ ((~(KEY.(kp.hon k)) \/ ~(get_ae_flagGT aparams)) ==>
      (c = aparams.scheme.enc (repr #pp kp k p) k.raw n))
    /\ witnessed (MM.contains ap.log (n,c) p)
    //TODO: Add precise description of log state here.
    /\ modifies (Set.singleton ap.rgn) h0 h1
  ))
let encrypt #id #i #key_length #kp #aparams #pp ap k n p =
  let c =
    if KEY.(kp.hon k) && b then
      let p' = zero_bytes (pp.valid_length) (length p) in
      aparams.scheme.enc p' k.raw n
    else
      aparams.scheme.enc (repr #pp kp k p) k.raw n
  in
  recall ap.log;
  MM.extend ap.log (n,c) p;
  c

val decrypt: #id:eqtype -> #i:id -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package #id key_length (key key_length #id) -> #aparams:ae_parameters{key_length = aparams.keylength} -> #pp:plain_package{valid_ae_plain_package aparams pp} -> ap:ae_package #id #i kp aparams pp -> k:key key_length i -> n:nonce aparams -> c:ciphertext aparams -> ST (option (p:protected_plain pp i))
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 p h1 ->
    ((KEY.(kp.hon k) /\ get_ae_flagGT aparams) ==>
      (match p with
       | Some p' -> MM.contains ap.log (n,c) p' h0
       | None -> MM.fresh ap.log (n,c) h0
      ))
    /\ ((~(KEY.(kp.hon k)) \/ ~(get_ae_flagGT aparams)) ==>
      (match aparams.scheme.dec c k.raw n with
       | Some p' -> Some? p /\ Some?.v p == coerce #pp kp k p'
       | None -> None? p
      ))
    /\ h0 == h1
  ))
let decrypt #id #i #key_length #kp #aparams #pp ap k n c =
  match KEY.(kp.hon k) && b with
  | true ->
    (match MM.lookup ap.log (n,c) with
    | Some p ->
      // No idea why we need this.
       let h0 = HyperStack.ST.get() in
       assert(MM.contains ap.log (n,c) p h0);
       Some p
    | None -> None)
  | false ->
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (coerce #pp kp k p)
    | None -> None
