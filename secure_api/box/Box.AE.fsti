module Box.AE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain
open Box.Index
open Mem

module KEY = Box.Key
module Flags = Box.Flags
module MM = FStar.Monotonic.Map


// KEY Package definition

val random_bytes: n:(n:nat{n<=32}) -> lbytes n

noeq abstract type key (#ip:index_package) (key_length:(n:nat{n<=32})) (i:id ip) =
     | Key:
       raw: lbytes key_length ->
       key #ip key_length i

val leak: #key_length:(n:nat{n<=32}) -> #ip:index_package -> #i:id ip{~Flags.ae \/ corrupt i} -> k:key key_length i -> raw:lbytes key_length{raw = k.raw}

val getGT: #key_length:(n:nat{n<=32}) -> (#ip:index_package) -> #i:id ip -> k:key key_length i -> GTot (raw:lbytes key_length{raw = k.raw})

val gen: key_length:(n:nat{n<=32}) -> #ip:index_package -> i:id ip -> k:key key_length i

val coerce: #key_length:(n:nat{n<=32}) -> #ip:index_package -> i:id ip{~Flags.ae \/ corrupt i} -> raw:lbytes key_length -> k:key key_length i{k.raw = raw}

val create_ae_key_package: ip:index_package -> key_length:(n:nat{n<=32}) -> kp:KEY.key_package ip{kp.KEY.key_length = key_length /\ kp.KEY.key_type == key #ip key_length}

// Definition AE package

let plain_package = pp:plain_package{pp.flag == Flags.ae}

noeq type encryption_scheme (key_length:(n:nat{n<=32})) (pp:plain_package)=
  | ES:
    gen: (unit -> lbytes key_length) ->
    enc: (p:plain pp -> k:lbytes key_length -> n:nonce pp -> c:cipher pp) ->
    enc_star: (plain_length:nat{pp.valid_plain_length plain_length} -> c:cipher pp) ->
    dec: (c:cipher pp -> k:lbytes key_length -> n:nonce pp -> option (p:plain pp)) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
      //    ) ->
    encryption_scheme key_length pp

// Make them abstract or move the flag to ae_package?
noeq type ae_parameters (pp:plain_package) =
  | GP:
    keylength:(n:nat{n<=32}) ->
    scheme: (encryption_scheme keylength pp) ->
    ae_parameters pp

noeq abstract type ae_package (#pp:plain_package) (ip:index_package) (aparams:ae_parameters pp) =
  | AE:
    log_rgn:erid ->
    log:message_log ip pp log_rgn ->
    ae_package #pp ip aparams

val recall_log: (#ip:index_package) -> (#pp:plain_package) -> (#aparams:ae_parameters pp) -> (ap:ae_package ip aparams) -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ (Flags.model ==>
      (let log : i_message_log ip pp ap.log_rgn = ap.log in
      contains h1 log))
  ))

val get_log_rgn: (#ip:index_package) -> (#pp:plain_package) -> (#aparams:ae_parameters pp) -> (ap:ae_package ip aparams) -> Tot (rgn:erid{rgn = ap.log_rgn})

val get_ap_log: (#ip:index_package) -> (#pp:plain_package) -> (#aparams:ae_parameters pp) -> (ap:ae_package ip aparams) -> GTot (message_log ip pp (get_log_rgn ap))

let nonce_is_unique (#ip:index_package) (#pp:plain_package)  (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (i:id ip) (n:nonce pp) (h0:mem) =
  Flags.model ==> (
    let log : i_message_log ip pp ap.log_rgn = ap.log in
    forall c . MM.fresh log (i,n,c) h0)

val create_ae_package: (#ip:index_package) -> (#pp:plain_package) -> (rgn:erid) -> (aparams:ae_parameters pp) -> ST (ae_package ip aparams)
  (requires (fun h0 -> True))
  (ensures (fun h0 ap h1 ->
    if Flags.model then
      let log : i_message_log ip pp ap.log_rgn = ap.log in
      modifies (Set.singleton rgn) h0 h1
      /\ (forall n i . nonce_is_unique ap i n h1)
      /\ extends ap.log_rgn rgn
      /\ sel h1 log == empty_message_log ip pp
      /\ contains h1 log
    else
      modifies_none h0 h1
  ))

val zero_bytes: (valid_length:(n:nat -> bool)) -> (n:nat{valid_length n}) -> p:lbytes n{valid_length (Seq.length p)}

let encrypt_footprint (#ip:index_package) (#pp:plain_package) (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (h0:mem) (h1:mem) =
  if Flags.model then
    modifies (Set.singleton ap.log_rgn) h0 h1
  else
    h0 == h1

let encrypt_log_change (#ip:index_package) (#pp:plain_package) (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (i:id ip) (n:nonce pp) (c:cipher pp) (p:protected_plain pp i) (h0:mem) (h1:mem) =
  Flags.model ==>
    (let log : i_message_log ip pp ap.log_rgn = ap.log in
    witnessed (MM.contains log (i,n,c) p)
    /\ contains h0 log
    /\ sel h1 log == MM.upd (sel h0 log) (i,n,c) p)

let encrypt_functional_spec (#ip:index_package) (#pp:plain_package) (#i:id ip) (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (k:key aparams.keylength i) (n:nonce pp) (c:cipher pp) (p:protected_plain pp i) =
  ((honest i /\ Flags.ae) ==>
    (c = aparams.scheme.enc_star (length p)))
  /\ ((corrupt i \/ ~Flags.ae) ==>
    (c = aparams.scheme.enc (repr p) k.raw n))

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
val encrypt: #ip:index_package -> #pp:plain_package -> #i:id ip -> #aparams:ae_parameters pp -> ap:ae_package ip aparams -> k:key aparams.keylength i -> n:nonce pp -> p:protected_plain pp i -> ST (cipher pp)
  (requires (fun h0 ->
    (nonce_is_unique ap i n h0)
    /\ registered i
  ))
  (ensures (fun h0 c h1 ->
    encrypt_functional_spec ap k n c p
    /\ encrypt_log_change ap i n c p h0 h1
    /\ encrypt_footprint ap h0 h1
    /\ ((forall n'. nonce_is_unique ap i n' h0) ==> (forall n' . n' =!=n ==> nonce_is_unique ap i n' h1))
  ))

let decrypt_footprint (#ip:index_package) (#pp:plain_package) (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (h0:mem) (h1:mem) = h0 == h1

let decrypt_log_change (#ip:index_package) (#pp:plain_package) (#aparams:ae_parameters pp) (ap:ae_package ip aparams) (h0:mem) (h1:mem) =
  Flags.model ==>
    (let log : i_message_log ip pp ap.log_rgn = ap.log in
    sel h1 log == sel h0 log)

let decrypt_functional_spec (#pp:plain_package)
                            (#ip:index_package)
                            (#i:id ip)
                            (#aparams:ae_parameters pp)
                            (ap:ae_package ip aparams)
                            (k:key aparams.keylength i)
                            (n:nonce pp)
                            (c:cipher pp)
                            (p:option (protected_plain pp i))
                            (h0:mem) =
    ((honest i /\ Flags.ae) ==>
      (let log : i_message_log ip pp ap.log_rgn = ap.log in
      match p with
       | Some p' -> MM.contains log (i,n,c) p' h0
       | None -> MM.fresh log (i,n,c) h0
      ))
    /\ ((corrupt i \/ ~Flags.ae) ==>
      (match aparams.scheme.dec c k.raw n with
       | Some p' -> Some? p /\ Some?.v p == Plain.coerce i p'
       | None -> None? p
      ))

val decrypt: #ip:index_package -> #pp:plain_package -> #i:id ip -> #aparams:ae_parameters pp -> ap:ae_package ip aparams -> k:key aparams.keylength i -> n:nonce pp -> c:cipher pp -> ST (option (p:protected_plain pp i))
  (requires (fun h0 ->
    registered i
  ))
  (ensures (fun h0 p h1 ->
    decrypt_functional_spec ap k n c p h0
    /\ decrypt_footprint ap h0 h1
    /\ decrypt_log_change ap h0 h1
  ))
