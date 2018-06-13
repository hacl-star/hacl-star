module Box.AE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Plain
open Box.Index

module KEY = Box.Key
module Flags = Box.Flags
module MM = FStar.Monotonic.Map

// KEY Package definition

val random_bytes: n:(n:nat{n<=32}) -> lbytes n

let bytes32 = b:bytes{Seq.length b <= 32}

noeq abstract type key (key_length:(n:nat{n<=32})) (i:inst_id) =
     | Key:
       raw: lbytes key_length ->
       h:bool ->
       key key_length i

val leak: #key_length:(n:nat{n<=32}) -> #rgn:erid -> ip:index_package rgn -> #i:inst_id{~Flags.ae \/ dishonest ip i} -> k:key key_length i -> raw:lbytes key_length{raw = k.raw}

val getGT: #key_length:(n:nat{n<=32}) -> #i:inst_id -> k:key key_length i -> GTot (raw:lbytes key_length{raw = k.raw})

val gen: key_length:(n:nat{n<=32}) -> #rgn:erid -> ip:index_package rgn -> i:inst_id -> k:key key_length i

val coerce: #key_length:(n:nat{n<=32}) -> #rgn:erid -> ip:index_package rgn -> i:inst_id{~Flags.ae \/ dishonest ip i} -> raw:lbytes key_length -> k:key key_length i{k.raw = raw}

val create_ae_key_package: #rgn:erid -> ip:index_package rgn -> key_length:(n:nat{n<=32}) -> KEY.key_package ip key_length (key key_length)


// Definition AE package
noeq type encryption_scheme (key_length:(n:nat{n<=32})) (nonce_length:(n:nat{n<=32})) =
  | ES:
    valid_plain_length:(nat -> bool) ->
    valid_cipher_length:(nat -> bool) ->
    gen: (unit -> lbytes key_length) ->
    enc: (p:bytes32{valid_plain_length (Seq.length p)} -> k:lbytes key_length -> n:lbytes nonce_length -> c:bytes32{valid_cipher_length (Seq.length c)}) ->
    enc_star: (plain_length:n32{valid_plain_length plain_length} -> k:lbytes key_length -> n:lbytes nonce_length -> c:bytes32{valid_cipher_length (Seq.length c)}) ->
    dec: (c:bytes32{valid_cipher_length (Seq.length c)} -> k:lbytes key_length -> n:lbytes nonce_length -> option (p:bytes32{valid_plain_length (Seq.length p)})) ->
//    correctness: (p:bytes -> k:lbytes key_length -> n:lbytes nonce_length -> Lemma
//    (requires True)
//    (ensures (
//      let dec_result = dec (enc p k n) k n in
//      Some? dec_result
//      /\ Some?.v dec_result == p
//    ))
//    ) ->
    encryption_scheme key_length nonce_length

// Make them abstract or move the flag to ae_package?
noeq type ae_parameters =
  | GP:
    keylength:(n:nat{n<=32}) ->
    nonce_length:(n:nat{n<=32}) ->
    scheme: (encryption_scheme keylength nonce_length) ->
    ae_parameters

//let nonce (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #key_length key) (#pp:plain_package) (ap:ae_parameters kp pp) = lbytes ap.nonce_length
let nonce (aparams:ae_parameters) = lbytes aparams.nonce_length
let ciphertext (aparams:ae_parameters) = c:bytes32{aparams.scheme.valid_cipher_length (Seq.length c)}

type message_log_key (id:eqtype) (aparams:ae_parameters) =
  | LOG_KEY: i:inst_id -> n:nonce aparams -> c:ciphertext aparams -> message_log_key id aparams

let message_log_value (i:inst_id) (pp:plain_package) = protected_plain pp i
let message_log_range (pp:plain_package) (aparams:ae_parameters) (k:message_log_key id aparams) = message_log_value (k.i) pp
let message_log_inv (#pp:plain_package) (#aparams:ae_parameters) (f:MM.map' (message_log_key id aparams) (message_log_range pp aparams)) = True

let message_log (#pp:plain_package) (rgn:erid) (aparams:ae_parameters) =
  MM.t rgn (message_log_key id aparams) (message_log_range pp aparams) (message_log_inv)

let empty_message_log (aparams:ae_parameters) (pp:plain_package) = MM.empty_map (message_log_key id aparams) (message_log_range pp aparams)

noeq abstract type ae_package (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (kp:KEY.key_package ip key_length (key key_length)) (aparams:ae_parameters{aparams.keylength = key_length}) =
  | AE:
    pp:plain_package{pp == PP Flags.ae aparams.scheme.valid_plain_length} ->
    log_rgn:erid{extends log_rgn rgn} ->
    log:message_log #pp log_rgn aparams ->
    ae_package #rgn #ip #key_length kp aparams

//val get_flag: (#rgn:erid) -> (#ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package ip key_length (key key_length)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> ap:ae_package kp aparams -> GTot (b:bool{b = ap.b})
//let valid_ae_plain_package (aparams:ae_parameters) (pp:plain_package) = pp == PP (get_ae_flagGT aparams) aparams.scheme.valid_plain_length

val get_ap_pp: (#rgn:erid) -> (#ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package ip key_length (key key_length)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> (ap:ae_package #rgn #ip #key_length kp aparams) -> pp:plain_package{pp == PP Flags.ae aparams.scheme.valid_plain_length /\ pp == ap.pp}

//val get_ap_rgn: (#rgn:erid) -> (#ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package ip key_length (key key_length)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> (ap:ae_package #rgn #ip #key_length kp aparams) -> rgn:erid{rgn = ap.rgn}

val recall_log: (#rgn:erid) -> (#ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package ip key_length (key key_length)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> (ap:ae_package kp aparams) -> ST unit
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 ->
    h0 == h1
    /\ contains h1 ap.log
  ))

val get_ap_log: (#rgn:erid) -> (#ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (#kp:KEY.key_package ip key_length (key key_length)) -> (#aparams:ae_parameters{aparams.keylength = key_length}) -> (ap:ae_package kp aparams) -> GTot (message_log #ap.pp ap.log_rgn aparams)

let nonce_is_unique (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) (i:inst_id) (n:nonce aparams) (h0:mem) =
  forall c . MM.fresh ap.log (LOG_KEY i n c) h0

val create_ae_package: (#rgn:erid) -> (ip:index_package rgn) -> (#key_length:(n:nat{n<=32})) -> (kp:KEY.key_package ip key_length (key key_length)) -> (aparams:ae_parameters{aparams.keylength = key_length}) -> ST (ae_package kp aparams)
  (requires (fun h0 -> True))
  (ensures (fun h0 ap h1 ->
    modifies (Set.singleton rgn) h0 h1
    /\ (forall n i . nonce_is_unique ap i n h1)
    /\ extends ap.log_rgn rgn
    /\ contains h1 ap.log
    /\ sel h1 ap.log == empty_message_log aparams ap.pp
  ))

val zero_bytes: (valid_length:(n:n32 -> bool)) -> (n:n32{valid_length n}) -> p:lbytes n{valid_length (Seq.length p)}

let encrypt_modified_regions (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) : (Set.set rid) = Set.singleton ap.log_rgn

let encrypt_log_change (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) (i:inst_id) (n:nonce aparams) (c:ciphertext aparams) (p:protected_plain ap.pp i) (h0:mem) (h1:mem) =
    let a = 1 in
    witnessed (MM.contains ap.log (LOG_KEY i n c) p)
    /\ contains h0 ap.log
    /\ sel h1 ap.log == MM.upd (sel h0 ap.log) (LOG_KEY i n c) p

let encrypt_functional_spec (#rgn:erid) (#ip:index_package rgn) (#i:inst_id) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) (k:key key_length i) (n:nonce aparams) (c:ciphertext aparams) (p:protected_plain ap.pp i) =
  let a = 1 in
  ((honest ip i /\ Flags.ae) ==>
    (c = aparams.scheme.enc_star (length p) k.raw n))
  /\ ((dishonest ip i \/ ~Flags.ae) ==>
    (c = aparams.scheme.enc (repr #rgn #ap.pp #ip #i p) k.raw n))

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
val encrypt: #rgn:erid -> #ip:index_package rgn -> #i:inst_id -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package ip key_length (key key_length) -> #aparams:ae_parameters{key_length = aparams.keylength} -> ap:ae_package kp aparams -> k:key key_length i -> n:nonce aparams -> p:protected_plain ap.pp i -> ST (ciphertext aparams)
  (requires (fun h0 ->
    (nonce_is_unique ap i n h0)
  ))
  (ensures (fun h0 c h1 ->
    encrypt_functional_spec ap k n c p
    /\ encrypt_log_change ap i n c p h0 h1
    /\ modifies (encrypt_modified_regions ap) h0 h1
    /\ ((forall n'. nonce_is_unique ap i n' h0) ==> (forall n' . n' =!=n ==> nonce_is_unique ap i n' h1))
  ))

let decrypt_modified_regions (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) = Set.empty

let decrypt_log_change (#rgn:erid) (#ip:index_package rgn) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package ip key_length (key key_length)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package kp aparams) (h0:mem) (h1:mem) =
  sel h1 ap.log == sel h0 ap.log


let decrypt_functional_spec (#rgn:erid)
                            (#ip:index_package rgn)
                            (#i:inst_id)
                            (#key_length:(n:nat{n<=32}))
                            (#kp:KEY.key_package ip key_length (key key_length))
                            (#aparams:ae_parameters{aparams.keylength = key_length})
                            (ap:ae_package kp aparams)
                            (k:key key_length i)
                            (n:nonce aparams)
                            (c:ciphertext aparams)
                            (p:option (protected_plain ap.pp i))
                            (h0:mem) =
  let a = 1 in
    ((honest ip i /\ Flags.ae) ==>
      (match p with
       | Some p' -> MM.contains ap.log (LOG_KEY i n c) p' h0
       | None -> MM.fresh ap.log (LOG_KEY i n c) h0
      ))
    /\ ((dishonest ip i \/ ~Flags.ae) ==>
      (match aparams.scheme.dec c k.raw n with
       | Some p' -> Some? p /\ Some?.v p == Plain.coerce ip i p'
       | None -> None? p
      ))

val decrypt: #rgn:erid -> #ip:index_package rgn -> #i:inst_id -> #key_length:(n:nat{n<=32}) -> #kp:KEY.key_package ip key_length (key key_length) -> #aparams:ae_parameters{key_length = aparams.keylength} -> ap:ae_package kp aparams -> k:key key_length i -> n:nonce aparams -> c:ciphertext aparams -> ST (option (p:protected_plain ap.pp i))
  (requires (fun h0 ->
    True
  ))
  (ensures (fun h0 p h1 ->
    decrypt_functional_spec ap k n c p h0
    /\ modifies (decrypt_modified_regions ap) h0 h1
    /\ decrypt_log_change ap h0 h1
  ))
