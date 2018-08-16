module Box.AE

open FStar.Set
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST

open FStar.Endianness

open Box.Index
open Box.Plain

module KEY = Box.Key
module MM = FStar.Monotonic.Map

// KEY Package definition

let rec random_bytes n =
  match n with
  | 0 -> let l:lbytes 0 = createL [] in l
  | _ -> append (createL [0x0buy]) (random_bytes (n-1))

let leak #ip #kl #i k =
 k.raw

let getGT #ip #kl #i k =
 k.raw

let gen key_length #ip i =
 Key (random_bytes key_length)

let coerce #key_length #ip i raw =
  Key raw

let create_ae_key_package ip key_length =
  KEY.create_key_package Flags.ae key_length (key key_length) getGT leak (gen key_length) coerce

//let get_ap_pp #ip #key_length #kp #aparams ap = ap.pp

//let get_ap_rgn #rgn #ip #key_length #kp #aparams ap = ap.log_rgn

let recall_log #ip #pp #aparams ap =
  if Flags.model then
    let log : i_message_log ip pp ap.log_rgn = ap.log in
    recall log
  else
    ()

let get_log_rgn #ip #pp #aparams ap = ap.log_rgn

let get_ap_log #ip #pp #aparams ap = ap.log

let create_ae_package #ip #pp (rgn:erid) aparams =
  let log_rgn = new_region rgn in
  //let pp = PP Flags.ae aparams.scheme.valid_plain_length aparams.scheme.valid_cipher_length in
  let log =
    if Flags.model then
      alloc_message_log log_rgn ip pp
    else
      ()
  in
  //let log = MM.alloc #log_rgn #(message_log_key aparams) #(message_log_range pp aparams) #(message_log_inv #pp #aparams) in
  AE #pp #ip #aparams log_rgn log

let zero_bytes valid_length n = Seq.create n (UInt8.uint_to_t 0)

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
let encrypt #ip #pp #i #aparams ap k n p =
  let honest_i = get_honesty i in
  let c =
    if honest_i && Flags.ae then
      aparams.scheme.enc_star (length p)
    else
      //lemma_dishonest_not_others
      aparams.scheme.enc (repr p) k.raw n
  in
  // To ensure nonce uniqueness, we extend the log even if we don't idealize.
  // Should nonce uniqueness be its own assumption?
  if Flags.model then
    (let log : i_message_log ip pp ap.log_rgn = ap.log in
    recall log;
    MM.extend log (i,n,c) p);
  c

let decrypt #ip #pp #i #aparams ap k n c =
  let honest_i = get_honesty i in
  match honest_i && Flags.ae with
  | true ->
    (let log : i_message_log ip pp ap.log_rgn = ap.log in
    match MM.lookup log (i,n,c) with
    | Some p ->
       recall log;
       Some p
    | None -> None)
  | false ->
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (Plain.coerce i p)
    | None -> None
