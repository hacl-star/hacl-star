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

let leak #kl #rgn ip #i k =
 k.raw

let getGT #kl #i k =
 k.raw

let gen key_length #rgn ip i =
 Key (random_bytes key_length) true

let coerce #key_length #rgn ip i raw =
  Key raw false

let create_ae_key_package #rgn ip key_length =
  KEY.create_key_package ip Flags.ae key_length (key key_length) (getGT #key_length) (leak #key_length #rgn ip) (gen key_length #rgn ip) (coerce ip)

let get_ap_pp #rgn #ip #key_length #kp #aparams ap = ap.pp

//let get_ap_rgn #rgn #ip #key_length #kp #aparams ap = ap.log_rgn

let recall_log #rgn #ip (#key_length:(n:nat{n<=32})) #kp #aparams ap = recall ap.log

let get_ap_log #rgn #ip #key_length #kp #aparams ap = ap.log

let create_ae_package (#rgn:erid) ip (#key_length:(n:nat{n<=32})) kp aparams =
  let log_rgn = new_region rgn in
  let pp = PP Flags.ae aparams.scheme.valid_plain_length in
  let log = MM.alloc #log_rgn #(message_log_key id aparams) #(message_log_range pp aparams) #(message_log_inv #pp #aparams) in
  AE #rgn #ip #key_length #kp #aparams pp log_rgn log

let zero_bytes valid_length n = Seq.create n (UInt8.uint_to_t 0)

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
let encrypt #rgn #ip #i #key_length #kp #aparams ap k n p =
  let honest_i = get_honesty ip i in
  let c =
    if honest_i && Flags.ae then
      aparams.scheme.enc_star (length p)
    else
      //lemma_dishonest_not_others
<<<<<<< HEAD
      aparams.scheme.enc (repr #rgn #ap.pp #ip p) k.raw n
=======
      aparams.scheme.enc (repr #rgn #ap.pp #ip #i p) k.raw n
>>>>>>> 264be060dd19c53ac9ab126eb69544c5fd13e723
  in
  recall ap.log;
  MM.extend ap.log (LOG_KEY i n c) p;
  c

let decrypt #rgn #ip #i #key_length #kp #aparams ap k n c =
  let honest_i = get_honesty ip i in
  match honest_i && Flags.ae with
  | true ->
    (match MM.lookup ap.log (LOG_KEY i n c) with
    | Some p ->
       recall ap.log;
       Some p
    | None -> None)
  | false ->
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (Plain.coerce #rgn #ap.pp ip i p)
    | None -> None
