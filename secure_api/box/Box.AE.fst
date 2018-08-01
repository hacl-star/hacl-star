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

let leak #kl ip #i k =
 k.raw

let getGT #kl #i k =
 k.raw

let gen key_length ip i =
 Key (random_bytes key_length) true

let coerce #key_length ip i raw =
  Key raw false

let create_ae_key_package ip key_length =
  KEY.create_key_package ip Flags.ae key_length (key key_length) (getGT #key_length) (leak #key_length ip) (gen key_length ip) (coerce ip)

let get_ap_pp #ip #key_length #kp #aparams ap = ap.pp

//let get_ap_rgn #rgn #ip #key_length #kp #aparams ap = ap.log_rgn

let recall_log #ip (#key_length:(n:nat{n<=32})) #kp #aparams ap = recall ap.log

let get_log_rgn #ip #key_length #kp #aparams ap = ap.log_rgn

let get_ap_log #ip #key_length #kp #aparams ap = ap.log

let create_ae_package #ip (#key_length:(n:nat{n<=32})) (rgn:erid) kp aparams =
  let log_rgn = new_region rgn in
  let pp = PP Flags.ae aparams.scheme.valid_plain_length in
  let log = alloc_ae_message_log aparams log_rgn pp in
  //let log = MM.alloc #log_rgn #(message_log_key aparams) #(message_log_range pp aparams) #(message_log_inv #pp #aparams) in
  AE #ip #key_length #kp #aparams pp log_rgn log

let zero_bytes valid_length n = Seq.create n (UInt8.uint_to_t 0)

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
let encrypt #ip #i #key_length #kp #aparams ap k n p =
  let honest_i = get_honesty ip i in
  let c =
    if honest_i && Flags.ae then
      aparams.scheme.enc_star (length p)
    else
      //lemma_dishonest_not_others
      aparams.scheme.enc (repr #ap.pp #ip #i p) k.raw n
  in
  recall ap.log;
  MM.extend ap.log (i,n,c) p;
  c

let decrypt #ip #i #key_length #kp #aparams ap k n c =
  let honest_i = get_honesty ip i in
  match honest_i && Flags.ae with
  | true ->
    (match MM.lookup ap.log (i,n,c) with
    | Some p ->
       recall ap.log;
       Some p
    | None -> None)
  | false ->
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (Plain.coerce #ap.pp ip i p)
    | None -> None
