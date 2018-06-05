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

let rec random_bytes n =
  match n with
  | 0 -> let l:lbytes 0 = createL [] in l
  | _ -> append (createL [0x0buy]) (random_bytes (n-1))

let hon #id #kl i k =
 k.h

let cget #id #kl i k =
 k.raw

let get #id #kl i k =
 k.raw

let getGT #id #kl i k =
 k.raw

let set #id #key_length i raw =
  Key raw true

let gen #id key_length i =
 Key (random_bytes key_length) true

let cset #id #key_length i raw =
  Key raw false

let create_ae_key_package id key_length =
  KEY.create_key_package key_length (key key_length #id) (hon #id #key_length) (getGT #id #key_length) (cget #id #key_length) (get #id #key_length) (gen #id key_length) cset set

let get_flag #id #key_length #kp #aparams ap = ap.b

let get_ap_pp #id #key_length #kp #aparams ap = ap.pp

let get_ap_rgn (#id:eqtype) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package #id #key_length kp aparams)= ap.rgn

let recall_log (#id:eqtype) (#key_length:(n:nat{n<=32})) (#kp:KEY.key_package #id key_length (key key_length #id)) (#aparams:ae_parameters{aparams.keylength = key_length}) (ap:ae_package #id kp aparams) = recall ap.log

let get_ap_log #id #key_length #kp #aparams ap = ap.log

let create_ae_package (rgn:erid) (#id:eqtype) (#key_length:(n:nat{n<=32})) (kp:KEY.key_package #id key_length (key key_length #id)) (aparams:ae_parameters{aparams.keylength = key_length}) (b:bool) =
  let rgn = new_region rgn in
  let pp = PP b aparams.scheme.valid_plain_length in
  let log = MM.alloc #rgn #(message_log_key id aparams) #(message_log_range #id pp aparams) #(message_log_inv #pp #aparams #id) in
  AE #id #key_length #kp #aparams b pp rgn log

let zero_bytes valid_length n = Seq.create n (UInt8.uint_to_t 0)

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 300"
let encrypt #id #i #key_length #kp #aparams ap k n p =
  let c =
    if KEY.(hon kp i k) && ap.b then
      let p' = zero_bytes (ap.pp.valid_length) (length p) in
      aparams.scheme.enc p' k.raw n
    else
      aparams.scheme.enc (repr #ap.pp kp k p) k.raw n
  in
  recall ap.log;
  MM.extend ap.log (LOG_KEY i n c) p;
  c

let decrypt #id #i #key_length #kp #aparams ap k n c =
  match KEY.(hon kp i k) && ap.b with
  | true ->
    (match MM.lookup ap.log (LOG_KEY i n c) with
    | Some p ->
       recall ap.log;
       Some p
    | None -> None)
  | false ->
    match aparams.scheme.dec c k.raw n with
    | Some p -> Some (coerce #ap.pp kp k p)
    | None -> None
