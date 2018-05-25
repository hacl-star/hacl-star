module Box.Key

open FStar.Endianness

// Definition KEY package
let hon #id #key_length #key_type kp = kp.hon

let getGT #id #key_length #key_type kp = kp.getGT

let cget #id #key_length #key_type kp = kp.cget

let get #id #key_length #key_type kp = kp.get

let gen #id #key_length #key_type kp = kp.gen

let cset #id #key_length #key_type kp = kp.cset

let set #id #key_length #key_type kp = kp.set

let create_key_package #id key_length key_type hon getGT cget get gen cset set =
  KP hon getGT cget get gen cset set
