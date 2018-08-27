module Spec.Lib.Stateful
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

let stateful (d:state_def) (r:Type0) : Type = d.state -> tuple2 r d.state

let alloc #d (f:stateful d 'a) : 'a  =
  let s = d.create () in
  let (r,s') = f s in
  r

let read #d (k:d.key) (x:state_index d k) : stateful d (d.value k) =
  fun s -> (d.get s k).[x],s

let write #d (k:d.key) (x:state_index d k) (v:d.value k) : stateful d unit =
  fun s -> (),(d.put s k ((d.get s k).[x] <- v ))

let return #d (x:'a) : stateful d 'a =
  fun s -> x, s

let bind #d (f:stateful d 'a) (g:'a -> stateful d 'b) : stateful d 'b =
  fun s -> let a,s' = f s in g a s'


let apply_st #d (k1:d.key) (k2:d.key) (f:state_seq d k1 -> state_seq d k2) : stateful d unit =
  fun s -> (), d.put s k2 (f (d.get s k1))

let apply2_st #d (k1:d.key) (k2:d.key) (k3:d.key) (f:state_seq d k1 -> state_seq d k2 -> state_seq d k3) : stateful d unit =
  fun s -> (), d.put s k3 (f (d.get s k1) (d.get s k2))

let apply2_ext_st #d (#a:Type0) (#len:size_nat) (ext:lseq a len) (k1:d.key) (k2:d.key) (f:lseq a len -> state_seq d k1 -> state_seq d k2) : stateful d unit =
  fun s -> (), d.put s k2 (f ext (d.get s k1))

(* Useful functions *)
let repeat_stateful #d (n:size_nat) (f:stateful d unit) : stateful d unit =
  fun s -> (),repeat n (fun s -> snd (f s)) s

let repeat_range_stateful #d (min:size_nat) (max:size_nat{min <= max}) (f:(i:size_nat{i >= min /\ i < max} -> stateful d unit)) : stateful d unit =
  fun s -> (),repeat_range min max (fun i s -> snd (f i s)) s

let copy #d k1 k2 : stateful d unit =
  apply_st k1 k2 (fun x -> x)
let in_place_map2 #d (k1:d.key) (k2:d.key{d.value k1 == d.value k2 /\ d.length k1 == d.length k2}) (f:d.value k1 -> d.value k2 -> d.value k2) : stateful d unit =
  apply2_st k1 k2 k2 (map2 f)
let import #a #len #d ext k f : stateful d unit =
  fun s -> (), d.put s k (f ext)
let import_slice #a #len #d ext k min max f : stateful d unit =
  fun s -> (), d.put s k (update_slice (d.get s k) min max (f ext))

let export #a #len #d k f : stateful d (lseq a len) =
  fun s -> (f (d.get s k)), s
