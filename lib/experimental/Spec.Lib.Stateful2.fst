module Spec.Lib.Stateful2
open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

let stateful 's 'a = 's -> tuple2 'a 's

let run (a:allocator 's) (f:stateful 's 'a) : 'a  =
  let s =  a() in
  let (r,s') = f s in
  r

let get (k:accessor 's 'a) : stateful 's 'a =
  fun s -> k.get s,s

let put (k:accessor 's 'a) (v:'a) : stateful 's unit =
  fun s -> (),(k.put s v)

let return (#s:Type0) (x:'a) : stateful s 'a =
  fun s -> x, s

let bind (f:stateful 's 'a) (g:'a -> stateful 's 'b) : stateful 's 'b =
  fun s -> let a,s' = f s in g a s'


let apply_st (k1:accessor 's 'a) (k2:accessor 's 'b) (f:'a -> 'b) : stateful 's unit =
  fun s -> (), k2.put s (f (k1.get s))

let apply2_st (k1:accessor 's 'a) (k2:accessor 's 'b) (k3:accessor 's 'c) (f:'a -> 'b -> 'c) : stateful 's unit =
  fun s -> (), k3.put s (f (k1.get s) (k2.get s))

(* Useful functions *)
let loop (min:size_nat) (max:size_nat{min <= max}) (f:i:size_nat{i>=min /\ i < max} -> stateful 's unit) : stateful 's unit =
  fun s -> (),repeat_range min max (fun i s -> snd (f i s)) s

let repeat (n:size_nat) (f:stateful 's unit) : stateful 's unit =
  fun s -> (),repeat n (fun s -> snd (f s)) s

let copy (k1:accessor 's 'a) (k2:accessor 's 'a) : stateful 's unit =
  apply_st k1 k2 (fun x -> x)

let import (ext:'a) (k:accessor 's 'b) (f:'a -> 'b) : stateful 's unit =
  fun s -> (), k.put s (f ext)

let export (k:accessor 's 'a) (f:'a -> 'b) : stateful 's 'b =
  fun s -> (f (k.get s)), s

let read #len (k:array_accessor 's 'a len) (i:size_nat{i < len}) : stateful 's 'a =
  fun s -> (k.get s).[i],s

let write #len (k:array_accessor 's 'a len) (i:size_nat{i < len}) (v:'a) =
  fun s -> (),(k.put s ((k.get s).[i] <- v))

let foreach #len (k:array_accessor 's 'a len) (f:i:size_nat{i < len} -> 'a -> stateful 's unit) : stateful 's unit =
  fun s -> (),fold_lefti (fun i a s -> snd (f i a s)) (k.get s) s

#reset-options "--z3rlimit 50"

let foreach_slice #len (k:array_accessor 's 'a len) slen (f:i:size_nat{i < len/slen} -> lseq 'a slen -> stateful 's unit) : stateful 's unit =
  fun s -> let arr = k.get s in
	loop 0 (len/slen) (fun i ->
		    let sl = slice arr (i*slen) ((i+1)*slen) in
		    f i sl) s

let in_place_map2 #len (k1:array_accessor 's 'a len) (k2:array_accessor 's 'b len) (f:'a -> 'b -> 'b) : stateful 's unit =
  apply2_st k1 k2 k2 (map2 f)

let import_slice #len #slice_len (ext:lseq 'a slice_len) (k:array_accessor 's 'b len) min max f =
  fun s -> (), k.put s (update_slice (k.get s) min max (f ext))


let alloc_ref (init:'a) : allocator 'a = fun () -> init
let ref_read #a : stateful a a  = fun s -> (s,s)
let ref_write (v:'a) : stateful 'a unit = fun s -> (),v

let alloc_array (len:size_nat) (init:'a): allocator (lseq 'a len) =
  fun () -> create len init
