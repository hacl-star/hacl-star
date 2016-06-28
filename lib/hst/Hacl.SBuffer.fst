module Hacl.SBuffer

open FStar.UInt32
open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

#set-options "--lax"

let u8  = UInt8.t
let u32 = UInt32.t
let u64 = UInt64.t

private type buffer (a:Type) = buffer a

private type _u8s  = buffer u8
private type _u32s = buffer u32
private type _u64s = buffer u64

type u8s  = _u8s
type u32s = _u32s
type u64s = _u64s

let contains #a h (b:buffer a) = contains #a h b
let sel #a h (b:buffer a{contains h b}) = sel #a h b
let max_length #a h (b:buffer a{contains h b}) = max_length #a h b
let length #a (b:buffer a) = length #a b
let length' #a (b:buffer a) = length' #a b
let idx #a (b:buffer a) = idx #a b
let content #a (b:buffer a) = content #a b
let as_ref #a (b:buffer a) = as_ref #a b
let as_aref #a (b:buffer a) = as_aref #a b
let frameOf #a (b:buffer a) = frameOf #a b

(* Liveness condition, necessary for any computation on the buffer *)
let live #a (h:mem) (b:buffer a) = live #a h b

let getValue #a h (b:buffer a{live h b}) (i:nat{i<max_length h b}) = getValue #a h b
let get #a h (b:buffer a{live h b}) (i:nat{i < length b}) = get #a h b i
let as_seq #a h (b:buffer a{live h b}) = as_seq #a h b
let equal #a h (b:buffer a) h' (b':buffer a) = equal #a h b h' b'

let eq_lemma #a h b h' b' = eq_lemma #a h b h' b'

(* y is included in x / x contains y *)
let includes #a (x:buffer a) (y:buffer a) : GTot Type0 = includes #a x y

let disjoint #a #a' (x:buffer a) (y:buffer a') : GTot Type0 = disjoint #a #a' x y

(* Abstraction of buffers of any type *)
let empty : Set.set abuffer = empty
let only #t (b:buffer t) : Tot (Set.set abuffer) = only #t b
let op_Plus_Plus #a s (b:buffer a) : Tot (Set.set abuffer) = op_Plus_Plus #a s b
let op_Plus_Plus_Plus set1 set2 : Tot (Set.set abuffer) = op_Plus_Plus_Plus set1 set2

(* Maps a set of buffer to the set of their references *)
let arefs s = arefs s

let disjointSet #a (b:buffer a) (bufs:Set.set abuffer) = disjointSet #a b bufs

let modifies_buf rid buffs h h' = modifies_buf rid buffs h h'

let disjoint_only_lemma #t #t' b b' = disjoint_only_lemma #t #t' b b'

let modifies_trans #rid bufs h0 h1 h2 = modifies_trans #rid bufs h0 h1 h2

let modifies_sub rid bufs subbufs h0 h1 = modifies_sub rid bufs subbufs h0 h1

let modifies_none h = modifies_none h

let modifies_fresh #a h0 h1 bufs b = modifies_fresh #a h0 h1 bufs b

let modifies_0 h0 h1 = modifies_0 h0 h1

let modifies_1 (#a:Type) (b:buffer a) h0 h1 = modifies_1 #a b h0 h1

let modifies_2 (#a:Type) (#a':Type) (b:buffer a) (b':buffer a') h0 h1 = modifies_2 #a #a' b b' h0 h1

let modifies_region rid bufs h0 h1 = modifies_region rid bufs h0 h1

(** Concrete getters and setters **)
let create #a (init:a) (len:u32) : ST (buffer a)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 -> ~(contains h0 b)
       /\ live h1 b /\ idx b = 0 /\ length b = v len /\ frameOf b = h0.tip
       /\ modifies_region h1.tip Set.empty h0 h1
       /\ sel h1 b = Seq.create (v len) init
       ))
  = create #a init len

let index #a (b:buffer a) (n:u32{v n<length b}) : STL a
     (requires (fun h -> live h b))
     (ensures (fun h0 z h1 -> live h0 b /\ h1 == h0 /\ z == get h0 b (v n) ))
  = index #a b n

val upd: #a:Type -> b:buffer a -> n:u32 -> z:a -> STL unit
  (requires (fun h -> live h b /\ v n < length b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ v n < length b
    /\ modifies_1 b h0 h1
    /\ sel h1 b = Seq.upd (sel h0 b) (idx b + v n) z))
let upd #a b n z = upd #a b n z

(* Could be made Total with a couple changes in the spec *)
let sub #a (b:buffer a) (i:u32) (len:u32{v len <= length b /\ v i + v len <= length b}) : STL (buffer a)
     (requires (fun h -> live h b))
     (ensures (fun h0 b' h1 -> content b = content b' /\ idx b' = idx b + v i /\ length b' = v len /\ (h0 == h1)))
  = sub #a b i len

let offset #a (b:buffer a) (i:u32{v i <= length b}) : STL (buffer a)
  (requires (fun h -> live h b))
  (ensures (fun h0 b' h1 -> content b' = content b /\ idx b' = idx b + v i /\ length b' = length b - v i
    /\ h0 == h1))
  = offset #a b i

val blit: #t:Type -> a:buffer t -> idx_a:u32{v idx_a <= length a} -> b:buffer t{disjoint a b} ->
  idx_b:u32{v idx_b <= length b} -> len:u32{v idx_a+v len <= length a /\ v idx_b+v len <= length b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h0 a /\ live h1 b /\ live h1 a
      /\ (forall (i:nat). {:pattern (get h1 b (v idx_b+i))} i < v len ==> get h1 b (v idx_b+i) = get h0 a (v idx_a+i))
      /\ (forall (i:nat). {:pattern (get h1 b i)} ((i >= v idx_b + v len /\ i < length b) \/ i < v idx_b) ==> get h1 b i = get h0 b i)
      /\ modifies_1 b h0 h1 ))
let blit #t a idx_a b idx_b len = blit #t a idx_a b idx_b len

val upd_lemma: #t:Type -> ha:mem -> hb:mem -> a:buffer t -> ctr:u32 -> x:t -> Lemma (True)
val no_upd_lemma: #t:Type -> ha:mem -> hb:mem -> a:buffer t -> bufs:(Set.set abuffer) -> Lemma (True)
let upd_lemma #t ha hb a ctr x = ()
let no_upd_lemma #t ha hb a bufs = ()

val no_upd_lemma_1: #t:Type -> #t':Type -> h0:mem -> h1:mem -> a:buffer t -> b:buffer t' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ modifies_1 a h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_1 a h0 h1); SMTPat (live h0 b); SMTPat (disjoint a b)]
let no_upd_lemma_1 #t #t' h0 h1 a b = no_upd_lemma_1 #t #t' h0 h1 a b

val no_upd_lemma_2: #t:Type -> #t':Type -> #t'':Type -> h0:mem -> h1:mem -> a:buffer t -> a':buffer t' -> b:buffer t'' -> Lemma
  (requires (live h0 b /\ disjoint a b /\ disjoint a' b /\ modifies_2 a a' h0 h1))
  (ensures  (live h0 b /\ live h1 b /\ equal h0 b h1 b))
  [SMTPat (modifies_1 a h0 h1); SMTPat (live h0 b); SMTPat (disjoint a b)]
let no_upd_lemma_2 #t #t' #t'' h0 h1 a a' b = no_upd_lemma_2 #t #t' #t'' h0 h1 a a' b
