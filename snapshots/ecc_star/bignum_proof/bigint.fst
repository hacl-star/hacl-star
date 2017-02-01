(*--build-config
  options:--admit_fsi FStar.Set --admit_fsi Parameters --verify_module Bigint --z3rlimit 5;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst;
  --*)

module Bigint

open FStar.Seq
open FStar.All
open FStar.ST
open FStar.Heap
open FStar.Array
open FStar.Ghost
open IntLib
open Parameters
open UInt

(*** Types ***) 

(* Maps the index of the integer data to the theoretic bit size of the cell *)
type template = nat -> Tot pos
type template_const = t:template{ forall (n:nat). t n = t 0 }
opaque val byte_templ: t:template{forall i. {:pattern (t i)} t i = 8}
let byte_templ = fun x -> 8

(* Big integer types *)
type biginteger (size:pos) = 
  | Bigint: data:array (usint size) -> t:template -> biginteger size
type bigint = b:biginteger platform_size{Bigint.t b = templ }
type bigint_wide = b:biginteger platform_wide{Bigint.t b = templ }
type serialized = b:biginteger 8{Bigint.t b = byte_templ}
type bytes = serialized

#reset-options
(*** Concrete getters ***)
opaque val getRef: #size:pos -> b:biginteger size -> Tot (a:array (usint size){a == Bigint.data b})
let getRef #size b = Bigint.data b

val getRef_lemma: #size:pos -> b:biginteger size -> 
  Lemma (requires (True)) (ensures (getRef b == Bigint.data b)) [SMTPat (getRef b)]
let getRef_lemma #size b = () 

opaque val getTemplate: 
  #size:pos -> b:biginteger size -> Tot (t:template{ t = Bigint.t b })
let getTemplate #size b = Bigint.t b

val getTemplate_lemma: #size:pos -> b:biginteger size ->
  Lemma (requires (True)) (ensures (getTemplate b = Bigint.t b)) [SMTPat (getTemplate b)]
let getTemplate_lemma #size b = 
  let x = getTemplate b in let y = Bigint.t b in cut (True /\ x = y)

#reset-options
(*** Ghost getters ***)
val live: heap -> #size:pos -> biginteger size -> GTot bool
let live h #size b = contains h (getRef b)

opaque val glive_lemma: h:heap -> #size:pos -> b:biginteger size ->
  GLemma unit (requires (True)) (ensures (live h b <==> contains h (getRef b))) []
let glive_lemma h #size b = 
  let x = live h b in let y = contains h (getRef b) in
  cut(x <==> y)

val live_lemma: h:heap -> #size:pos -> b:biginteger size ->
  Lemma (requires (True)) (ensures (live h b <==> contains h (getRef b))) [SMTPat (live h b)]
let live_lemma h #size b = 
  coerce (requires (True)) (ensures (live h b <==> contains h (getRef b))) (fun _ -> glive_lemma h #size b)

val getLength : h:heap -> #size:pos -> b:biginteger size{live h b} -> 
  GTot nat
let getLength h #size b = FStar.Seq.length (sel h (getRef b))

val egetLength : h:heap -> #size:pos -> b:biginteger size{live h b} -> 
  Tot (erased nat)
let egetLength h #size b = hide (FStar.Seq.length (sel h (getRef b)))

opaque val ggetLength_lemma: h:heap -> #size:pos -> b:biginteger size{live h b} ->
  GLemma unit (requires (True)) (ensures (getLength h b = FStar.Seq.length (sel h (getRef b)))) []
let ggetLength_lemma h #size b =
  let x = getLength h b in let y = FStar.Seq.length (sel h (getRef b)) in cut (True /\ x = y)

val getLength_lemma: h:heap -> #size:pos -> b:biginteger size{live h b} ->
  Lemma (requires (True)) (ensures (getLength h b = FStar.Seq.length (sel h (getRef b))))
  [SMTPat (getLength h b)]
let getLength_lemma h #size b =
  coerce (requires (True)) (ensures (getLength h b = FStar.Seq.length (sel h (getRef b)))) (fun _ -> ggetLength_lemma h #size b)
  
val getValue :
  h:heap -> #size:pos -> b:biginteger size{ live h b } -> i:nat{ i < getLength h b } ->
  GTot (usint size)
let getValue h #size b i = FStar.Seq.index (sel h (getRef b)) i

val egetValue :
  h:heap -> #size:pos -> b:biginteger size{ live h b } -> i:nat{ i < getLength h b } ->
  Tot (erased (usint size))
let egetValue h #size b i = hide (FStar.Seq.index (sel h (getRef b)) i)

opaque val ggetValue_lemma:
  h:heap -> #size:pos -> b:biginteger size{ live h b } -> i:nat{ i < getLength h b } ->
  GLemma unit (requires (True)) (ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i)) []  
let ggetValue_lemma h #size b i = 
  let x = getValue h b i in let y = FStar.Seq.index (sel h (getRef b)) i in cut (True /\ x = y)

val getValue_lemma:
  h:heap -> #size:pos -> b:biginteger size{ live h b } -> i:nat{ i < getLength h b } ->
  Lemma (requires (True)) (ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i))
  [SMTPat (getValue h b i)]  
let getValue_lemma h #size b i = 
  coerce (requires (True)) (ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i)) (fun _ -> ggetValue_lemma h #size b i)

#reset-options
(*** Concrete functions ***)
val create:
  word_size:pos -> size:pos -> t:template -> 
  ST (biginteger word_size)
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> 
      (~(live h0 b))
      /\ (live h1 b)
      /\ (modifies !{} h0 h1)
      /\ (sel h1 (getRef b) = FStar.Seq.create size (zero word_size))
      /\ (getTemplate b = t)
    ))
let create word_size size t = 
  Bigint (FStar.Array.create size (zero word_size)) t

val index: 
  #word_size:pos -> b:biginteger word_size -> n:nat -> 
  ST (usint word_size)
     (requires (fun h -> live h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> 
       (h0==h1) /\ (live h1 b) /\ (n < getLength h1 b)
       /\ (modifies !{} h0 h1)
       /\ (getLength h0 #word_size b = getLength h1 #word_size b)
       /\ (v = getValue h0 #word_size b n)
      )) 
let index #word_size b n = 
  FStar.Array.index (getRef #word_size b) n
 
val upd:
  #ws:pos -> b:biginteger ws -> idx:nat -> v:usint ws ->
  ST unit
     (requires (fun h -> (contains h (getRef b))
			 /\ (idx < FStar.Seq.length (sel h (getRef b)))))
     (ensures (fun h0 u h1 -> 
	       (idx < FStar.Seq.length (sel h0 (getRef b)))
               /\ (contains h0 (getRef b))
               /\ (contains h1 (getRef b))
	       /\ (h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx v))
	       /\ (modifies !{getRef b} h0 h1)
	       /\ (getLength h0 b = getLength h1 b)
	       ))
let upd #ws b idx v = 
  FStar.Array.upd (getRef b) idx v

#reset-options

type EqualBigint (#size:pos) (ha:heap) (a:biginteger size) (hb:heap) (b:biginteger size) =
  (live ha a) /\ (live hb b) /\ (getLength ha a = getLength hb b)
  /\ (forall (i:nat). {:pattern (getValue ha a i) \/ (getValue hb b i)} i < getLength ha a ==> v (getValue ha a i) = v (getValue hb b i))
  /\ (getTemplate a = getTemplate b)

(* Abreviation for bigint one can safely compute with *)
type Similar (#size_a:pos) (a:biginteger size_a) (#size_b:pos) (b:biginteger size_b) =
  (getTemplate a = getTemplate b) /\ (Heap.Ref (getRef a) =!= Heap.Ref (getRef b))

type SameFormat (#size:pos) (ha:heap) (hb:heap) (a:biginteger size) (b:biginteger size) = 
  (live ha a) /\ (live hb b) /\ (getTemplate a = getTemplate b) /\ (getLength ha a = getLength hb b)

type EqSub (ha:heap) (#size_a:pos) (a:biginteger size_a) (a_idx:nat) (hb:heap) (#size_b:pos) (b:biginteger size_b) (b_idx:nat) (len:nat) =
  (live ha a) /\ (live hb b)
  /\ (getLength ha a >= a_idx + len) /\ (getLength hb b >= b_idx + len)
  /\ (forall (i:nat). {:pattern (getValue ha a (a_idx+i)) \/ (getValue hb b (b_idx+i))} i < len ==> v (getValue ha a (a_idx+i)) = v (getValue hb b (b_idx+i)))

val copy:
  #size:pos -> a:biginteger size ->
  ST (biginteger size)
     (requires (fun h -> live h a /\ getLength h a > 0))
     (ensures (fun h0 b h1 ->
       (live h0 a)
       /\ (live h1 b)
       /\ ~(live h0 b)
       /\ (EqualBigint #size h0 a h1 b)
       /\ (modifies !{} h0 h1)
     ))
let copy #size a = 
  Bigint (FStar.Array.copy (getRef #size a)) (getTemplate a)

(* Normalized big integer type *)
type Normalized (h:heap) (#size:pos) (b:biginteger size{ live h b })  =
  (forall (n:nat). {:pattern (v (getValue h b n))} n < getLength h b ==> bitsize (v (getValue h b n)) (getTemplate b n))

opaque type IsNull (h:heap) (#size:pos) (b:biginteger size{ live h b }) =
  (forall (n:nat). {:pattern (v (getValue h b n))} n < getLength h b ==> v (getValue h b n) = 0)

#reset-options

val auxiliary_lemma_0: len:nat -> Lemma (requires (True)) (ensures (0+len = len))
let auxiliary_lemma_0 len = ()

opaque val gauxiliary_lemma_2:
  #size:pos -> h:heap -> b:biginteger size{live h b} -> i:nat{i<getLength h b} ->
  GLemma unit (requires (True)) (ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i))	[]
let gauxiliary_lemma_2 #size h b i =
  let x = getValue h b i in
  let y = FStar.Seq.index (sel h (getRef b)) i in
  cut (True /\ x = y)

val auxiliary_lemma_2:
  #size:pos -> h:heap -> b:biginteger size{live h b} -> i:nat{i<getLength h b} ->
  Lemma (requires (True))
	(ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i))
	[SMTPat (FStar.Seq.index (sel h (getRef #size b)) i)]
let auxiliary_lemma_2 #size h b i =
  coerce (requires (True)) (ensures (getValue h b i == FStar.Seq.index (sel h (getRef b)) i)) (fun _ -> gauxiliary_lemma_2 #size h b i)

opaque val gauxiliary_lemma_3:
  #size:pos -> h:heap -> b:biginteger size{live h b} ->
  GLemma unit (requires (True)) (ensures (forall (i:nat). i < getLength h b ==> getValue h b i == FStar.Seq.index (sel h (getRef b)) i)) []
let gauxiliary_lemma_3 #size h b =
  let l = getLength h b in
  let seq = sel h (getRef b) in
  cut (forall (i:nat). i < getLength h b ==> FStar.Seq.index seq i == FStar.Seq.index (sel h (getRef b)) i);
  cut (forall (i:nat). i < getLength h b ==> FStar.Seq.index seq i == getValue h b i)

val auxiliary_lemma_3:
  #size:pos -> h:heap -> b:biginteger size{live h b} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). i < getLength h b ==> getValue h b i == FStar.Seq.index (sel h (getRef b)) i))
let auxiliary_lemma_3 #size h b =
 coerce (requires (True)) (ensures (forall (i:nat). i < getLength h b ==> getValue h b i == FStar.Seq.index (sel h (getRef b)) i)) (fun _ -> gauxiliary_lemma_3 #size h b)

#reset-options

val auxiliary_lemma_1: 
  #size:pos -> h0:heap -> h1:heap -> a:biginteger size -> b:biginteger size -> len:pos ->
  Lemma 
    (requires ((contains h0 (getRef a))
	       /\ (contains h0 (getRef b))
	       /\ (contains h1 (getRef b))
	       /\ (FStar.Seq.length (sel h0 (getRef a)) >= len)
	       /\ (FStar.Seq.length (sel h0 (getRef b)) >= len)
	       /\ (FStar.Seq.length (sel h1 (getRef b)) = FStar.Seq.length (sel h0 (getRef b)))
	       /\ (forall (i:nat). i < len ==> 
		   v (Seq.index (sel h0 (getRef a)) (0+i)) = v (Seq.index (sel h1 (getRef b)) (0+i)))
	       /\ (forall (i:nat). (i < Seq.length (sel h1 (getRef b)) /\ (i < 0 \/ i >= 0 + len)) ==>
		   (Seq.index (sel h1 (getRef b)) i == Seq.index (sel h0 (getRef b)) i))
     ))
     (ensures (live h1 b /\ getLength h1 b >= len
               /\ EqSub h0 a 0 h1 b 0 len /\ EqSub h0 b len h1 b len (getLength h1 b - len)))
let auxiliary_lemma_1 #size h0 h1 a b len = 
//  admit();
  live_lemma h0 #size b;
  live_lemma h1 #size b;
  live_lemma h0 #size a;  
  getLength_lemma h1 #size b;
  getLength_lemma h0 #size b;
  getLength_lemma h0 #size a;	  
  cut (live h0 a /\ live h1 b);
  auxiliary_lemma_0 len;
  cut (getLength h0 a >= 0 + len /\ getLength h1 b >= 0 + len); 
  cut (forall (i:nat). i < len ==> i < getLength h0 a);
  cut (forall (i:nat). i < len ==> i < getLength h0 b);
  cut (forall (i:nat). i < len ==> i < getLength h1 b);
  auxiliary_lemma_3 #size h0 a;
  auxiliary_lemma_3 #size h0 b;
  auxiliary_lemma_3 #size h1 b

#reset-options

val blit:
  #size:pos -> a:biginteger size -> b:biginteger size{Similar a b} -> len:pos ->
  ST unit
    (requires (fun h -> 
      (live h a) /\ (live h b) /\ (len <= getLength h a) /\ (len <= getLength h b)
      ))
    (ensures (fun h0 _ h1 ->
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b) /\ (len <= getLength h0 a)
      /\ (len <= getLength h0 b) /\ (getLength h0 b = getLength h1 b)
      /\ (getLength h1 a = getLength h0 a) /\ (modifies !{getRef b} h0 h1)
      /\ (EqSub h0 a 0 h1 b 0 len) /\ (EqSub h0 b len h1 b len (getLength h1 b - len))
      ))
let blit #w a b len =
  let h0 = ST.get() in
  let (ref_b:ref (FStar.Seq.seq (usint w))) = getRef #w b in
  let (ref_a:ref (FStar.Seq.seq (usint w))) = getRef #w a in
  let h = ST.get() in
  cut (live h a /\ live h b);
  live_lemma h #w b;
  live_lemma h #w a;
  cut (True /\ ref_b <> ref_a);
  getLength_lemma h #w b;
  getLength_lemma h #w a;
  cut (True /\ Seq.length (sel h ref_a) >= len);
  cut (True /\ Seq.length (sel h ref_b) >= len);
  FStar.Array.blit (ref_a) 0 (ref_b) 0 len;
  let h1 = ST.get() in 
  live_lemma h1 #w b;
  live_lemma h1 #w a;  
  getLength_lemma h1 #w b;
  getLength_lemma h1 #w a;	  
  auxiliary_lemma_0 len;
  cut(getLength h0 a >= 0 + len /\ getLength h1 b >= 0 + len);
  auxiliary_lemma_1 #w h0 h1 a b len

opaque type Standardized (h:heap) (#size:pos) (b:biginteger size) =
  live h b /\ getLength h b >= norm_length /\ getTemplate b = templ
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> bitsize (v (getValue h b i)) (getTemplate b i))

opaque type Filled (h:heap) (#size:pos) (b:biginteger size) (min:pos) (max:pos{max <= size}) =
  live h b /\ getLength h b >= norm_length /\ getTemplate b = templ /\ 
  (forall (i:nat). {:pattern (v (getValue h b i))} i < norm_length ==> (pow2 min <= v (getValue h b i) /\ v (getValue h b i) < pow2 max))

(* Concrete functions *)
val create_limb:
  size:pos -> 
  ST bigint
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> 
      (~(live h0 b))
      /\ (live h1 b)
      /\ (modifies !{} h0 h1)
      /\ (sel h1 (getRef b) = FStar.Seq.create size (zero_limb))
      /\ (getTemplate b = templ)
    ))
let create_limb size = Bigint (FStar.Array.create size (zero_limb)) templ

val create_wide:
  size:pos -> 
  ST bigint_wide
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> 
      (~(live h0 b))
      /\ (live h1 b)
      /\ (modifies !{} h0 h1)
      /\ (sel h1 (getRef b) = FStar.Seq.create size zero_wide)
    ))
let create_wide size = Bigint (FStar.Array.create size zero_wide) templ

val create_wide_templ: size:pos -> t:template -> ST (biginteger platform_wide)
  (requires (fun h -> True))
  (ensures (fun h0 b h1 -> ~(live h0 b) /\ live h1 b /\ modifies !{} h0 h1
			 /\ sel h1 (getRef b) = FStar.Seq.create size zero_wide
			 /\ getTemplate b = t))
let create_wide_templ size t = Bigint (FStar.Array.create size zero_wide) t			 

val index_byte: 
  b:bytes -> n:nat -> 
  ST byte
     (requires (fun h -> live h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> 
       (h0==h1) /\ (live h0 b) /\ (live h1 b) /\ (n < getLength h1 b)
       /\ (modifies !{} h0 h1)
       /\ (getLength h0 b = getLength h1 b)
       /\ (v = getValue h0 b n)
      )) 
let index_byte b n = 
  FStar.Array.index (getRef b) n

val index_limb: 
  b:bigint -> n:nat -> 
  ST limb
     (requires (fun h -> live h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> 
       (h0==h1) /\ (live h0 b) /\ (live h1 b) /\ (n < getLength h1 b)
       /\ (modifies !{} h0 h1)
       /\ (getLength h0 b = getLength h1 b)
       /\ (v = getValue h0 b n)
      )) 
let index_limb b n = 
  FStar.Array.index (getRef b) n

val index_wide: 
  b:biginteger platform_wide -> n:nat -> 
  ST wide
     (requires (fun h -> live h b /\ n < getLength h b))
     (ensures (fun h0 v h1 -> 
       (h0==h1) /\ (live h0 b) /\ (live h1 b) /\ (n < getLength h1 b)
       /\ (modifies !{} h0 h1)
       /\ (getLength h0 b = getLength h1 b)
       /\ (v = getValue h0 b n)
      )) 
let index_wide b n = 
  FStar.Array.index (getRef b) n

val upd_limb:
  b:bigint -> idx:nat -> v:limb ->
  ST unit
     (requires (fun h -> (contains h (getRef b))
			 /\ (idx < FStar.Seq.length (sel h (getRef b)))))
     (ensures (fun h0 u h1 -> 
	       (idx < FStar.Seq.length (sel h0 (getRef b)))
               /\ (contains h0 (getRef b))
               /\ (contains h1 (getRef b))
	       /\ (h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx v))
	       /\ (modifies !{getRef b} h0 h1)
	       /\ (getLength h0 b = getLength h1 b)
	       ))
let upd_limb b idx v = 
  FStar.Array.upd (getRef b) idx v

(* val upd_wide: *)
(*   b:bigint_wide -> idx:nat -> v:wide -> *)
(*   ST unit *)
(*      (requires (fun h -> (contains h (getRef b)) *)
(* 			 /\ (idx < FStar.Seq.length (sel h (getRef b))))) *)
(*      (ensures (fun h0 u h1 ->  *)
(* 	       (idx < FStar.Seq.length (sel h0 (getRef b))) *)
(*                /\ (contains h0 (getRef b)) *)
(*                /\ (contains h1 (getRef b)) *)
(* 	       /\ (h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx v)) *)
(* 	       /\ (modifies !{getRef b} h0 h1) *)
(* 	       /\ (getLength h0 b = getLength h1 b) *)
(* 	       )) *)
(* let upd_wide b idx v =  *)
(*   FStar.Array.upd (getRef b) idx v *)

val upd_wide:
  b:biginteger platform_wide -> idx:nat -> v:wide ->
  ST unit
     (requires (fun h -> (contains h (getRef b)) /\ (idx < FStar.Seq.length (sel h (getRef b)))))
     (ensures (fun h0 u h1 -> 
	       (idx < FStar.Seq.length (sel h0 (getRef b)))
               /\ (contains h0 (getRef b)) /\ (contains h1 (getRef b))
	       /\ (h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx v))
	       /\ (modifies !{getRef b} h0 h1)
	       /\ (getLength h0 b = getLength h1 b) ))
let upd_wide b idx v = FStar.Array.upd (getRef b) idx v


#reset-options

val upd_lemma:
  h0:heap -> h1:heap -> #size:pos -> b:biginteger size -> idx:nat -> x:usint size -> 
  Lemma
    (requires (live h0 b /\ live h1 b /\ idx < getLength h1 b 
      /\ getLength h1 b = getLength h0 b
      /\ h1==Heap.upd h0 (getRef b) (FStar.Seq.upd (sel h0 (getRef b)) idx x)))
    (ensures (
      live h0 b /\ live h1 b 
      /\ getLength h1 b = getLength h0 b
      /\ idx < getLength h1 b
      /\ (forall (i:nat{ i <> idx /\ i < getLength h1 b}). getValue h1 b i == getValue h0 b i)
      /\ v (getValue h1 b idx) = v x))
let upd_lemma h0 h1 #size b idx x = ()

val no_upd_lemma: h0:heap -> h1:heap -> #size:pos -> b:biginteger size -> mods:FStar.Set.set aref ->
  Lemma
    (requires (live h0 b /\ modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
    (ensures (
      live h0 b /\ live h1 b 
      /\ getLength h0 b = getLength h1 b
      /\ (forall (i:nat{i < getLength h1 b}). {:pattern (getValue h1 b i)} getValue h1 b i == getValue h0 b i)))
let no_upd_lemma h0 h1 #size b mods = ()

val blit_limb:
  a:bigint -> b:bigint{Similar a b} -> len:pos ->
  ST unit
    (requires (fun h -> 
      (live h a) /\ (live h b) /\ (len <= getLength h a) /\ (getLength h b >= len)
      ))
    (ensures (fun h0 _ h1 ->
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b) /\ (len <= getLength h0 a)
      /\ (getLength h0 b >= len) /\ (getLength h0 b = getLength h1 b)
      /\ (getLength h1 a = getLength h0 a) /\ (modifies !{getRef b} h0 h1)
      /\ (EqSub h0 a 0 h1 b 0 len) /\ (EqSub h0 b len h1 b len (getLength h1 b - len))
      ))
let blit_limb a b len =
  let h0 = ST.get() in
  let ref_b = getRef b in
  let ref_a = getRef a in
  let h = ST.get() in
  cut (live h a /\ live h b);
  live_lemma h b;
  live_lemma h a;
  cut (True /\ ref_b <> ref_a);
  getLength_lemma h b;
  getLength_lemma h a;
  cut (True /\ Seq.length (sel h ref_a) >= len);
  cut (True /\ Seq.length (sel h ref_b) >= len);
  FStar.Array.blit (ref_a) 0 (ref_b) 0 len;
  let h1 = ST.get() in 
  live_lemma h1 b;
  live_lemma h1 a;  
  getLength_lemma h1 b;
  getLength_lemma h1 a;	  
  auxiliary_lemma_0 len;
  cut(getLength h0 a >= 0 + len /\ getLength h1 b >= 0 + len);
  auxiliary_lemma_1 h0 h1 a b len

val blit_wide:
  a:bigint_wide -> b:bigint_wide{Similar a b} -> len:pos ->
  ST unit
    (requires (fun h -> 
      (live h a) /\ (live h b) /\ (len <= getLength h a) /\ (getLength h b >= len)
      ))
    (ensures (fun h0 _ h1 ->
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b) /\ (len <= getLength h0 a)
      /\ (getLength h0 b >= len) /\ (getLength h0 b = getLength h1 b)
      /\ (getLength h1 a = getLength h0 a) /\ (modifies !{getRef b} h0 h1)
      /\ (EqSub h0 a 0 h1 b 0 len) /\ (EqSub h0 b len h1 b len (getLength h1 b - len))
      ))
let blit_wide a b len =
  let h0 = ST.get() in
  let ref_b = getRef b in
  let ref_a = getRef a in
  let h = ST.get() in
  cut (live h a /\ live h b);
  live_lemma h b;
  live_lemma h a;
  cut (True /\ ref_b <> ref_a);
  getLength_lemma h b;
  getLength_lemma h a;
  cut (True /\ Seq.length (sel h ref_a) >= len);
  cut (True /\ Seq.length (sel h ref_b) >= len);
  FStar.Array.blit (ref_a) 0 (ref_b) 0 len;
  let h1 = ST.get() in 
  live_lemma h1 b;
  live_lemma h1 a;  
  getLength_lemma h1 b;
  getLength_lemma h1 a;	  
  auxiliary_lemma_0 len;
  cut(getLength h0 a >= 0 + len /\ getLength h1 b >= 0 + len);
  auxiliary_lemma_1 h0 h1 a b len
