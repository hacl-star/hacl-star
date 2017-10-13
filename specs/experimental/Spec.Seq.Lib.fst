module Spec.Seq.Lib

open FStar.Seq
open FStar.Mul
open FStar.UInt

module U8 = FStar.UInt8
module U32 = FStar.UInt32
open U32

type seq 'a = s:Seq.seq 'a{length s < pow2 32}
type byte = UInt8.t
type bytes = seq byte
type lseq 'a n = s:seq 'a{length s = U32.v n}
type lbytes n = s:bytes{length s = U32.v n}

val create: #a:Type -> sz:U32.t -> v:a -> s:seq a{length s = U32.v sz}
let create #a s v = Seq.create #a (U32.v s) v

val upd: #a:Type -> s:seq a -> i:U32.t{U32.v i < length s} -> 
	 v:a -> s':seq a{length s' = length s}
let upd #a s i v = Seq.upd #a s (U32.v i) v

val index: #a:Type -> s:seq a -> i:U32.t{U32.v i < length s} -> a
let index #a s i = Seq.index #a s (U32.v i)

let op_String_Access = index
let op_String_Assignment = upd

val slice: #a:Type -> s:seq a -> i:U32.t -> j:U32.t{U32.v i <= U32.v j /\ U32.v j <= length s} -> t:seq a {length t = U32.v j - U32.v i}
let slice #a s i j = Seq.slice #a s (U32.v i) (U32.v j)

val seq_length: #a:Type -> s:seq a -> r:U32.t{U32.v r = length s}
let seq_length (#a:Type) (s:seq a) = U32.uint_to_t (length s)

val blit: #a:Type ->
	s1:seq a -> ind_s1:U32.t{U32.v ind_s1 <= length s1} ->
	s2:seq a -> ind_s2:U32.t{U32.v ind_s2 <= length s2} ->
	len:U32.t{U32.v ind_s1 + U32.v len <= length s1 /\ 
		  U32.v ind_s2 + U32.v len <= length s2} ->
	Tot (res:seq a{length res = length s2}) 

#reset-options "--z3rlimit 30"

let blit #a s1 ind_s1 s2 ind_s2 len =
    let t1 = slice s2 0ul ind_s2 in
    let t3 = slice s2 (ind_s2 +^ len) (seq_length s2)  in
    let f2 = slice s1 ind_s1 (ind_s1 +^ len)  in
    t1 @| f2 @| t3

val update_slice: #a:Type -> s:seq a -> i:U32.t -> l:U32.t{U32.v i + U32.v l <= length s} -> 
		  f: (s:lseq a l -> s:lseq a l) -> Tot (r:seq a{length r = length s})
let update_slice #a s i l f = 
    let s1 = slice s 0ul i in
    let s2 = slice s i (i +^ l) in
    let s3 = slice s (i +^ l) (seq_length s) in
    s1 @| (f s2) @| s3