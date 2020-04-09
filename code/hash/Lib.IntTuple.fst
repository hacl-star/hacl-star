module Lib.IntTuple

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple

#set-options "--z3rlimit 100"
let funit (i:nat) = unit
let ntuple_to_bytes_be (#t:inttype{unsigned t}) (#l:secrecy_level) (#len:flen) (s:ntuple (uint_t t l) len) : Lib.ByteSequence.lbytes_l l (numbytes t * len) =
    assert_norm (len * numbytes t < pow2 32);
    let _, o = normalize_term (Lib.Sequence.generate_blocks (numbytes t) len len funit
		(fun i u -> (),Lib.ByteSequence.uint_to_bytes_be #t #l s.(|i|)) ()) in
    o

let ntuple_to_bytes_le (#t:inttype{unsigned t}) (#l:secrecy_level) (#len:flen) (s:ntuple (uint_t t l) len) : Lib.ByteSequence.lbytes_l l (numbytes t * len) =
    assert_norm (len * numbytes t < pow2 32);
    let _, o = normalize_term (Lib.Sequence.generate_blocks (numbytes t) len len funit
		(fun i u -> (),Lib.ByteSequence.uint_to_bytes_le #t #l s.(|i|)) ()) in
    o

let ntuple_from_bytes_be (#t:inttype{unsigned t /\ t <> U1}) (#l:secrecy_level) (#len:flen) (b:Lib.ByteSequence.lbytes_l l (numbytes t * len)) : (s:ntuple (uint_t t l) len) =
    normalize_term (createi #(uint_t t l) len
      (fun i -> Lib.ByteSequence.uint_from_bytes_be (Lib.Sequence.sub b (i * numbytes t) (numbytes t))))

let ntuple_from_bytes_le (#t:inttype{unsigned t /\ t <> U1}) (#l:secrecy_level) (#len:flen) (b:Lib.ByteSequence.lbytes_l l (numbytes t * len)) : (s:ntuple (uint_t t l) len) =
    normalize_term (createi #(uint_t t l) len
      (fun i -> Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b (i * numbytes t) (numbytes t))))

inline_for_extraction
let (+|) #t #l #len = map2 #(uint_t t l) #(uint_t t l) #(uint_t t l) #len ( +. )

inline_for_extraction
let ( *| ) (#t:inttype{unsigned t /\ t <> U128}) #l #len = map2 #(uint_t t l) #(uint_t t l) #(uint_t t l) #len ( *. )

inline_for_extraction
let (-|) #t #l #len = map2 #(uint_t t l) #(uint_t t l) #(uint_t t l) #len ( -. )

inline_for_extraction
let (^|) #t #l #len = map2 #(uint_t t l) #(uint_t t l) #(uint_t t l) #len ( ^. )

inline_for_extraction
let (&|) #t #l #len = map2 #(uint_t t l) #(uint_t t l) #(uint_t t l) #len ( &. )

inline_for_extraction
let (~|) #t #l #len = map #(uint_t t l) #(uint_t t l) #len ( ~. )

inline_for_extraction
let (>>>|) #t #l #len x r  = map #(uint_t t l) #(uint_t t l) #len ( fun i -> i >>>. r ) x

inline_for_extraction
let (>>|) #t #l #len x r  = map #(uint_t t l) #(uint_t t l) #len ( fun i -> i >>. r ) x

inline_for_extraction
let (<<<|) #t #l #len x r  = map #(uint_t t l) #(uint_t t l) #len ( fun i -> i <<<. r ) x

inline_for_extraction
let (<<|) #t #l #len x r  = map #(uint_t t l) #(uint_t t l) #len ( fun i -> i <<. r ) x

