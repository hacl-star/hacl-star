module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 30 --max_fuel 0 --max_ifuel 0"

/// Definition of byte-based sequences

unfold inline_for_extraction
type bytes_l (l:secrecy_level) = seq (uint_t U8 l)

unfold inline_for_extraction
type lbytes_l (l:secrecy_level) (len:size_nat) = lseq (uint_t U8 l) len

unfold inline_for_extraction let bytes = bytes_l SEC
unfold inline_for_extraction let lbytes (len:size_nat) = lbytes_l SEC len
unfold inline_for_extraction let pub_bytes = bytes_l PUB
unfold inline_for_extraction let pub_lbytes (len:size_nat) = lbytes_l PUB len

(** Construct the equality mask for a pair of secret integer sequences *)
val seq_eq_mask: #t:inttype{~(S128? t)} -> #len1:size_nat -> #len2:size_nat
  -> b1:lseq (int_t t SEC) len1
  -> b2:lseq (int_t t SEC) len2
  -> len:size_nat{len <= len1 /\ len <= len2}
  -> res:int_t t SEC{
      (sub b1 0 len == sub b2 0 len  ==> v res == v (ones t SEC)) /\
      (sub b1 0 len =!= sub b2 0 len ==> v res == v (zeros t SEC))}

(** Compares two byte sequences and declassifies the result *)
inline_for_extraction
val lbytes_eq: #len:size_nat -> b1:lbytes len -> b2:lbytes len -> b:bool{b <==> b1 == b2}

inline_for_extraction
val mask_select: #t:inttype{~(S128? t)} -> mask:int_t t SEC -> a:int_t t SEC -> b:int_t t SEC -> int_t t SEC

val mask_select_lemma: #t:inttype{~(S128? t)} -> mask:int_t t SEC -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (requires v mask = 0 \/ v mask = v (ones t SEC))
  (ensures  mask_select mask a b == (if v mask = 0 then b else a))

val seq_mask_select: #t:inttype{~(S128? t)} -> #len:size_nat
  -> a:lseq (int_t t SEC) len
  -> b:lseq (int_t t SEC) len
  -> mask:int_t t SEC
  -> Pure (lseq (int_t t SEC) len)
    (requires v mask = 0 \/ v mask = v (ones t SEC))
    (ensures  fun res -> res == (if v mask = 0 then b else a))

/// Constant for empty lbytes


let bytes_empty: bytes = Seq.Base.empty


let lbytes_empty: lbytes 0 = create 0 (u8 0)

/// Conversions between natural numbers and sequences

inline_for_extraction
val nat_from_intseq_be: #t:inttype{unsigned t} -> #l:secrecy_level -> b:seq (uint_t t l)
  -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
val nat_from_intseq_le: #t:inttype{unsigned t} -> #l:secrecy_level
  -> b:seq (uint_t t l) -> n:nat{n < pow2 (length b * bits t)}

inline_for_extraction
let nat_from_bytes_be (#l:secrecy_level) (b:bytes_l l) : n:nat{n < pow2 (length b * 8)} =
  nat_from_intseq_be #U8 #l b

inline_for_extraction
let nat_from_bytes_le (#l:secrecy_level) (b:bytes_l l) : n:nat{n < pow2 (length b * 8)} =
  nat_from_intseq_le #U8 #l b

inline_for_extraction
val nat_to_intseq_be: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> n:nat{n < pow2 (bits t * len)} ->
  b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_be b}

inline_for_extraction
val nat_to_intseq_le: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> n:nat{n < pow2 (bits t * len)} ->
  b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_le b}

val index_nat_to_intseq_le:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> len:size_nat
  -> n:nat{n < pow2 (bits t * len)}
  -> i:nat{i < len}
  -> Lemma (Seq.index (nat_to_intseq_le #t #l len n) i ==
           uint #t #l (n / pow2 (bits t * i) % pow2 (bits t)))

val index_nat_to_intseq_be:
    #t:inttype{unsigned t}
  -> #l:secrecy_level
  -> len:size_nat
  -> n:nat{n < pow2 (bits t * len)}
  -> i:nat{i < len}
  -> Lemma (Seq.index (nat_to_intseq_be #t #l len n) (len - i - 1) ==
           uint #t #l (n / pow2 (bits t * i) % pow2 (bits t)))

inline_for_extraction
let nat_to_bytes_be (#l:secrecy_level) (len:nat) (n:nat{n < pow2 (8 * len)}) : b:bytes_l l{length b == len /\ n == nat_from_intseq_be #U8 b} =
  nat_to_intseq_be #U8 #l len n

inline_for_extraction
let nat_to_bytes_le (#l:secrecy_level) (len:nat) (n:nat{n < pow2 (8 * len)}) : b:bytes_l l{length b == len /\ n == nat_from_intseq_le #U8 b} =
  nat_to_intseq_le #U8 #l len n

inline_for_extraction
val uint_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> uint_t t l -> lbytes_l l (numbytes t)

val index_uint_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_le #t #l u) i ==
                              uint #U8 #l (v u / pow2 (8 * i) % pow2 8))

inline_for_extraction
val uint_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l -> lbytes_l l (numbytes t)

val index_uint_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> u:uint_t t l
  -> Lemma
    (forall (i:nat{i < numbytes t}). index (uint_to_bytes_be #t #l u) (numbytes t - i - 1) ==
                              uint #U8 #l (v u / pow2 (8 * i) % pow2 8))

inline_for_extraction
val uint_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> b:lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uint_from_bytes_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> lbytes_l l (numbytes t) -> uint_t t l

inline_for_extraction
val uints_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

val index_uints_to_bytes_le: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> ul:lseq (uint_t t l) len -> i:nat{i < len * numbytes t}
  -> Lemma (index (uints_to_bytes_le #t #l #len ul) i == (uint_to_bytes_le ul.[i / numbytes t]).[i % numbytes t])

inline_for_extraction
val uints_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len -> lbytes_l l (len * numbytes t)

val index_uints_to_bytes_be: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> ul:lseq (uint_t t l) len -> i:nat{i < len * numbytes t}
  -> Lemma (index (uints_to_bytes_be #t #l #len ul) i == (uint_to_bytes_be ul.[i / numbytes t]).[i % numbytes t])

inline_for_extraction
val uints_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len

val index_uints_from_bytes_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:size_nat{i < len}
  -> Lemma (index (uints_from_bytes_le #t #l #len b) i == uint_from_bytes_le (sub b (i * numbytes t) (numbytes t)))

inline_for_extraction
val uints_from_bytes_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> lbytes_l l (len * numbytes t) -> lseq (uint_t t l) len

val index_uints_from_bytes_be: #t:inttype{unsigned t /\ ~(t == U1)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:size_nat{i < len}
  -> Lemma (index (uints_from_bytes_be #t #l #len b) i == uint_from_bytes_be (sub b (i * numbytes t) (numbytes t)))

inline_for_extraction
val uint_at_index_le: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t)
  -> idx:nat{idx < len}
  -> u:uint_t t l{u == (uints_from_bytes_le #t #l #len b).[idx]}

inline_for_extraction
val uint_at_index_be: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t)
  -> idx:nat{idx < len}
  -> u:uint_t t l{u == (uints_from_bytes_be #t #l #len b).[idx]}

val nat_from_intseq_le_lemma0: #t:inttype{unsigned t} -> #l:secrecy_level -> b:lseq (uint_t t l) 1 ->
  Lemma (nat_from_intseq_le b == uint_v b.[0])

val nat_from_intseq_le_slice_lemma: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat
  -> b:lseq (uint_t t l) len -> i:nat{i <= len} ->
  Lemma (nat_from_intseq_le b == nat_from_intseq_le (slice b 0 i) + pow2 (i * bits t) * nat_from_intseq_le (slice b i len))

val nat_from_intseq_be_lemma0: #t:inttype{unsigned t} -> #l:secrecy_level -> b:lseq (uint_t t l) 1 ->
  Lemma (nat_from_intseq_be b == uint_v b.[0])

val nat_from_intseq_be_slice_lemma: #t:inttype{unsigned t} -> #l:secrecy_level -> #len:size_nat
  -> b:lseq (uint_t t l) len -> i:nat{i <= len} ->
  Lemma (nat_from_intseq_be b == nat_from_intseq_be (slice b i len) + pow2 ((len - i) * bits t) * nat_from_intseq_be (slice b 0 i))

val uints_from_bytes_le_slice_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_pos{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) -> i:nat -> j:nat{i <= j /\ j <= len} ->
  Lemma (slice (uints_from_bytes_le #t #l #len b) i j == uints_from_bytes_le #t #l #(j-i) (slice b (i * numbytes t) (j * numbytes t)))

val uints_from_bytes_le_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_le (uints_from_bytes_le #t #l #len b) == nat_from_bytes_le b)

val uints_from_bytes_be_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_be (uints_from_bytes_be #t #l #len b) == nat_from_bytes_be b)

val uints_to_bytes_le_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> len:nat{len * numbytes t < pow2 32}
  -> n:nat{n < pow2 (bits t * len)}
  -> Lemma
    (uints_to_bytes_le #t #l #len (nat_to_intseq_le #t #l len n) ==
     nat_to_bytes_le (len * numbytes t) n)

val uints_to_bytes_be_nat_lemma: #t:inttype{unsigned t /\ ~(U1? t)} -> #l:secrecy_level
  -> len:nat{len * numbytes t < pow2 32}
  -> n:nat{n < pow2 (bits t * len)}
  -> Lemma
    (uints_to_bytes_be #t #l #len (nat_to_intseq_be #t #l len n) ==
     nat_to_bytes_be (len * numbytes t) n)

val nat_from_intseq_le_inj:
  #t:inttype{unsigned t} -> #l:secrecy_level -> b1:seq (uint_t t l) -> b2:seq (uint_t t l) ->
  Lemma
    (requires length b1 == length b2 /\ nat_from_intseq_le b1 == nat_from_intseq_le b2)
    (ensures Seq.equal b1 b2)
    (decreases (length b1))

val nat_from_intseq_be_inj:
  #t:inttype{unsigned t} -> #l:secrecy_level -> b1:seq (uint_t t l) -> b2:seq (uint_t t l) ->
  Lemma
    (requires length b1 == length b2 /\ nat_from_intseq_be b1 == nat_from_intseq_be b2)
    (ensures Seq.equal b1 b2)
    (decreases (length b1))

val lemma_nat_to_from_bytes_be_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == length b} -> x:nat{x < pow2 (8 * len)} ->
  Lemma (nat_from_bytes_be (nat_to_bytes_be #l len x) == x)

val lemma_nat_to_from_bytes_le_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == length b} -> x:nat{x < pow2 (8 * len)} ->
  Lemma (nat_from_bytes_le (nat_to_bytes_le #l len x) == x)

val lemma_uint_to_bytes_le_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> x:uint_t t l ->
  Lemma (nat_from_bytes_le (uint_to_bytes_le #t #l x) == uint_v x)

val lemma_uint_to_bytes_be_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> x:uint_t t l ->
  Lemma (nat_from_bytes_be (uint_to_bytes_be #t #l x) == uint_v x)

val lemma_nat_from_to_intseq_le_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> b:seq (uint_t t l){length b == len} ->
  Lemma (nat_to_intseq_le len (nat_from_intseq_le b) == b)

val lemma_nat_from_to_intseq_be_preserves_value: #t:inttype{unsigned t} -> #l:secrecy_level -> len:nat -> b:seq (uint_t t l){length b == len} ->
  Lemma (nat_to_intseq_be len (nat_from_intseq_be b) == b)

val lemma_nat_from_to_bytes_le_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == Lib.Sequence.length b} ->
  Lemma (nat_to_bytes_le #l len (nat_from_bytes_le b) == b)

val lemma_nat_from_to_bytes_be_preserves_value: #l:secrecy_level -> b:bytes_l l -> len:size_nat{len == Lib.Sequence.length b} ->
  Lemma (nat_to_bytes_be #l len (nat_from_bytes_be b) == b)

val lemma_reveal_uint_to_bytes_le: #t:inttype{unsigned t /\ t <> U1} -> #l:secrecy_level -> b:bytes_l l{Lib.Sequence.length b == numbytes t} ->
  Lemma (nat_from_bytes_le b == uint_v (uint_from_bytes_le #t #l b))

val lemma_reveal_uint_to_bytes_be: #t:inttype{unsigned t /\ t <> U1} -> #l:secrecy_level -> b:bytes_l l{Lib.Sequence.length b == numbytes t} ->
  Lemma (nat_from_bytes_be b == uint_v (uint_from_bytes_be #t #l b))

val lemma_uint_to_from_bytes_le_preserves_value :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  i : uint_t t l ->
  Lemma(uint_from_bytes_le #t #l (uint_to_bytes_le #t #l i) == i)

val lemma_uint_to_from_bytes_be_preserves_value :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  i : uint_t t l ->
  Lemma(uint_from_bytes_be #t #l (uint_to_bytes_be #t #l i) == i)

val lemma_uint_from_to_bytes_le_preserves_value :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  s : lbytes_l l (numbytes t) ->
  Lemma(uint_to_bytes_le #t #l (uint_from_bytes_le #t #l s) `equal` s)

val lemma_uint_from_to_bytes_be_preserves_value :
  #t : inttype{unsigned t /\ ~(U1? t)} ->
  #l : secrecy_level ->
  s : lbytes_l l (numbytes t) ->
  Lemma(uint_to_bytes_be #t #l (uint_from_bytes_be #t #l s) `equal` s)

val nat_from_intseq_be_public_to_secret:
  #t:inttype{unsigned t} -> len:size_pos{len * bits t < pow2 32} -> b:lseq (uint_t t PUB) len ->
  Lemma (nat_from_intseq_be b == nat_from_intseq_be (map secret b))

val nat_from_intseq_le_public_to_secret:
  #t:inttype{unsigned t} -> len:size_pos{len * bits t < pow2 32} -> b:lseq (uint_t t PUB) len ->
  Lemma (nat_from_intseq_le b == nat_from_intseq_le (map secret b))
