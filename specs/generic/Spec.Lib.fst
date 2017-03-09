module Spec.Lib

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness


#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

let rotate_left (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  ((a <<^ s) |^ (a >>^ (32ul -^ s)))

let rotate_right (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

let op_Less_Less_Less (a:UInt32.t) (s:UInt32.t {v s<32}) = rotate_left a s
let op_Greater_Greater_Greater (a:UInt32.t) (s:UInt32.t {v s<32}) = rotate_right a s

let byte = UInt8.t
let bytes = seq UInt8.t
let lbytes (l:nat) = b:seq UInt8.t {length b = l}
let op_At f g = fun x -> g (f x)
inline_for_extraction
let set (i:nat) (x:'a) (s:seq 'a{length s > i}) : Tot (s':seq 'a{length s' = length s}) = upd s i x

inline_for_extraction
let iter n f x = C.Loops.repeat_spec n f x

inline_for_extraction
let map2 f s1 s2 = C.Loops.seq_map2 f s1 s2

let singleton x = Seq.create 1 x

let tuple x y = Seq.upd (Seq.create 2 x) 1 y

#set-options "--initial_fuel 0 --max_fuel 0"

let uint32_from_le (b:lbytes 4) : UInt32.t =
    let n = little_endian b  in
    lemma_little_endian_is_bounded b;
    UInt32.uint_to_t n

let uint32_to_le (a:UInt32.t) : lbytes 4 =
    little_bytes 4ul (v a)


let lemma_uint32_from_le_inj (b:lbytes 4) (b':lbytes 4) : Lemma
  (requires (uint32_from_le b = uint32_from_le b'))
  (ensures  (b == b'))
  = lemma_little_endian_inj b b'


let lemma_uint32_to_le_inj (b:UInt32.t) (b':UInt32.t) : Lemma
  (requires (uint32_to_le b == uint32_to_le b'))
  (ensures  (b = b'))
  = ()

// JK: those two should go somewhere else
val uint32s_from_le: len:nat -> b:lbytes (4 * len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_le len src =
  if len = 0 then Seq.createEmpty #UInt32.t
  else
    let h = slice src 0 4 in
    let t = slice src 4 (4*len) in
    Seq.cons (uint32_from_le h)
             (uint32s_from_le (len-1) t)

val uint32s_to_le: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 * len))  (decreases len)
let rec uint32s_to_le len src =
  if len = 0 then Seq.createEmpty #UInt8.t
  else
    let h = index src 0 in
    let t = slice src 1 len in
    Seq.append (uint32_to_le h)
               (uint32s_to_le (len-1) t)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let lemma_uint32s_from_le_def_0 (len:nat{len = 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_le len b == Seq.createEmpty)
  = ()
let lemma_uint32s_from_le_def_1 (len:nat{len > 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_le len b == Seq.cons (uint32_from_le (slice b 0 4))
                                     (uint32s_from_le (len-1) (slice b 4 (4*len))))
  = ()


let lemma_uint32s_to_le_def_0 (len:nat{len = 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.createEmpty)
  = ()
let lemma_uint32s_to_le_def_1 (len:nat{len > 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.append (uint32_to_le (index s 0))
                                     (uint32s_to_le (len-1) (slice s 1 (len))))
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let rec lemma_uint32s_from_le_inj (len:nat) (b:lbytes (4 * len)) (b':lbytes (4 * len)) : Lemma
  (requires (uint32s_from_le len b == uint32s_from_le len b'))
  (ensures  (b == b'))
  = if len = 0 then (lemma_uint32s_from_le_def_0 len b; lemma_uint32s_from_le_def_0 len b';
      Seq.lemma_eq_intro b b')
    else (let h  = slice b 0 4 in
          let h' = slice b' 0 4 in
          let t  = slice b 4 (4*len) in
          let t' = slice b' 4 (4*len) in
          lemma_uint32s_from_le_def_1 len b;
          lemma_uint32s_from_le_def_1 len b';
          Seq.lemma_eq_intro (uint32s_from_le len b) (uint32s_from_le len b');
          cut (Seq.index (uint32s_from_le len b) 0 == Seq.index (uint32s_from_le len b') 0); 
          cut (Seq.index (uint32s_from_le len b) 0 == uint32_from_le h);
          cut (Seq.index (uint32s_from_le len b') 0 == uint32_from_le h');
          lemma_uint32_from_le_inj h h';
          Seq.lemma_eq_intro h h';
          cut (Seq.slice (uint32s_from_le len b) 1 len == Seq.slice (uint32s_from_le len b') 1 len);
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b) 1 len) (uint32s_from_le (len-1) t);
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b') 1 len) (uint32s_from_le (len-1) t');
          lemma_uint32s_from_le_inj (len-1) t t';
          Seq.lemma_eq_intro t t';
          Seq.lemma_eq_intro b (h @| t);
          Seq.lemma_eq_intro b' (h' @| t')
          )


let rec lemma_uint32s_to_le_inj (len:nat) (b:seq UInt32.t{length b = len})
                                         (b':seq UInt32.t{length b' = len})  : Lemma
  (requires (uint32s_to_le len b == uint32s_to_le len b'))
  (ensures  (b == b'))
  = if len = 0 then (
      lemma_uint32s_to_le_def_0 len b;
      lemma_uint32s_to_le_def_0 len b';
      Seq.lemma_eq_intro b b'
    ) else (
      let h  = index b 0 in
      let h' = index b' 0 in
      let t  = slice b 1 (len) in
      let t' = slice b' 1 (len) in
      lemma_uint32s_to_le_def_1 len b;
      lemma_uint32s_to_le_def_1 len b';
      Seq.lemma_eq_intro (uint32s_to_le len b) (uint32s_to_le len b');
      cut (Seq.slice (uint32s_to_le len b) 0 4 == Seq.slice (uint32s_to_le len b') 0 4);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) 0 4) (uint32_to_le h);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') 0 4) (uint32_to_le h');
      lemma_uint32_to_le_inj h h';
      cut (Seq.slice (uint32s_to_le len b) 4 (4*len) == Seq.slice (uint32s_to_le len b') 4 (4*len));
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) 4 (4*len)) (uint32s_to_le (len-1) t);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') 4 (4*len)) (uint32s_to_le (len-1) t');
      lemma_uint32s_to_le_inj (len-1) t t';
      Seq.lemma_eq_intro t t';
      Seq.lemma_eq_intro b (cons h t);
      Seq.lemma_eq_intro b' (cons h' t')
    )
