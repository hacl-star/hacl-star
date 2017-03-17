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
let op_Bar_Greater f g = op_At f g
inline_for_extraction
let set (i:nat) (x:'a) (s:seq 'a{length s > i}) : Tot (s':seq 'a{length s' = length s}) = upd s i x
inline_for_extraction
let op_String_Access = Seq.index
inline_for_extraction
let op_String_Assignment = Seq.upd

inline_for_extraction
let iter n f x = Spec.Loops.repeat_spec n f x

inline_for_extraction
let map2 f s1 s2 = Spec.Loops.seq_map2 f s1 s2

let singleton x = Seq.create 1 x

let tuple x y = Seq.upd (Seq.create 2 x) 1 y

#set-options "--initial_fuel 0 --max_fuel 0"

let uint32_from_le (b:lbytes 4) : UInt32.t =
    let n = little_endian b  in
    lemma_little_endian_is_bounded b;
    UInt32.uint_to_t n

let uint32_to_le (a:UInt32.t) : lbytes 4 =
    little_bytes 4ul (v a)

let uint32_from_be (b:lbytes 4) : UInt32.t =
    let n = big_endian b  in
    lemma_big_endian_is_bounded b;
    UInt32.uint_to_t n

let uint32_to_be (a:UInt32.t) : lbytes 4 =
    big_bytes 4ul (v a)


let uint64_from_le (b:lbytes 8) : UInt64.t =
    let n = little_endian b  in
    lemma_little_endian_is_bounded b;
    UInt64.uint_to_t n

let uint64_to_le (a:UInt64.t) : lbytes 8 =
    little_bytes 8ul (UInt64.v a)

let uint64_from_be (b:lbytes 8) : UInt64.t =
    let n = big_endian b  in
    lemma_big_endian_is_bounded b;
    UInt64.uint_to_t n

let uint64_to_be (a:UInt64.t) : lbytes 8 =
    big_bytes 8ul (UInt64.v a)


let lemma_uint32_from_le_inj (b:lbytes 4) (b':lbytes 4) : Lemma
  (requires (uint32_from_le b = uint32_from_le b'))
  (ensures  (b == b'))
  = lemma_little_endian_inj b b'


let lemma_uint32_to_le_inj (b:UInt32.t) (b':UInt32.t) : Lemma
  (requires (uint32_to_le b == uint32_to_le b'))
  (ensures  (b = b'))
  = ()


abstract val create_4: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a ->
  Tot (s:seq a{length s = 4 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3})
let create_4 #a s0 s1 s2 s3 =
  let s = create 4 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in s

abstract val create_8: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  Tot (s:seq a{length s = 8 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3  /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7})
let create_8 #a s0 s1 s2 s3 s4 s5 s6 s7 =
  let s = create 8 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in s

abstract val create_16: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a -> s12:a -> s13:a -> s14:a -> s15:a ->
  Tot (s:seq a{length s = 16
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11
    /\ index s 12 == s12 /\ index s 13 == s13 /\ index s 14 == s14 /\ index s 15 == s15})
let create_16 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =
  let s = create 16 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in
  let s = s.[12] <- s12 in
  let s = s.[13] <- s13 in
  let s = s.[14] <- s14 in
  let s = s.[15] <- s15 in s

abstract val create_4: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a ->
  Tot (s:seq a{length s = 4 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3})
let create_4 #a s0 s1 s2 s3 =
  let s = create 4 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in s

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


val uint64s_from_le: len:nat -> b:lbytes (8 * len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_le len src =
  if len = 0 then Seq.createEmpty #UInt64.t
  else
    let h = slice src 0 8 in
    let t = slice src 8 (8*len) in
    Seq.cons (uint64_from_le h)
             (uint64s_from_le (len-1) t)

val uint64s_to_le: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 * len))  (decreases len)
let rec uint64s_to_le len src =
  if len = 0 then Seq.createEmpty #UInt8.t
  else
    let h = index src 0 in
    let t = slice src 1 len in
    Seq.append (uint64_to_le h)
               (uint64s_to_le (len-1) t)


val uint32s_from_be: len:nat -> b:lbytes (4 * len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_be len src =
  if len = 0 then Seq.createEmpty #UInt32.t
  else
    let h = slice src 0 4 in
    let t = slice src 4 (4*len) in
    Seq.cons (uint32_from_be h)
             (uint32s_from_be (len-1) t)

val uint32s_to_be: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 * len))  (decreases len)
let rec uint32s_to_be len src =
  if len = 0 then Seq.createEmpty #UInt8.t
  else
    let h = index src 0 in
    let t = slice src 1 len in
    Seq.append (uint32_to_be h)
               (uint32s_to_be (len-1) t)


val uint64s_from_be: len:nat -> b:lbytes (8 * len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_be len src =
  if len = 0 then Seq.createEmpty #UInt64.t
  else
    let h = slice src 0 8 in
    let t = slice src 8 (8*len) in
    Seq.cons (uint64_from_be h)
             (uint64s_from_be (len-1) t)

val uint64s_to_be: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 * len))  (decreases len)
let rec uint64s_to_be len src =
  if len = 0 then Seq.createEmpty #UInt8.t
  else
    let h = index src 0 in
    let t = slice src 1 len in
    Seq.append (uint64_to_be h)
               (uint64s_to_be (len-1) t)


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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"


let lemma_append_assoc (#a:Type) (x:seq a) (y:seq a) (z:seq a) : Lemma
  (x @| (y @| z) == (x @| y) @| z) = lemma_eq_intro ((x @| y) @| z) (x @| (y @| z))


val lemma_uint32s_from_le_slice: len:nat -> b:lbytes (4*len) -> n:nat{n <= len} -> Lemma
  (requires (True))
  (ensures (uint32s_from_le len b == uint32s_from_le n (slice b 0 (4 * n)) @| uint32s_from_le (len - n) (slice b (4 * n) (length b))))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"
let rec lemma_uint32s_from_le_slice len b n =
  if n = 0 then (
    lemma_uint32s_from_le_def_0 0 (slice b 0 0);
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_from_le 0 (slice b 0 0)) createEmpty;
    lemma_eq_intro (createEmpty @| uint32s_from_le len b) (uint32s_from_le len b)
  ) else (
    lemma_uint32s_from_le_def_1 len b;
    lemma_uint32s_from_le_def_1 n (slice b 0 (4*n));
    let hd, tl = split b 4 in
    lemma_uint32s_from_le_slice (len-1) tl (n-1);
    cut (uint32s_from_le (len-1) tl == uint32s_from_le (n-1) (slice tl 0 (4 * (n-1))) @| uint32s_from_le (len - n) (slice tl (4 * (n-1)) (length tl)));
    lemma_eq_intro (slice tl (4 * (n-1)) (length tl)) (slice b (4 * n) (length b));
    lemma_eq_intro (slice tl 0 (4*(n-1))) (slice b 4 (4 * n));
    lemma_append_assoc (create 1 (uint32_from_le hd)) (uint32s_from_le (n-1) (slice tl 0 (4 * (n-1))))
                       (uint32s_from_le (len-n) (slice b (4 * n) (length b)));
    lemma_eq_intro (slice b 0 4) (slice (slice b 0 (4*n)) 0 4);
    lemma_eq_intro (slice b 4 (4*n)) (slice (slice b 0 (4*n)) 4 (4 *n));
    lemma_eq_intro (uint32s_from_le n (slice b 0 (4 * n))) (cons (uint32_from_le hd) (uint32s_from_le (n-1) (slice b 4 (4*n)))))


val lemma_uint32s_to_le_slice: len:nat -> b:Seq.seq UInt32.t{length b = len} -> n:nat{n <= len} -> Lemma
  (uint32s_to_le len b = uint32s_to_le n (slice b 0 n) @| uint32s_to_le (len - n) (slice b n len))
let rec lemma_uint32s_to_le_slice len b n =
  if n = 0 then (
    lemma_uint32s_to_le_def_0 0 (slice b 0 0);
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_to_le 0 (slice b 0 0)) createEmpty;
    lemma_eq_intro (createEmpty @| uint32s_to_le len b) (uint32s_to_le len b)
  ) else (
    lemma_uint32s_to_le_def_1 len b;
    lemma_uint32s_to_le_def_1 n (slice b 0 (n));
    let h  = index b 0 in
    let tl = slice b 1 len in
    lemma_uint32s_to_le_slice (len-1) tl (n-1);
    cut (uint32s_to_le (len-1) tl == uint32s_to_le (n-1) (slice tl 0 (n-1))
                                     @| uint32s_to_le (len-n) (slice tl (n-1) (len-1)));
    lemma_eq_intro (slice tl (n-1) (len-1)) (slice b n len);
    lemma_eq_intro (slice tl 0 (n-1)) (slice b 1 n);
    lemma_append_assoc (uint32_to_le h) (uint32s_to_le (n-1) (slice b 1 n))
                       (uint32s_to_le (len-n) (slice b n len));
    cut (index (slice b 0 n) 0 = index b 0);
    lemma_eq_intro (slice b 1 n) (slice (slice b 0 n) 1 n);
    lemma_eq_intro (uint32s_to_le n (slice b 0 n)) (uint32_to_le h @| (uint32s_to_le (n-1) (slice b 1 n)))
  )
