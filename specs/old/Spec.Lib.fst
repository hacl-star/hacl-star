module Spec.Lib

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Old.Endianness

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

let rotate_left (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) : Tot UInt32.t =
  ((a <<^ s) |^ (a >>^ (32ul -^ s)))

let rotate_right (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) : Tot UInt32.t =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

let op_Less_Less_Less (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) = rotate_left a s
let op_Greater_Greater_Greater (a:UInt32.t) (s:UInt32.t {0 < v s /\ v s<32}) = rotate_right a s

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

unfold inline_for_extraction
let iter n f x = Spec.Loops.repeat_spec n f x

unfold inline_for_extraction
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


#reset-options "--z3rlimit 150"
let lemma_uint32_from_le_inj (b:lbytes 4) (b':lbytes 4) : Lemma
  (requires (uint32_from_le b = uint32_from_le b'))
  (ensures  (b == b'))
  = lemma_little_endian_inj b b'


let lemma_uint32_to_le_inj (b:UInt32.t) (b':UInt32.t) : Lemma
  (requires (uint32_to_le b == uint32_to_le b'))
  (ensures  (b = b'))
  = ()

let lemma_uint32_to_from_bij (b:UInt32.t) : Lemma
  (requires (True))
  (ensures (uint32_from_le (uint32_to_le b) = b))
  = ()

let lemma_uint32_from_to_bij (b:lbytes 4) : Lemma
  (requires (True))
  (ensures (uint32_to_le (uint32_from_le b) = b))
  = lemma_uint32_to_from_bij (uint32_from_le b);
    let lemma (s:lbytes 4) (s':lbytes 4):
      Lemma (requires (s <> s'))
            (ensures (uint32_from_le s <> uint32_from_le s'))
      = if uint32_from_le s = uint32_from_le s' then lemma_uint32_from_le_inj s s' in
    if uint32_to_le (uint32_from_le b) <> b then lemma (uint32_to_le (uint32_from_le b)) b


val uint32s_from_le: len:nat -> b:lbytes (4 * len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_le len src =
  if len = 0 then Seq.empty
  else (
    let prefix, last = split src (4 * len - 4) in
    snoc (uint32s_from_le (len-1) prefix) (uint32_from_le last)
  )

    (* uint32s_from_le (len - 1)  *)
(* let rec uint32s_from_le len src = *)
(*   if len = 0 then Seq.empty #UInt32.t *)
(*   else *)
(*     let h = slice src 0 4 in *)
(*     let t = slice src 4 (4*len) in *)
(*     Seq.cons (uint32_from_le h) *)
(*              (uint32s_from_le (len-1) t) *)

val uint32s_to_le: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 * len))  (decreases len)
let rec uint32s_to_le len src =
  if len = 0 then Seq.empty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint32s_to_le (len-1) prefix @| (uint32_to_le last)
  )

val uint64s_from_le: len:nat -> b:lbytes (8 * len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_le len src =
  if len = 0 then Seq.empty
  else (
    let prefix, last = split src (8 * len - 8) in
    snoc (uint64s_from_le (len-1) prefix) (uint64_from_le last)
  )

val uint64s_to_le: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 * len))  (decreases len)
let rec uint64s_to_le len src =
  if len = 0 then Seq.empty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint64s_to_le (len-1) prefix @| (uint64_to_le last)
  )


val uint32s_from_be: len:nat -> b:lbytes (4 * len) -> Tot (s:seq UInt32.t{length s = len}) (decreases len)
let rec uint32s_from_be len src =
  if len = 0 then Seq.empty
  else (
    let prefix, last = split src (4 * len - 4) in
    snoc (uint32s_from_be (len-1) prefix) (uint32_from_be last)
  )

val uint32s_to_be: len:nat -> s:seq UInt32.t{length s = len} -> Tot (lbytes (4 * len))  (decreases len)
let rec uint32s_to_be len src =
  if len = 0 then Seq.empty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint32s_to_be (len-1) prefix @| (uint32_to_be last)
  )

val uint64s_from_be: len:nat -> b:lbytes (8 * len) -> Tot (s:seq UInt64.t{length s = len}) (decreases len)
let rec uint64s_from_be len src =
  if len = 0 then Seq.empty
  else (
    let prefix, last = split src (8 * len - 8) in
    snoc (uint64s_from_be (len-1) prefix) (uint64_from_be last)
  )

val uint64s_to_be: len:nat -> s:seq UInt64.t{length s = len} -> Tot (lbytes (8 * len))  (decreases len)
let rec uint64s_to_be len src =
  if len = 0 then Seq.empty
  else (
    let prefix = slice src 0 (len - 1) in
    let last   = index src (len - 1) in
    uint64s_to_be (len-1) prefix @| (uint64_to_be last)
  )


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let lemma_uint32s_from_le_def_0 (len:nat{len = 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_le len b == Seq.empty)
  = ()
let lemma_uint32s_from_le_def_1 (len:nat{len > 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_le len b == Seq.snoc (uint32s_from_le (len-1) (slice b 0 (4*len - 4)))
                                     (uint32_from_le (slice b (4*len - 4) (4*len)))
  )
  = ()


let lemma_uint32s_to_le_def_0 (len:nat{len = 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.empty)
  = ()
let lemma_uint32s_to_le_def_1 (len:nat{len > 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_le len s == Seq.append (uint32s_to_le (len-1) (slice s 0 (len-1)))
                                     (uint32_to_le (index s (len-1))))
  = ()


let lemma_uint32s_from_be_def_0 (len:nat{len = 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_be len b == Seq.empty)
  = ()
let lemma_uint32s_from_be_def_1 (len:nat{len > 0}) (b:lbytes (4*len)) : Lemma
  (uint32s_from_be len b == Seq.snoc (uint32s_from_be (len-1) (slice b 0 (4*len - 4)))
                                     (uint32_from_be (slice b (4*len - 4) (4*len)))
  )
  = ()


let lemma_uint32s_to_be_def_0 (len:nat{len = 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_be len s == Seq.empty)
  = ()
let lemma_uint32s_to_be_def_1 (len:nat{len > 0}) (s:seq UInt32.t{length s = len}) : Lemma
  (uint32s_to_be len s == Seq.append (uint32s_to_be (len-1) (slice s 0 (len-1)))
                                     (uint32_to_be (index s (len-1))))
  = ()


let lemma_uint64s_from_be_def_0 (len:nat{len = 0}) (b:lbytes (8*len)) : Lemma
  (uint64s_from_be len b == Seq.empty)
  = ()
let lemma_uint64s_from_be_def_1 (len:nat{len > 0}) (b:lbytes (8*len)) : Lemma
  (uint64s_from_be len b == Seq.snoc (uint64s_from_be (len-1) (slice b 0 (8*len - 8)))
                                     (uint64_from_be (slice b (8*len - 8) (8*len)))
  )
  = ()


let lemma_uint64s_to_be_def_0 (len:nat{len = 0}) (s:seq UInt64.t{length s = len}) : Lemma
  (uint64s_to_be len s == Seq.empty)
  = ()
let lemma_uint64s_to_be_def_1 (len:nat{len > 0}) (s:seq UInt64.t{length s = len}) : Lemma
  (uint64s_to_be len s == Seq.append (uint64s_to_be (len-1) (slice s 0 (len-1)))
                                     (uint64_to_be (index s (len-1))))
  = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let rec lemma_uint32s_from_le_inj (len:nat) (b:lbytes (4 * len)) (b':lbytes (4 * len)) : Lemma
  (requires (uint32s_from_le len b == uint32s_from_le len b'))
  (ensures  (b == b'))
  = if len = 0 then (lemma_uint32s_from_le_def_0 len b; lemma_uint32s_from_le_def_0 len b';
      Seq.lemma_eq_intro b b')
    else (
          let h  = slice b (4*len - 4) (4*len) in
          let h'  = slice b' (4*len - 4) (4*len) in
          let t  = slice b 0 (4*len-4) in
          let t' = slice b' 0 (4*len-4) in
          lemma_uint32s_from_le_def_1 len b;
          lemma_uint32s_from_le_def_1 len b';
          Seq.lemma_eq_intro (uint32s_from_le len b) (uint32s_from_le len b');
          cut (Seq.index (uint32s_from_le len b) (len-1) == Seq.index (uint32s_from_le len b') (len-1));
          cut (Seq.index (uint32s_from_le len b) (len-1) == uint32_from_le h);
          cut (Seq.index (uint32s_from_le len b') (len-1) == uint32_from_le h');
          lemma_uint32_from_le_inj h h';
          Seq.lemma_eq_intro h h';
          cut (Seq.slice (uint32s_from_le len b) 0 (len-1) == Seq.slice (uint32s_from_le len b') 0 (len-1));
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b) 0 (len-1)) (uint32s_from_le (len-1) t);
          Seq.lemma_eq_intro (Seq.slice (uint32s_from_le len b') 0 (len-1)) (uint32s_from_le (len-1) t');
          lemma_uint32s_from_le_inj (len-1) t t';
          Seq.lemma_eq_intro t t';
          Seq.lemma_eq_intro b (t @| h);
          Seq.lemma_eq_intro b' (t' @| h')
          )


#set-options "--max_fuel 0 --z3rlimit 100"

let rec lemma_uint32s_from_le_bij (len:nat) (b:lbytes (4 * len)) : Lemma
  (requires (True))
  (ensures  (uint32s_to_le len (uint32s_from_le len b) == b))
  = if len = 0 then (
      lemma_uint32s_from_le_def_0 0 b;
      lemma_uint32s_to_le_def_0 0 (Seq.empty);
      lemma_eq_intro (uint32s_to_le len (uint32s_from_le len b)) b
    ) else (
      lemma_uint32s_from_le_def_1 len b;
      let b' = uint32s_from_le len b in
      lemma_uint32s_to_le_def_1 len b';
      lemma_uint32_from_to_bij (slice b (4*len-4) (length b));
      lemma_uint32s_from_le_bij (len - 1) (slice b 0 (length b - 4));
      lemma_eq_intro b'  (snoc (uint32s_from_le (len-1) (slice b 0 (length b - 4))) (uint32_from_le (slice b (length b - 4) (length b))));
      lemma_eq_intro (slice b' 0 (length b'-1)) (uint32s_from_le (len-1) (slice b 0 (length b - 4)));
      lemma_eq_intro (uint32s_to_le len b') (append (uint32s_to_le (len-1) (uint32s_from_le (len-1) (slice b 0 (length b - 4)))) (uint32_to_le (uint32_from_le (slice b (length b - 4) (length b)))) );
      lemma_eq_intro (uint32s_to_le len (uint32s_from_le len b)) b
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
      let h  = index b (len-1) in
      let h' = index b' (len-1) in
      let t  = slice b 0 (len-1) in
      let t' = slice b' 0 (len-1) in
      lemma_uint32s_to_le_def_1 len b;
      lemma_uint32s_to_le_def_1 len b';
      Seq.lemma_eq_intro (uint32s_to_le len b) (uint32s_to_le len b');
      cut (Seq.slice (uint32s_to_le len b) (4*len-4) (4 * len) == Seq.slice (uint32s_to_le len b') (4*len -4) (4 * len));
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) (4*len-4) (4 * len)) (uint32_to_le h);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') (4*len-4) (4 * len)) (uint32_to_le h');
      lemma_uint32_to_le_inj h h';
      cut (Seq.slice (uint32s_to_le len b) 0 (4*len-4) == Seq.slice (uint32s_to_le len b') 0 (4*len-4));
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b) 0 (4*len-4)) (uint32s_to_le (len-1) t);
      Seq.lemma_eq_intro (Seq.slice (uint32s_to_le len b') 0 (4*len-4)) (uint32s_to_le (len-1) t');
      lemma_uint32s_to_le_inj (len-1) t t';
      Seq.lemma_eq_intro t t';
      Seq.lemma_eq_intro b (snoc t h);
      Seq.lemma_eq_intro b' (snoc t' h')
    )


let rec lemma_uint32s_to_le_bij (len:nat) (b:seq UInt32.t{length b = len}) : Lemma
  (requires (True))
  (ensures  (uint32s_from_le len (uint32s_to_le len b) == b))
  = if len = 0 then (
      lemma_uint32s_to_le_def_0 0 b;
      lemma_uint32s_from_le_def_0 0 (Seq.empty);
      lemma_eq_intro (uint32s_from_le len (uint32s_to_le len b)) b
    ) else (
      lemma_uint32s_to_le_def_1 len b;
      let b' = uint32s_to_le len b in
      lemma_uint32s_from_le_def_1 len b';
      lemma_uint32_to_from_bij (index b (len-1));
      lemma_uint32s_to_le_bij (len - 1) (slice b 0 (length b-1));
      lemma_eq_intro b' (append (uint32s_to_le (len-1) (slice b 0 (length b-1))) (uint32_to_le (index b (len-1))));
      lemma_eq_intro (slice b' 0 (length b' - 4)) (uint32s_to_le (len-1) (slice b 0 (length b-1)));
      lemma_eq_intro (slice b' (4*len-4) (4*len)) (uint32_to_le (index b (len-1)));
      lemma_eq_intro (uint32s_from_le len b') (snoc (uint32s_from_le (len-1) (uint32s_to_le (len-1) (slice b 0 (length b-1)))) (uint32_from_le (uint32_to_le (index b (len-1)))));
      lemma_eq_intro (uint32s_from_le len (uint32s_to_le len b)) b
    )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

let lemma_append_assoc (#a:Type) (x:seq a) (y:seq a) (z:seq a) : Lemma
  (x @| (y @| z) == (x @| y) @| z) = lemma_eq_intro ((x @| y) @| z) (x @| (y @| z))


val lemma_uint32s_from_le_slice: len:nat -> b:lbytes (4*len) -> n:nat{n <= len} -> Lemma
  (requires (True))
  (ensures (uint32s_from_le len b == uint32s_from_le n (slice b 0 (4 * n)) @| uint32s_from_le (len - n) (slice b (4 * n) (length b))))
  (decreases (len-n))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"
let rec lemma_uint32s_from_le_slice len b n =
  if n = len then (
    lemma_uint32s_from_le_def_0 0 (slice b (4*len) (4*len));
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_from_le 0 (slice b (4*len) (4*len))) Seq.empty;
    lemma_eq_intro (uint32s_from_le len b @| Seq.empty) (uint32s_from_le len b)
  ) else (
    lemma_uint32s_from_le_def_1 len b;
    lemma_uint32s_from_le_def_1 (len - n) (slice b (4 * n) (4 * len));
    let tl, hd = split b (4*len - 4) in
    lemma_uint32s_from_le_slice (len-1) tl (n);
    lemma_eq_intro (slice tl 0 (4*n)) (slice b 0 (4*n));
    lemma_eq_intro (slice tl (4*n) (4*(len-1))) (slice b (4*n) (4 * (len - 1)));
    lemma_append_assoc (uint32s_from_le n (slice tl 0 (4 * n)))
                       (uint32s_from_le (len - 1 - n) (slice tl (4*n) (4*(len - 1))))
                       (create 1 (uint32_from_le hd));
    lemma_eq_intro (slice b (4*len-4) (4*len)) (slice (slice b (4*n) (4*len)) (4*(len - 1 - n)) (4*(len-n)));
    lemma_eq_intro (slice b (4*n) (4*(len-1))) (slice (slice b (4*n) (length b)) 0 (4 * (len - n - 1)));

    lemma_eq_intro (uint32s_from_le (len-n) (slice b (4 * n) (4*len))) (snoc (uint32s_from_le (len-n-1) (slice b (4*n) (4*(len-1)))) (uint32_from_le hd)))


val lemma_uint32s_to_le_slice: len:nat -> b:Seq.seq UInt32.t{length b = len} -> n:nat{n <= len} -> Lemma
  (requires (True))
  (ensures (uint32s_to_le len b = uint32s_to_le n (slice b 0 n) @| uint32s_to_le (len - n) (slice b n len)))
  (decreases (len - n))
let rec lemma_uint32s_to_le_slice len b n =
  if n = len then (
    lemma_uint32s_to_le_def_0 0 (slice b len len);
    lemma_eq_intro (slice b 0 (length b)) b;
    lemma_eq_intro (uint32s_to_le 0 (slice b len len)) Seq.empty;
    lemma_eq_intro (uint32s_to_le len b @| Seq.empty) (uint32s_to_le len b)
  ) else (
    lemma_uint32s_to_le_def_1 len b;
    lemma_uint32s_to_le_def_1 (len-n) (slice b n (len));
    let h  = index b (len-1) in
    let tl = slice b 0 (len-1) in
    lemma_uint32s_to_le_slice (len-1) tl (n);
    lemma_eq_intro (slice tl (0) (n)) (slice b 0 n);
    lemma_eq_intro (slice tl n (len - 1)) (slice b n (len - 1));
    lemma_append_assoc (uint32s_to_le (n) (slice b 0 n))
                       (uint32s_to_le (len-n-1) (slice b n (len-1))) (uint32_to_le h);
    cut (index (slice b n len) (len - n - 1) = index b (len-1));
    lemma_eq_intro (slice b n (len-1)) (slice (slice b n (len)) 0 (len-n-1));
    lemma_eq_intro (uint32s_to_le (len-n) (slice b n (len))) (uint32s_to_le (len-n-1) (slice b n (len-1)) @| uint32_to_le h)
  )
