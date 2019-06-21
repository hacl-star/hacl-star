module Vale.Def.Words.Seq_s
open Vale.Def.Words_s
open Vale.Def.Words.Two_s
open Vale.Def.Words.Four_s
open FStar.Seq
open FStar.Mul
open Vale.Lib.Seqs_s

let seqn (n:nat) (a:Type) : Type = s:seq a{length s == n}
let seq2 (a:Type) = seqn 2 a
let seq4 (a:Type) = seqn 4 a
let seq8 (a:Type) = seqn 8 a
let seq16 (a:Type) = seqn 16 a

let seq_to_two_LE (#a:Type) (s:seq2 a) : two a =
  Mktwo (index s 0) (index s 1)

let seq_to_two_BE (#a:Type) (s:seq2 a) : two a =
  Mktwo (index s 1) (index s 0)

let seq_to_four_LE (#a:Type) (s:seq4 a) : four a =
  Mkfour (index s 0) (index s 1) (index s 2) (index s 3)

let seq_to_four_BE (#a:Type) (s:seq4 a) : four a =
  Mkfour (index s 3) (index s 2) (index s 1) (index s 0)

val two_to_seq_LE (#a:Type) (x:two a) : Pure (seq2 a)
  (requires True)
  (ensures fun s ->
    index s 0 == x.lo /\
    index s 1 == x.hi
  )

val two_to_seq_BE (#a:Type) (x:two a) : Pure (seq2 a)
  (requires True)
  (ensures fun s ->
    index s 1 == x.lo /\
    index s 0 == x.hi
  )

val four_to_seq_LE (#a:Type) (x:four a) : Pure (seq4 a)
  (requires True)
  (ensures fun s ->
    index s 0 == x.lo0 /\
    index s 1 == x.lo1 /\
    index s 2 == x.hi2 /\
    index s 3 == x.hi3
  )

val four_to_seq_BE (#a:Type) (x:four a) : Pure (seq4 a)
  (requires True)
  (ensures fun s ->
    index s 3 == x.lo0 /\
    index s 2 == x.lo1 /\
    index s 1 == x.hi2 /\
    index s 0 == x.hi3
  )

[@"opaque_to_smt"]
let seq_two_to_seq_LE (#a:Type) (x:seq (two a)) : (z:seq a{length z == length x * 2}) =
  let f (n:nat{n < length x * 2}) = two_select (index x (n / 2)) (n % 2) in
  init (length x * 2) f

[@"opaque_to_smt"]
let seq_two_to_seq_BE (#a:Type) (x:seq (two a)) : (z:seq a{length z == length x * 2}) =
  let f (n:nat{n < length x * 2}) = two_select (index x (n / 2)) (1 - n % 2) in
  init (length x * 2) f

[@"opaque_to_smt"]
let seq_four_to_seq_LE (#a:Type) (x:seq (four a)) : (z:seq a{length z == length x * 4}) =
  let f (n:nat{n < length x * 4}) = four_select (index x (n / 4)) (n % 4) in
  init (length x * 4) f

[@"opaque_to_smt"]
let seq_four_to_seq_BE (#a:Type) (x:seq (four a)) : (z:seq a{length z == length x * 4}) =
  let f (n:nat{n < length x * 4}) = four_select (index x (n / 4)) (3 - n % 4) in
  init (length x * 4) f

[@"opaque_to_smt"]
let seq_to_seq_two_LE (#a:Type) (x:seq a{length x % 2 == 0}) : (z:seq (two a){length z == length x / 2}) =
  let f (n:nat{n < length x / 2}) = Mktwo (index x (n * 2)) (index x (n * 2 + 1)) in
  init (length x / 2) f

[@"opaque_to_smt"]
let seq_to_seq_two_BE (#a:Type) (x:seq a{length x % 2 == 0}) : (z:seq (two a){length z == length x / 2}) =
  let f (n:nat{n < length x / 2}) = Mktwo (index x (n * 2 + 1)) (index x (n * 2)) in
  init (length x / 2) f

[@"opaque_to_smt"]
let seq_to_seq_four_LE (#a:Type) (x:seq a{length x % 4 == 0}) : (z:seq (four a){length z == length x / 4}) =
  let f (n:nat{n < length x / 4}) = Mkfour
    (index x (n * 4)) (index x (n * 4 + 1)) (index x (n * 4 + 2)) (index x (n * 4 + 3))
    in
  init (length x / 4) f

[@"opaque_to_smt"]
let seq_to_seq_four_BE (#a:Type) (x:seq a{length x % 4 == 0}) : (z:seq (four a){length z == length x / 4}) =
  let f (n:nat{n < length x / 4}) = Mkfour
    (index x (n * 4 + 3)) (index x (n * 4 + 2)) (index x (n * 4 + 1)) (index x (n * 4))
    in
  init (length x / 4) f


// Commonly used operations on bytes

let seq_nat8_to_seq_nat32_LE (x:seq nat8{length x % 4 == 0}) : seq nat32 =
  seq_map (four_to_nat 8) (seq_to_seq_four_LE x)

let seq_nat8_to_seq_nat32_BE (x:seq nat8{length x % 4 == 0}) : seq nat32 =
  seq_map (four_to_nat 8) (seq_to_seq_four_BE x)

let seq_nat32_to_seq_nat8_LE (x:seq nat32) : seq nat8 =
  seq_four_to_seq_LE (seq_map (nat_to_four 8) x)

let seq_nat32_to_seq_nat8_BE (x:seq nat32) : seq nat8 =
  seq_four_to_seq_BE (seq_map (nat_to_four 8) x)

let seq_nat8_to_seq_uint8 (x:seq nat8) : seq UInt8.t =
  seq_map UInt8.uint_to_t x

let seq_uint8_to_seq_nat8 (x:seq UInt8.t) : seq nat8 =
  seq_map UInt8.v x
