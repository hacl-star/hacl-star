module Hacl.Spe.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
open FStar.Int.Cast

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Spec.Poly1305_64
open Hacl.Spec.Poly1305

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


let zero : elem = 0
let one  : elem = 1

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 + e2) % prime
let op_Plus_At e1 e2 = fadd e1 e2

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime
let op_Star_At e1 e2 = fmul e1 e2


val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 16} ->
  Tot (st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)
    /\ seval (MkState?.r st) = UInt.logand #128 (little_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff
    /\ seval (MkState?.h st) = 0})
let poly1305_init_spec key =
  poly1305_init_spec key


private val lemma_mod_distr: acc0:nat -> block:nat -> r0:nat -> Lemma
  (((acc0 + block) * r0) % prime = (((acc0 % prime) +@ (block % prime)) *@ (r0 % prime)))
private let lemma_mod_distr acc block r0 =
  let open FStar.Math.Lemmas in
  lemma_mod_mul_distr_l (acc + block) r0 prime;
  lemma_mod_mul_distr_l r0 ((acc + block) % prime) prime;
  lemma_mod_plus_distr_l acc block prime;
  lemma_mod_plus_distr_l block (acc % prime) prime

private val lemma_mod_distr_seq: acc:seqelem -> block:word_16 -> r:seqelem -> Lemma
  (let acc0 = seval acc in let r0 = seval r in
   let block = little_endian block + pow2 128 in
   ((acc0 + block) * r0) % prime = (((acc0 % prime) +@ (block % prime)) *@ (r0 % prime)))
private let lemma_mod_distr_seq acc block r =
  let acc0 = seval acc in let r0 = seval r in
  let block = little_endian block + pow2 128 in
  lemma_mod_distr acc0 block r0


val poly1305_update_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word_16 ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) % prime in
       let acc1 = seval (MkState?.h st') % prime in
       let r0 = seval (MkState?.r st) % prime in
       let r1 = seval (MkState?.r st') % prime in
       let log0:seq word = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = (little_endian m + pow2 128) % prime in
       r0 = r1 /\ acc1  = ((acc0 +@ block) *@ r0)
       /\ (log1 == (Seq.create 1 m) @| log0))})
let poly1305_update_spec st m =
  lemma_mod_distr_seq (MkState?.h st) m (MkState?.r st);
  poly1305_update_spec st m


val poly1305_finish_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word ->
  rem':limb{v rem' = length m /\ length m < 16} ->
  key_s:Seq.seq H8.t{Seq.length key_s = 16} ->
  Tot (mac:word_16{
      (let acc = seval (MkState?.h st) % prime in
       let r   = seval (MkState?.r st) % prime in
       let k   = little_endian key_s   in
       let m'   = (little_endian m + pow2 (8*length m)) % prime in
       let mac = little_endian mac in
       if Seq.length m >= 1
       then mac = (((acc +@ m') *@ r) + k) % pow2 128
       else mac = ((acc + k) % pow2 128)) })
       (* if Seq.length m >= 1 *)
       (* then mac == finish ((acc +@ m') *@ r) key_s *)
       (* else mac == finish acc key_s) }) *)
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let poly1305_finish_spec st m rem' key_s =
  if Seq.length m >= 1 then (
    lemma_mod_distr (seval (MkState?.h st)) (little_endian m + pow2 (8*length m)) (seval (MkState?.r st))(* ; *)
    (* Math.Lemmas.lemma_mod_plus_distr_l (((selem (MkState?.h st) +@ ((little_endian m + pow2 (8*length m)) % prime)) *@ (seval (MkState?.r st) % prime))) (little_endian key_s) (pow2 128) *)
  )
  (* else ( *)
  (*   Math.Lemmas.lemma_mod_plus_distr_l (selem (MkState?.h st)) (little_endian key_s) (pow2 128) *)
  (* ) *);
  let mac = poly1305_finish_spec st m rem' key_s in
  (* lemma_little_endian_inj mac (if length m >= 1 then finish ((selem (MkState?.h st) +@ ((little_endian m + pow2 (8*length m)) % prime)) *@ (seval (MkState?.r st) % prime)) key_s else finish (selem (MkState?.h st)) key_s); *)
  mac


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

(* *************************** *)
(* Standalone poly1305 version *)
(* *************************** *)

let encode (w:word) : Tot elem =
  let l = length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  lemma_little_endian_is_bounded w;
  pow2 (8 * l) +@ little_endian w


val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r


let invariant (st:poly1305_state_) : GTot Type0 =
  let acc = (MkState?.h st) in let r = (MkState?.r st) in let log = MkState?.log st in
  seval r < pow2 130 - 5 /\  red_44 r /\ red_45 acc /\ selem acc = poly log (seval r)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val encode_bytes: txt:Seq.seq UInt8.t -> GTot (text) (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then
    Seq.createEmpty
  else
    let l0 = FStar.Math.Lib.min l 16 in
    let w, txt = Seq.split txt l0 in
    Seq.snoc (encode_bytes txt) w

(** Auxiliary lemmas *)

val append_empty: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma
  (requires (Seq.length s1 == 0))
  (ensures  (Seq.append s1 s2 == s2))
  [SMTPat (Seq.append s1 s2); SMTPatT (Seq.length s1 == 0)]
let append_empty #a s1 s2 =
  Seq.lemma_eq_intro (Seq.append s1 s2) s2

val append_cons_snoc: #a:Type -> s1:Seq.seq a -> hd:a -> tl:Seq.seq a -> Lemma
  (Seq.append s1 (Seq.cons hd tl) ==
   Seq.append (Seq.snoc s1 hd) tl)
let append_cons_snoc #a s1 hd tl =
  Seq.lemma_eq_intro
    (Seq.append s1 (Seq.cons hd tl))
    (Seq.append (Seq.snoc s1 hd) tl)

val snoc_cons: #a:Type -> s:Seq.seq a -> x:a -> y:a -> Lemma
  (FStar.Seq.(Seq.equal (snoc (cons x s) y) (cons x (snoc s y))))
let snoc_cons #a s x y = ()

val append_assoc: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> s3:Seq.seq a -> Lemma
  (FStar.Seq.(equal (append s1 (append s2 s3)) (append (append s1 s2) s3)))
let append_assoc #a s1 s2 s3 = ()

val append_as_seq_sub: h:mem -> n:UInt32.t -> m:UInt32.t -> msg:Buffer.buffer H8.t{Buffer.live h msg /\ U32.v m <= U32.v n /\ U32.v n <= Buffer.length msg} -> Lemma
  (append (Buffer.as_seq h (Buffer.sub msg 0ul m))
          (Buffer.as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32.sub n m))) ==
   Buffer.as_seq h (Buffer.sub msg 0ul n))
let append_as_seq_sub h n m msg =
  Seq.lemma_eq_intro
    (append (Buffer.as_seq h (Buffer.sub msg 0ul m))
            (Buffer.as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32.sub n m))))
     (Buffer.as_seq h (Buffer.sub msg 0ul n))

val append_as_seq: h:mem -> m:UInt32.t -> n:UInt32.t ->
  msg:Buffer.buffer H8.t{Buffer.live h msg /\ U32.v m + U32.v n == Buffer.length msg} -> Lemma
  (Seq.equal
    (append (Buffer.as_seq h (Buffer.sub msg 0ul m)) (Buffer.as_seq h (Buffer.sub msg m n)))
    (Buffer.as_seq h msg))
let append_as_seq h n m msg = ()


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

val encode_bytes_empty: txt:Seq.seq UInt8.t -> Lemma
    (requires Seq.length txt == 0)
    (ensures  encode_bytes txt == Seq.createEmpty)
    [SMTPat (encode_bytes txt); SMTPatT (Seq.length txt == 0)]
let encode_bytes_empty txt = ()

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val snoc_encode_bytes: s:Seq.seq UInt8.t -> w:word_16 -> Lemma
  (Seq.equal (Seq.snoc (encode_bytes s) w) (encode_bytes (Seq.append w s)))
let snoc_encode_bytes s w =
  let txt0, txt1 = Seq.split (Seq.append w s) 16 in
  assert (Seq.equal w txt0 /\ Seq.equal s txt1)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val encode_bytes_append: len:U32.t -> s:Seq.seq UInt8.t -> w:word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == U32.v len /\ U32.rem len 16ul == 0ul))
  (ensures  (Seq.equal (encode_bytes (Seq.append s w))
                      (Seq.cons w (encode_bytes s))))
  (decreases (Seq.length s))
let rec encode_bytes_append len s w =
  let open FStar.Seq in
  let open FStar.Seq in
  let txt = Seq.append s w in
  lemma_len_append s w;
  let l0 = Math.Lib.min (length txt) 16 in
  let w', txt = split_eq txt l0 in
  if length s = 0 then
    begin
    assert (equal w w');
    encode_bytes_empty txt
    end
  else
    begin
    assert (l0 == 16);
    let w0, s' = split_eq s 16 in
    snoc_encode_bytes (append s' w) w0;
    append_assoc w0 s' w;
    snoc_cons (encode_bytes s') w w0;
    encode_bytes_append (U32.(len -^ 16ul)) s' w
    end


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val lemma_append_empty: #a:Type -> s:seq a -> Lemma
  (s @| createEmpty #a == s)
let lemma_append_empty #a s = Seq.lemma_eq_intro s (s @| createEmpty #a)




(* val poly1305_blocks_spec_: *)
(*   st:poly1305_state_{invariant st} -> *)
(*   m:Seq.seq H8.t -> *)
(*   len:U64.t{16 * U64.v len = Seq.length m /\ Seq.length m >= 16} -> *)
(*   Tot (st':poly1305_state_{ *)
(*     let log' = MkState?.log st' in *)
(*     let log  = MkState?.log st in *)
(*     let acc' = MkState?.h st' in *)
(*     let acc  = MkState?.h st in *)
(*     let r    = MkState?.r st in *)
(*     log' == log @| encode_bytes m *)
(*     /\ selem acc' = poly log' (seval r) *)
(*   }) *)
(* let poly1305_blocks_spec_ st m len = *)
(*   cut (U64.v len >= 1); *)
(*   let log = MkState?.log st in *)
(*   let acc = MkState?.h st in *)
(*   let r   = MkState?.r st in *)
(*   let block  = slice m 0 16 in *)
(*   let m'     = slice m 16 (length m) in *)
(*   let st'    = poly1305_update_spec st block in *)
(*   let len'   = U64.(len -^ 1uL) in *)
(*   let log'   = MkState?.log st' in *)
(*   let acc'   = MkState?.h st' in *)
(*   cut (log' == log @| Seq.create 1 block); *)
(*   Math.Lemmas.modulo_lemma (seval r) (prime); *)
(*   cut (selem acc' = poly log' (seval r)); admit() *)
(*   append_cons_snoc log block (encode_bytes m'); *)
(*   (\* append_cons_snoc (encode_bytes m') m log; *\) *)
(*   let st'' = poly1305_blocks_spec st' m' len in *)
(*   st'') *)
     

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

private let lemma_tl (log:log_t) (m:word_16) (log':log_t) : Lemma
  (requires (log' == create 1 m @| log))
  (ensures (length log' > 0 /\ (Seq.tail log' == log) /\ (Seq.head log' == m)))
  = Seq.lemma_eq_intro (tail log') log;
    cut (Seq.index log' 0 == m)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

private let poly_def_0 (log:log_t{length log = 0}) (r:elem) : Lemma
  (poly log r = zero)
   = ()

private let poly_def_1 (log:log_t{length log > 0}) (r:elem) : Lemma
  (let hd = Seq.head log in
   let tl = Seq.tail log in
   poly log r = (poly tl r +@ encode hd) *@ r)
   = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val lemma_poly1305_blocks_spec_1:
  m:word_16 ->
  log:log_t -> log':log_t ->
  acc:elem -> r:elem -> acc':elem ->
  Lemma (requires (acc = poly log r /\ (log' == append (create 1 m) log) /\ acc' = ((acc +@ encode m) *@ r)))
        (ensures (acc' = poly log' r))
let lemma_poly1305_blocks_spec_1 m log log' acc r acc' =
  lemma_tl log m log';
  poly_def_1 log' r;
  cut (poly log' r = (poly log r +@ encode m) *@ r)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val lemma_poly1305_blocks_spec_2:
  m:Seq.seq H8.t ->
  len:U64.t{16 * U64.v len = Seq.length m /\ length m >= 16} ->
  log:log_t -> log':log_t -> log'':log_t ->
  acc:elem -> acc':elem -> acc'':elem -> r:elem ->
  Lemma (requires (
      let block = slice m 0 16 in let m' = slice m 16 (length m) in
      let log' = create 1 block @| log in
      let log'' = encode_bytes m' @| log' in
      acc = poly log r /\ acc' = (acc +@ encode block) *@ r
      /\ acc'' = poly log'' r))
    (ensures (
      let block = slice m 0 16 in let m' = slice m 16 (length m) in
      let log' = create 1 block @| log in
      let log'' = encode_bytes m' @| log' in
      acc = poly log r /\ acc' = (acc +@ encode block) *@ r
      /\ acc'' = poly log'' r
      /\ log'' == encode_bytes m @| log))
let lemma_poly1305_blocks_spec_2 m len log log' log'' acc acc' acc'' r =
  let block = slice m 0 16 in let m' = slice m 16 (length m) in
  let log' = create 1 block @| log in
  let log'' = encode_bytes m' @| log' in
  snoc_encode_bytes m' block;
  lemma_eq_intro (append block m') m;
  lemma_eq_intro (encode_bytes m' @| create 1 block) (encode_bytes m);
  cut (encode_bytes m == Seq.snoc (encode_bytes m') block);
  append_cons_snoc (encode_bytes m') block log
  

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

val poly1305_blocks_spec:
  st:poly1305_state_{invariant st} ->
  m:Seq.seq H8.t ->
  len:U64.t{16 * U64.v len = Seq.length m} ->
  Tot (st':poly1305_state_{
    let log' = MkState?.log st' in
    let log  = MkState?.log st in
    let acc' = MkState?.h st' in
    let acc  = MkState?.h st in
    let r    = MkState?.r st in
    log' == encode_bytes m @| log
    /\ selem acc' = poly log' (seval r)
  })
  (decreases (U64.v len))
let rec poly1305_blocks_spec st m len =
  let log = MkState?.log st in
  let acc = MkState?.h st in
  let r   = MkState?.r st in
  if U64.(len =^ 0uL) then (
    admit();
    encode_bytes_empty m; lemma_append_empty log;
    st
  )
  else (
    cut (U64.v len >= 1);
    let block  = slice m 0 16 in
    let m'     = slice m 16 (length m) in
    let st'    = poly1305_update_spec st block in
    let len'   = U64.(len -^ 1uL) in
    let log'   = MkState?.log st' in
    cut (log' == Seq.cons block log);
    let acc'   = MkState?.h st' in
    Math.Lemmas.modulo_lemma (seval r) (prime);
    lemma_poly1305_blocks_spec_1 block log log' (selem acc) (seval r) (selem acc');
    cut (invariant st');
    append_cons_snoc (encode_bytes m') block log;
    snoc_encode_bytes m' block;
    let st'' = poly1305_blocks_spec st' m' len' in
    let log'' = MkState?.log st'' in
    let acc'' = MkState?.h st'' in
    lemma_poly1305_blocks_spec_2 m len log log' log'' (selem acc) (selem acc') (selem acc'') (seval r);
    st'')


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 10"

assume val lemma_msg_to_text_eq_encode_bytes: msg:bytes{length msg > 0} -> Lemma (encode_bytes msg == msg_to_text msg)
(* let rec lemma_msg_to_text_eq_encode_bytes msg = *)
(*   if length msg <= 16 then ( *)
(*     lemma_eq_intro msg (slice msg 0 (Math.Lib.min 16 (length msg))); *)
(*     lemma_eq_intro (msg @| createEmpty) msg *)
(*   ) *)
(*   else admit() *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val crypto_onetimeauth_spec:
  input:Seq.seq H8.t ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= Seq.length input} ->
  k:Seq.seq H8.t{Seq.length k = 32} ->
  Tot (mac:Seq.seq H8.t{Seq.length mac = 16
    /\ mac == poly1305 input k})
let crypto_onetimeauth_spec input len k =
  let kr, ks = split k 16 in
  let len16 = U64.(len >>^  4ul) in
  let rem16 = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U64.v len) 4;
  let part_input, last_block = split input (16 * U64.v len16) in
  let init_st = poly1305_init_spec kr in
  assert_norm(pow2 128 < pow2 130 - 5);
  poly_def_0 (MkState?.log init_st) (seval (MkState?.r init_st));
  cut (invariant init_st);
  let partial_st = poly1305_blocks_spec init_st part_input len16 in
  admit(); // TODO: finish
  poly1305_finish_spec partial_st last_block rem16 ks
