module Hacl.Spe.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
open FStar.Seq
open FStar.Endianness
open FStar.Int.Cast

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Endianness
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Spec.Poly1305
open Hacl.Spec.Poly1305_64

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"

val poly1305_init_spec: key:Seq.seq H8.t{Seq.length key = 16} ->
  Tot (st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)
    /\ seval (MkState?.r st) = UInt.logand #128 (hlittle_endian key) 0x0ffffffc0ffffffc0ffffffc0fffffff
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
   let block = hlittle_endian block + pow2 128 in
   ((acc0 + block) * r0) % prime = (((acc0 % prime) +@ (block % prime)) *@ (r0 % prime)))
private let lemma_mod_distr_seq acc block r =
  let acc0 = seval acc in let r0 = seval r in
  let block = hlittle_endian block + pow2 128 in
  lemma_mod_distr acc0 block r0


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

val poly1305_update_spec: st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word_16 ->
  Tot (st':poly1305_state_{red_44 (MkState?.r st') /\ red_45 (MkState?.h st')
    /\ (let acc0 = seval (MkState?.h st) % prime in
       let acc1 = seval (MkState?.h st') % prime in
       let r0 = seval (MkState?.r st) % prime in
       let r1 = seval (MkState?.r st') % prime in
       let log0:seq word = (MkState?.log st) in
       let log1 = (MkState?.log st') in
       let block  = (hlittle_endian m + pow2 128) in
       r0 = r1 /\ acc1  = ((acc0 +@ block) *@ r0)
       /\ (log1 == (Seq.create 1 m) @| log0))})
let poly1305_update_spec st m =
  lemma_mod_distr_seq (MkState?.h st) m (MkState?.r st);
  poly1305_update_spec st m


val poly1305_finish_spec:
  st:poly1305_state_{red_44 (MkState?.r st) /\ red_45 (MkState?.h st)} ->
  m:word ->
  rem':U64.t{U64.v rem' = length m /\ length m < 16} ->
  key_s:Seq.seq H8.t{Seq.length key_s = 16} ->
  Tot (mac:word_16{
      (let acc = seval (MkState?.h st) % prime in
       let r   = seval (MkState?.r st) % prime in
       let k   = hlittle_endian key_s   in
       let m'   = (hlittle_endian m + pow2 (8*length m)) % prime in
       (* let mac = hlittle_endian mac in *)
       (* if Seq.length m >= 1 *)
       (* then mac = (((acc +@ m') *@ r) + k) % pow2 128 *)
       (* else mac = ((acc + k) % pow2 128)) }) *)
       if Seq.length m >= 1
       then reveal_sbytes mac == finish ((acc +@ m') *@ r) (reveal_sbytes key_s)
       else reveal_sbytes mac == finish acc (reveal_sbytes key_s)) })
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let poly1305_finish_spec st m rem' key_s =
  if Seq.length m >= 1 then (
    lemma_mod_distr (seval (MkState?.h st)) (hlittle_endian m + pow2 (8*length m)) (seval (MkState?.r st))
  );
  let mac = poly1305_finish_spec st m rem' key_s in
  if Seq.length m >= 1 then (
    cut (let mac = hlittle_endian mac in
         let acc = seval (MkState?.h st) % prime in
         let r   = seval (MkState?.r st) % prime in
         let k   = hlittle_endian key_s   in
         let m'   = (hlittle_endian m + pow2 (8*length m)) % prime in
         mac = (((acc +@ m') *@ r) + k) % pow2 128);
    cut (let mac = hlittle_endian mac in
         let acc = seval (MkState?.h st) % prime in
         let r   = seval (MkState?.r st) % prime in
         let k   = hlittle_endian key_s   in
         let m'   = (hlittle_endian m + pow2 (8*length m)) % prime in
         little_endian (finish ((acc +@ m') *@ r) (reveal_sbytes key_s)) = (((acc +@ m') *@ r) + k) % pow2 128);
    lemma_little_endian_inj (reveal_sbytes mac) (finish ((selem (MkState?.h st) +@ ((hlittle_endian m + pow2 (8*length m)) % prime)) *@ (selem (MkState?.r st))) (reveal_sbytes key_s))
  )
  else lemma_little_endian_inj (reveal_sbytes mac) (finish (selem (MkState?.h st)) (reveal_sbytes key_s));
  mac


(* *************************** *)
(* Standalone poly1305 version *)
(* *************************** *)


unfold inline_for_extraction let encode (w:word) : GTot elem = encode (reveal_sbytes w)


(* val poly: vs:text -> r:elem -> GTot (a:elem) *)
(* let poly vs r = *)
(* poly vs r *)

val poly: vs:text -> r:elem -> GTot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r


let invariant (st:poly1305_state_) : GTot Type0 =
  let acc = (MkState?.h st) in let r = (MkState?.r st) in let log = MkState?.log st in
  seval r < pow2 130 - 5 /\  red_44 r /\ red_45 acc /\ selem acc = poly log (seval r)


val encode_bytes: txt:Seq.seq H8.t -> GTot (text) (decreases (Seq.length txt))
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


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val encode_bytes_empty: txt:Seq.seq H8.t -> Lemma
    (requires Seq.length txt == 0)
    (ensures  encode_bytes txt == Seq.createEmpty)
    [SMTPat (encode_bytes txt); SMTPatT (Seq.length txt == 0)]
let encode_bytes_empty txt = ()

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

val snoc_encode_bytes: s:Seq.seq H8.t -> w:word_16 -> Lemma
  (Seq.equal (Seq.snoc (encode_bytes s) w) (encode_bytes (Seq.append w s)))
let snoc_encode_bytes s w =
  let txt0, txt1 = Seq.split (Seq.append w s) 16 in
  assert (Seq.equal w txt0 /\ Seq.equal s txt1)

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

val encode_bytes_append: len:U32.t -> s:Seq.seq H8.t -> w:word -> Lemma
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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_append_empty: #a:Type -> s:seq a -> Lemma
  (s @| createEmpty #a == s)
let lemma_append_empty #a s = Seq.lemma_eq_intro s (s @| createEmpty #a)
     

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private let lemma_tl (log:log_t) (m:word_16) (log':log_t) : Lemma
  (requires (log' == create 1 m @| log))
  (ensures (length log' > 0 /\ (Seq.tail log' == log) /\ (Seq.head log' == m)))
  = Seq.lemma_eq_intro (tail log') log;
    cut (Seq.index log' 0 == m)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

private let poly_def_0 (log:log_t{length log = 0}) (r:elem) : Lemma
  (poly log r = zero)
   = ()

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let poly_def_1 (log:log_t{length log > 0}) (r:elem) : Lemma
  (let hd = Seq.head log in
   let tl = Seq.tail log in
   poly log r = (poly tl r +@ encode hd) *@ r)
   = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

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
  

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 1000"

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
    invariant st'
    /\ log' == encode_bytes m @| log
    /\ selem acc' = poly log' (seval r)
  })
  (decreases (U64.v len))
let rec poly1305_blocks_spec st m len =
  let log = MkState?.log st in
  let acc = MkState?.h st in
  let r   = MkState?.r st in
  if U64.(len =^ 0uL) then (
    encode_bytes_empty m; lemma_append_empty log;
    Seq.lemma_eq_intro log (encode_bytes m @| log);
    cut(log == encode_bytes m @| log);
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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* assume val lemma_onetimeauth_finish_1: *)
(*   input:Seq.seq H8.t{Seq.length input > 0} -> *)
(*   len:U64.t{U64.v len < pow2 32 /\ U64.v len = Seq.length input} -> *)
(*   Lemma ( *)
(*     let l = 16 * (U64.v len / 16) in *)
(*     let i1, i2 = split input l in *)
(*     msg_to_text (reveal_sbytes input) == encode_bytes (input) *)
(*     /\ (if l = U64.v len then encode_bytes input == encode_bytes i1 *)
(*        else encode_bytes input == Seq.create 1 i2 @| encode_bytes i1)) *)

(* assume val lemma_onetimeauth_finish_2: *)
(*   input:Seq.seq H8.t{Seq.length input > 0} ->   *)
(*   len:U64.t{U64.v len < pow2 32 /\ U64.v len = Seq.length input /\ U64.v len % 16 > 0} -> *)
(*   r:elem -> *)
(*   Lemma ( *)
(*     let l = 16 * (U64.v len / 16) in *)
(*     let i1, i2 = split input l in *)
(*     let block = (hlittle_endian i2 + pow2 (8*length i2)) % prime in *)
(*     poly (encode_bytes input) r = (poly (encode_bytes i1) r +@ block) *@ r) *)
  

(* #reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100" *)
(* let lemma_onetimeauth_finish input len = () *)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

val crypto_onetimeauth_spec:
  input:Seq.seq H8.t{Seq.length input > 0} ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len = Seq.length input} ->
  k:Seq.seq H8.t{Seq.length k = 32} ->
  Tot (mac:Seq.seq H8.t{Seq.length mac = 16
    /\ reveal_sbytes mac == poly1305 (reveal_sbytes input) (reveal_sbytes k)})
let crypto_onetimeauth_spec input len k =
  let kr, ks = split k 16 in
  let len16 = U64.(len >>^  4ul) in
  let rem16 = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U64.v len) 4;
  assert_norm(pow2 4 = 16);
  cut (U64.v len = 16 * U64.v len16 + U64.v rem16);
  Math.Lemmas.lemma_div_mod (U64.v len) 16;
  let part_input, last_block = split input (16 * U64.v len16) in
  (* cut (Seq.length last_block < 16); *)
  let init_st = poly1305_init_spec kr in
  assert_norm(pow2 128 < pow2 130 - 5);
  poly_def_0 (MkState?.log init_st) (seval (MkState?.r init_st));
  cut (invariant init_st);
  let partial_st = poly1305_blocks_spec init_st part_input len16 in
  cut (invariant partial_st);
  let mac = poly1305_finish_spec partial_st last_block rem16 ks in
  (* lemma_onetimeauth_finish_1 input len; *)
  (* if U64.v rem16 > 0 then lemma_onetimeauth_finish_2 input len (selem (MkState?.r init_st)); *)
  (* assert(mac == finish (poly (encode_bytes input) (encode_r kr)) ks); *)
  FStar.Endianness.lemma_little_endian_inj (reveal_sbytes mac) (poly1305 (reveal_sbytes input) (reveal_sbytes k));
  mac
