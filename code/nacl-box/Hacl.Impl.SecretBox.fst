module Hacl.Impl.SecretBox

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Salsa20
open Hacl.Poly1305_32

module ST = FStar.HyperStack.ST
module Spec = Spec.SecretBox
module LSeq = Lib.Sequence


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val secretbox_init:
    xkeys:lbuffer uint8 96ul
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul ->
  Stack unit
  (requires fun h ->
    live h xkeys /\ live h k /\ live h n /\
    disjoint k xkeys /\ disjoint n xkeys)
  (ensures  fun h0 _ h1 ->
    modifies (loc xkeys) h0 h1 /\
    (let xkeys = as_seq h1 xkeys in
    let subkey : Spec.key = LSeq.sub xkeys 0 32 in
    let aekey : Spec.aekey = LSeq.sub xkeys 32 64 in
    (subkey, aekey) == Spec.secretbox_init (as_seq h0 k) (as_seq h0 n)))

let secretbox_init xkeys k n =
  let h0 = ST.get() in
  let subkey = sub xkeys 0ul 32ul in
  let aekey = sub xkeys 32ul 64ul in
  let n0 = sub n 0ul 16ul in
  let n1 = sub n 16ul 8ul in
  hsalsa20 subkey k n0;
  salsa20_key_block0 aekey subkey n1


inline_for_extraction noextract
let get_len0 (len:size_t) : Tot (r:size_t{v r <= 32 /\ v r == Spec.get_len0 (v len)}) =
  if len <=. 32ul then len else 32ul


#set-options "--z3rlimit 100"

inline_for_extraction noextract
val secretbox_detached_cipher:
    mlen:size_t
  -> c:lbuffer uint8 mlen
  -> k:lbuffer uint8 32ul
  -> xkeys:lbuffer uint8 96ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h xkeys /\ live h n /\ live h k /\
    eq_or_disjoint m c /\ disjoint xkeys c /\ disjoint xkeys m /\
    disjoint n m /\ disjoint n c /\
    (let subkey : Spec.key = LSeq.sub (as_seq h xkeys) 0 32 in
    let aekey : Spec.aekey = LSeq.sub (as_seq h xkeys) 32 64 in
    (subkey, aekey) == Spec.secretbox_init (as_seq h k) (as_seq h n)))
  (ensures  fun h0 _ h1 -> modifies (loc c) h0 h1 /\
    (let (tag, cipher) = Spec.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) in
     as_seq h1 c == cipher))

let secretbox_detached_cipher mlen c k xkeys n m =
  let h0 = ST.get () in
  push_frame ();
  let n1 = sub n 16ul 8ul in
  let subkey = sub xkeys 0ul 32ul in
  let mkey = sub xkeys 32ul 32ul in
  let ekey0 = sub xkeys 64ul 32ul in

  let mlen0 = get_len0 mlen in
  let mlen1 = mlen -! mlen0 in
  let m0 = sub m 0ul mlen0 in
  let m1 = sub m mlen0 mlen1 in

  let block0 = create 32ul (u8 0) in
  update_sub block0 0ul mlen0 m0;
  map2T 32ul block0 ( ^. ) block0 ekey0;

  let c0 = sub c 0ul mlen0 in
  let c1 = sub c mlen0 mlen1 in
  let h1 = ST.get () in
  copy c0 (sub block0 0ul mlen0);
  let h2 = ST.get () in
  //assert (as_seq h2 c0 == LSeq.sub (as_seq h1 block0) 0 (v mlen0));
  salsa20_encrypt mlen1 c1 m1 subkey n1 1ul;
  let h3 = ST.get () in
  //assert (as_seq h3 c1 == Spec.Salsa20.salsa20_encrypt_bytes (as_seq h2 subkey) (as_seq h2 n1) 1 (as_seq h2 m1));
  FStar.Seq.Properties.lemma_split (as_seq h3 c) (v mlen0);
  //FStar.Seq.Properties.lemma_split (Seq.append (as_seq h2 c0) (as_seq h3 c1)) (v mlen0);
  assert (as_seq h3 c == Seq.append (as_seq h2 c0) (as_seq h3 c1));
  assert (
    let (tag, cipher) = Spec.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) in
    as_seq h3 c == cipher);
  pop_frame ()


val secretbox_detached:
    mlen:size_t
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ disjoint tag m /\ eq_or_disjoint m c /\
    disjoint n m /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc c |+| loc tag) h0 h1 /\
    (as_seq h1 tag, as_seq h1 c) == Spec.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))

let secretbox_detached mlen c tag k n m =
  let h0 = ST.get () in
  push_frame();
  let xkeys = create 96ul (u8 0) in
  secretbox_init xkeys k n;
  let mkey = sub xkeys 32ul 32ul in
  secretbox_detached_cipher mlen c k xkeys n m;
  poly1305_mac tag mlen c mkey;
  let h1 = ST.get () in
  assert (
    let (tag1, cipher) = Spec.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) in
    (as_seq h1 tag, as_seq h1 c) == (tag1, cipher));
  pop_frame()


inline_for_extraction noextract
val secretbox_open_detached_plain:
    mlen:size_t
  -> m:lbuffer uint8 mlen
  -> xkeys:lbuffer uint8 96ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h xkeys /\ live h n /\
    disjoint m n /\ disjoint c n /\ eq_or_disjoint m c /\
    disjoint xkeys m /\ disjoint xkeys c)
  (ensures fun h0 r h1 -> modifies (loc m) h0 h1 /\
    (let subkey = LSeq.sub (as_seq h0 xkeys) 0 32 in
    let ekey0 = LSeq.sub (as_seq h0 xkeys) 64 32 in
    let n1 = LSeq.sub (as_seq h0 n) 16 8 in
    let clen0 = Spec.get_len0 (v mlen) in
    let clen1 = v mlen - clen0 in
    let c0 = LSeq.sub (as_seq h0 c) 0 clen0 in
    let c1 = LSeq.sub (as_seq h0 c) clen0 clen1 in

    let block0 = LSeq.create 32 (u8 0) in
    let block0 = LSeq.update_sub block0 0 clen0 c0 in
    let block0 = LSeq.map2 (^.) block0 ekey0 in

    let m0 = LSeq.sub block0 0 clen0 in
    let m1 = Spec.Salsa20.salsa20_decrypt_bytes subkey n1 1 c1 in
    let msg = Seq.append m0 m1 in
    as_seq h1 m == msg))

let secretbox_open_detached_plain mlen m xkeys n c =
  push_frame ();
  let subkey = sub xkeys 0ul 32ul in
  let ekey0 = sub xkeys 64ul 32ul in
  let n1 = sub n 16ul 8ul in

  let mlen0 = get_len0 mlen in
  let mlen1 = mlen -! mlen0 in
  let c0 = sub c 0ul mlen0 in
  let c1 = sub c mlen0 mlen1 in

  let block0 = create 32ul (u8 0) in
  update_sub block0 0ul mlen0 c0;
  map2T 32ul block0 ( ^. ) block0 ekey0;

  let m0 = sub m 0ul mlen0 in
  let m1 = sub m mlen0 mlen1 in
  copy m0 (sub block0 0ul mlen0);
  salsa20_decrypt mlen1 m1 c1 subkey n1 1ul;
  let h1 = ST.get () in
  FStar.Seq.Properties.lemma_split (as_seq h1 m) (v mlen0);
  pop_frame ()


val secretbox_open_detached:
    mlen:size_t
  -> m:lbuffer uint8 mlen
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 mlen
  -> tag:lbuffer uint8 16ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ disjoint tag m /\ disjoint m n /\ disjoint c n /\ eq_or_disjoint m c)
  (ensures fun h0 r h1 -> modifies (loc m) h0 h1 /\
    (let msg = Spec.secretbox_open_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

let secretbox_open_detached mlen m k n c tag =
  push_frame();
  let xkeys = create 96ul (u8 0) in
  secretbox_init xkeys k n;
  let mkey = sub xkeys 32ul 32ul in

  let tag' = create 16ul (u8 0) in
  Hacl.Poly1305_32.poly1305_mac tag' mlen c mkey;

  let res =
    if lbytes_eq tag tag' then (
      secretbox_open_detached_plain mlen m xkeys n c;
      0ul)
    else
      0xfffffffful in
  pop_frame ();
  res


val secretbox_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> c:lbuffer uint8 (mlen +! 16ul)
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> m:lbuffer uint8 mlen ->
  Stack unit
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 _ h1 -> modifies (loc c) h0 h1 /\
    as_seq h1 c == Spec.secretbox_easy (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))

let secretbox_easy mlen c k n m =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  secretbox_detached mlen cip tag k n m;
  let h1 = ST.get () in
  FStar.Seq.Properties.lemma_split (as_seq h1 c) 16


val secretbox_open_easy:
    mlen:size_t{v mlen + 16 <= max_size_t}
  -> m:lbuffer uint8 mlen
  -> k:lbuffer uint8 32ul
  -> n:lbuffer uint8 24ul
  -> c:lbuffer uint8 (mlen +! 16ul) ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies (loc m) h0 h1 /\
   (let msg = Spec.secretbox_open_easy (as_seq h0 k) (as_seq h0 n) (as_seq h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq h1 m == Some?.v msg
    | _ -> None? msg))

let secretbox_open_easy mlen m k n c =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  secretbox_open_detached mlen m k n cip tag
