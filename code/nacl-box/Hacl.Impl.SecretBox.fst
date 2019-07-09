module Hacl.Impl.SecretBox

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Salsa20
open Hacl.Poly1305_32
module Spec = Spec.SecretBox
module LibSeq = Lib.Sequence


#set-options "--z3rlimit  100 --max_fuel 0 --max_ifuel 0"
let lbytebuf (x:size_t) = lbuffer uint8 x
val secretbox_init: xkeys:lbytebuf 96ul -> k:lbytebuf 32ul -> n:lbytebuf 24ul ->
		    Stack unit
		    (requires (fun h -> live h xkeys /\ live h k /\ live h n /\
				     disjoint k xkeys /\ disjoint n xkeys))
		    (ensures (fun h0 _ h1 -> modifies (loc xkeys) h0 h1 /\
		      (let xkeys = as_seq h1 xkeys in
		       let subkey : Spec.key = LibSeq.sub xkeys 0 32 in
		       let aekey : Spec.aekey = LibSeq.sub xkeys 32 64 in
		       (subkey, aekey) ==
		       Spec.secretbox_init (as_seq h0 k) (as_seq h0 n))))
let secretbox_init xkeys k n =
    let h0 = ST.get() in
    let subkey = sub xkeys 0ul 32ul in
    let aekey = sub xkeys 32ul 64ul in
    let n0 = sub n 0ul 16ul in
    let n1 = sub n 16ul 8ul in
    Hacl.Impl.HSalsa20.hsalsa20 subkey k n0;
    Hacl.Impl.Salsa20.salsa20_key_block0 aekey subkey n1

val secretbox_detached: mlen:size_t -> c:lbuffer uint8 mlen -> tag:lbuffer uint8 16ul ->
			k:lbytebuf 32ul -> n:lbytebuf 24ul ->
			m:lbuffer uint8 mlen ->
			Stack unit
			(requires (fun h -> live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
				   disjoint tag c /\ eq_or_disjoint m c))
			(ensures (fun h0 _ h1 -> modifies (loc c |+| loc tag) h0 h1))
			(*
			/\
			  (as_seq h1 tag,as_seq h1 c) ==
			   Spec.secretbox_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))) *)
#set-options "--z3rlimit  300"
let secretbox_detached mlen c tag k n m =
    let h0_ = ST.get() in
    push_frame();
    let n1 = sub n 16ul 8ul in
    let xkeys = create 96ul (u8 0) in
    let subkey = sub xkeys 0ul 32ul in
    let mkey = sub xkeys 32ul 32ul in
    let ekey0 = sub xkeys 64ul 32ul in
    let block0 = create 32ul (u8 0) in
    let h0 = ST.get() in
    let mlen0 = if mlen <. 32ul then mlen else 32ul in
    let mlen1 = mlen -! mlen0 in
    let m0 = sub m 0ul mlen0 in
    let m1 = sub m mlen0 mlen1 in
    let c0 = sub c 0ul mlen0 in
    let c1 = sub c mlen0 mlen1 in
    secretbox_init xkeys k n;
    let h1 = ST.get() in
    assert (modifies (loc xkeys) h0 h1);
    copy (sub block0 0ul mlen0) m0;
    let h1 = ST.get() in
    assert (modifies (loc xkeys |+| loc block0) h0 h1);
    map2T 32ul block0 ( ^. ) block0 ekey0;
    let h1 = ST.get() in
    assert (modifies (loc xkeys |+| loc block0) h0 h1);
    copy c0 (sub block0 0ul mlen0);
    let h1 = ST.get() in
    assert (modifies ((loc xkeys |+| loc block0) |+| loc c) h0 h1);
    Hacl.Impl.Salsa20.salsa20_encrypt mlen1 c1 m1 subkey n1 1ul;
    let h1 = ST.get() in
    assert (modifies ((loc xkeys |+| loc block0) |+| loc c) h0 h1);
    Hacl.Poly1305_32.poly1305_mac tag mlen c mkey;
    let h1 = ST.get() in
    assert (modifies (((loc xkeys |+| loc block0) |+| loc c) |+| loc tag) h0 h1);
    pop_frame();
    let h1_ = ST.get() in
    assert (modifies (loc c |+| loc tag) h0_ h1_)


val secretbox_open_detached: mlen:size_t -> m:lbuffer uint8 mlen ->
			k:lbytebuf 32ul -> n:lbytebuf 24ul ->
			c:lbuffer uint8 mlen ->
			tag:lbuffer uint8 16ul ->
			Stack size_t
			(requires (fun h -> live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
				   disjoint tag c /\ eq_or_disjoint m c))
			(ensures (fun h0 _ h1 -> modifies (loc m) h0 h1))
			(*
			/\
			  (as_seq h1 tag,as_seq h1 m) ==
			   Spec.secretbox_open_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq h0 c))) *)
let secretbox_open_detached mlen m k n c tag =
    push_frame();
    let n1 = sub n 16ul 8ul in
    let xkeys = create 96ul (u8 0) in
    let subkey = sub xkeys 0ul 32ul in
    let mkey = sub xkeys 32ul 32ul in
    let ekey0 = sub xkeys 64ul 32ul in
    let block0 = create 32ul (u8 0) in
    let tag' = create 16ul (u8 0) in
    let h0 = ST.get() in
    let mlen0 = if mlen <. 32ul then mlen else 32ul in
    let mlen1 = mlen -! mlen0 in
    let m0 = sub m 0ul mlen0 in
    let m1 = sub m mlen0 mlen1 in
    let c0 = sub c 0ul mlen0 in
    let c1 = sub c mlen0 mlen1 in
    secretbox_init xkeys k n;
    Hacl.Poly1305_32.poly1305_mac tag' mlen c mkey;
    let h1 = ST.get() in
    assert (modifies (loc xkeys |+| loc tag') h0 h1);
    if lbytes_eq tag' tag then (
      copy (sub block0 0ul mlen0) c0;
      map2T 32ul block0 ( ^. ) block0 ekey0;
      copy m0 (sub block0 0ul mlen0);
      Hacl.Impl.Salsa20.salsa20_decrypt mlen1 m1 c1 subkey n1 1ul;
      let h1 = ST.get() in
      assert (modifies (((loc xkeys |+| loc tag') |+| loc block0) |+| loc m) h0 h1);
      pop_frame();
      0ul)
    else (
      pop_frame();
      0xfffffffful)

val secretbox_easy: mlen:size_t{v mlen + 16 <= max_size_t} -> c:lbuffer uint8 (mlen +! 16ul) ->
			k:lbytebuf 32ul -> n:lbytebuf 24ul ->
			m:lbuffer uint8 mlen ->
			Stack unit
			(requires (fun h -> live h c /\ live h m /\ live h k /\ live h n /\
				         disjoint m c))
			(ensures (fun h0 _ h1 -> modifies (loc c) h0 h1))
			(*
			/\
			  as_seq h1 c ==
			   Spec.secretbox_easy (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))) *)
let secretbox_easy mlen c k n m =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  secretbox_detached mlen cip tag k n m

val secretbox_open_easy: mlen:size_t{v mlen + 16 <= max_size_t} -> m:lbuffer uint8 mlen ->
			k:lbytebuf 32ul -> n:lbytebuf 24ul ->
			c:lbuffer uint8 (mlen +! 16ul) ->
			Stack size_t
			(requires (fun h -> live h c /\ live h m /\ live h k /\ live h n /\
				         disjoint m c))
			(ensures (fun h0 _ h1 -> modifies (loc m) h0 h1))
			(*
			/\
			  as_seq h1 c ==
			   Spec.secretbox_easy (as_seq h0 k) (as_seq h0 n) (as_seq h0 m))) *)
let secretbox_open_easy mlen m k n c =
  let tag = sub c 0ul 16ul in
  let cip = sub c 16ul mlen in
  secretbox_open_detached mlen m k n cip tag

