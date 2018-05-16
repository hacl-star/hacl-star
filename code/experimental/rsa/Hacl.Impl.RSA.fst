module Hacl.Impl.RSA

open FStar.HyperStack.All
open FStar.Mul
open Spec.Lib.Loops
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf
open Spec.Lib.IntTypes

open Hacl.Impl.Lib
open Hacl.Impl.MGF
open Hacl.Impl.Comparison
open Hacl.Impl.Convert
open Hacl.Impl.Exponentiation
open Hacl.Impl.Addition
open Hacl.Impl.Multiplication

module Buffer = Spec.Lib.IntBuf

inline_for_extraction
let hLen:size_t = size 32

val xor_bytes:
  #len:size_nat -> clen:size_t{v clen == len} ->
  b1:lbytes len -> b2:lbytes len -> Stack unit
  (requires (fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 b1 h0 h1))
  [@"c_inline"]
let xor_bytes #len clen b1 b2 = map2 #uint8 #uint8 #len clen (fun x y -> logxor #U8 x y) b1 b2

val pss_encode:
  #sLen:size_nat -> #msgLen:size_nat -> #emLen:size_nat ->
  ssLen:size_t{v ssLen = sLen /\ 8 + v hLen + sLen < max_size_t} -> salt:lbytes sLen ->
  mmsgLen:size_t{v mmsgLen = msgLen} -> msg:lbytes msgLen ->
  emBits:size_t{v emBits > 0 /\ emLen = v (blocks emBits (size 8)) /\ v hLen + sLen + 2 <= v (blocks emBits (size 8))} ->
  em:lbytes emLen -> Stack unit
  (requires (fun h -> live h salt /\ live h msg /\ live h em /\
		    disjoint msg salt /\ disjoint em msg /\ disjoint em salt))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 em h0 h1))
  [@"c_inline"]
  #reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
let pss_encode #sLen #msgLen #emLen ssLen salt mmsgLen msg emBits em =
  let (emLen:size_t{v emLen > 0}) = blocks emBits (size 8) in
  let (msBits:size_t{v msBits < 8}) = emBits %. (size 8) in

  let m1Len:size_t = add #SIZE (add #SIZE (size 8) hLen) ssLen in
  let (dbLen:size_t{v dbLen > 0}) = sub #SIZE (sub #SIZE emLen hLen) (size 1) in
  //st = [hash(msg); m1; hash(m1); db; dbMask]
  assume (2 * v hLen + 4 + v (blocks dbLen hLen) * v hLen < pow2 32); //for mgf
  assume (v hLen + sLen + 6 + 2 * v emLen < max_size_t);
  let stLen:size_t = add #SIZE (add #SIZE (add #SIZE (add #SIZE hLen m1Len) hLen) dbLen) dbLen in

  alloc #uint8 #unit #(v stLen) stLen (u8 0) [BufItem salt; BufItem msg] [BufItem em]
  (fun h0 _ h1 -> True)
  (fun st ->
    let mHash = Buffer.sub #uint8 #(v stLen) #(v hLen) st (size 0) hLen in
    let m1 = Buffer.sub #uint8 #(v stLen) #(v m1Len) st hLen m1Len in
    let m1Hash = Buffer.sub #uint8 #(v stLen) #(v hLen) st (add #SIZE hLen m1Len) hLen in
    let db = Buffer.sub #uint8 #(v stLen) #(v dbLen) st (add #SIZE (add #SIZE hLen m1Len) hLen) dbLen in
    let dbMask = Buffer.sub #uint8 #(v stLen) #(v dbLen) st (add #SIZE (add #SIZE (add #SIZE hLen m1Len) hLen) dbLen) dbLen in

    hash_sha256 mHash mmsgLen msg;
    let m1_hash = Buffer.sub #uint8 #(v m1Len) #(v hLen) m1 (size 8) hLen in
    copy hLen mHash m1_hash;
    let m1_salt = Buffer.sub #uint8 #(v m1Len) #sLen m1 (add #SIZE (size 8) hLen) ssLen in
    copy ssLen salt m1_salt;
    hash_sha256 m1Hash m1Len m1;

    assert (0 <= v dbLen - sLen - 1);
    let last_before_salt = sub #SIZE (sub #SIZE dbLen ssLen) (size 1) in
    db.(last_before_salt) <- u8 1;
    let db_salt = Buffer.sub #uint8 #(v dbLen) #sLen db (add #SIZE last_before_salt (size 1)) ssLen in
    copy ssLen salt db_salt;
    mgf_sha256 #(v hLen) #(v dbLen) hLen m1Hash dbLen dbMask;
    xor_bytes dbLen db dbMask;

    (if (msBits >. size 0) then begin
      let shift_bits = sub #SIZE (size 8) msBits in
      assert (0 < v shift_bits /\ v shift_bits < 8);
      db.(size 0) <- db.(size 0) &. (shift_right #U8 (u8 0xff) (size_to_uint32 shift_bits))
    end);

    let em_db = Buffer.sub #uint8 #(v emLen) #(v dbLen) em (size 0) dbLen in
    copy dbLen db em_db;
    let em_hash = Buffer.sub #uint8 #(v emLen) #(v hLen) em dbLen hLen in
    copy hLen m1Hash em_hash;
    em.(sub #SIZE emLen (size 1)) <- u8 0xbc
  )

val pss_verify:
  #msgLen:size_nat -> #emLen:size_nat ->
  sLen:size_t{8 + v hLen + v sLen < max_size_t} ->
  mmsgLen:size_t{v mmsgLen = msgLen} -> msg:lbytes msgLen ->
  emBits:size_t{v emBits > 0 /\ emLen = v (blocks emBits (size 8)) /\ v hLen + v sLen + 2 <= v (blocks emBits (size 8))} -> // <- check the last condition before calling this function!
  em:lbytes emLen -> Stack bool
  (requires (fun h -> live h msg /\ live h em /\ disjoint em msg))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))
  [@"c_inline"]
  #reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"
let pss_verify #msgLen #emLen sLen mmsgLen msg emBits em =
  let (emLen:size_t{v emLen > 0}) = blocks emBits (size 8) in
  let (msBits:size_t{v msBits < 8}) = emBits %. (size 8) in

  let em_0 = if (msBits >. size 0) then em.(size 0) &. (shift_left #U8 (u8 0xff) (size_to_uint32 msBits)) else u8 0 in
  let em_last = em.(sub #SIZE emLen (size 1)) in

  let padLen:size_t = sub #SIZE (sub #SIZE (sub #SIZE emLen sLen) hLen) (size 1) in
  let dbLen:size_t = sub #SIZE (sub #SIZE emLen hLen) (size 1) in
  let m1Len:size_t = add #SIZE (add #SIZE (size 8) hLen) sLen in
  assume (4 + 2 * v hLen + v hLen * v (blocks dbLen hLen) < max_size_t);
  //st = [hash(msg); pad; dbMask; m1; hash(m1)]
  let stLen = add #SIZE (add #SIZE (add #SIZE (add #SIZE hLen padLen) dbLen) m1Len) hLen in
  alloc #uint8 #bool #(v stLen) stLen (u8 0) [BufItem em; BufItem msg] []
  (fun h0 _ h1 -> True)
  (fun st ->
    if not ((eq_u8 em_0 (u8 0)) && (eq_u8 em_last (u8 0xbc))) then false
    else begin
      let mHash = Buffer.sub #uint8 #(v stLen) #(v hLen) st (size 0) hLen in
      let pad2 = Buffer.sub #uint8 #(v stLen) #(v padLen) st hLen padLen in
      let dbMask = Buffer.sub #uint8 #(v stLen) #(v dbLen) st (add #SIZE hLen padLen) dbLen in
      let m1 = Buffer.sub #uint8 #(v stLen) #(v m1Len) st (add #SIZE (add #SIZE hLen padLen) dbLen) m1Len in
      let m1Hash' = Buffer.sub #uint8 #(v stLen) #(v hLen) st (sub #SIZE stLen hLen) hLen in

      let maskedDB = Buffer.sub #uint8 #(v emLen) #(v dbLen) em (size 0) dbLen in
      let m1Hash = Buffer.sub #uint8 #(v emLen) #(v hLen) em dbLen hLen in

      hash_sha256 mHash mmsgLen msg;

      mgf_sha256 #(v hLen) #(v dbLen) hLen m1Hash dbLen dbMask;
      xor_bytes dbLen dbMask maskedDB;
      (if (msBits >. size 0) then begin
        let shift_bits = sub #SIZE (size 8) msBits in
        dbMask.(size 0) <- dbMask.(size 0) &. (shift_right #U8 (u8 0xff) (size_to_uint32 shift_bits))
      end);

      pad2.(sub #SIZE padLen (size 1)) <- u8 0x01;
      let pad = Buffer.sub #uint8 #(v dbLen) #(v padLen) dbMask (size 0) padLen in
      let salt = Buffer.sub #uint8 #(v dbLen) #(v sLen) dbMask padLen sLen in

      let m1_hash = Buffer.sub #uint8 #(v m1Len) #(v hLen) m1 (size 8) hLen in
      copy hLen mHash m1_hash;
      let m1_salt = Buffer.sub #uint8 #(v m1Len) #(v sLen) m1 (add #SIZE (size 8) hLen) sLen in
      copy sLen salt m1_salt;
      hash_sha256 m1Hash' m1Len m1;

      if not (eq_b padLen pad pad2) then false
      else eq_b hLen m1Hash m1Hash'
    end
  )

val rsa_sign:
  #sLen:size_nat -> #msgLen:size_nat -> #nLen:size_nat ->
  pow2_i:size_t -> modBits:size_t{0 < v modBits /\ nLen = v (blocks modBits (size 64))} ->
  eBits:size_t{0 < v eBits /\ v eBits <= v modBits} -> dBits:size_t{0 < v dBits /\ v dBits <= v modBits} ->
  pLen:size_t -> qLen:size_t{nLen + v (blocks eBits (size 64)) + v (blocks dBits (size 64)) + v pLen + v qLen < max_size_t} ->
  skey:lbignum (nLen + v (blocks eBits (size 64)) + v (blocks dBits (size 64)) + v pLen + v qLen) -> rBlind:uint64 ->
  ssLen:size_t{v ssLen == sLen /\ sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - sLen - v hLen - 2 >= 0} -> salt:lbytes sLen ->
  mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen -> sgnt:lbytes (v (blocks modBits (size 8))) -> Stack unit
  (requires (fun h -> live h salt /\ live h msg /\ live h sgnt /\ live h skey /\
	            disjoint msg salt /\ disjoint msg sgnt /\ disjoint sgnt salt))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 sgnt h0 h1))

let rsa_sign #sLen #msgLen #nLen pow2_i modBits eBits dBits pLen qLen skey rBlind ssLen salt mmsgLen msg sgnt =
  let nLen = blocks modBits (size 64) in
  let eLen = blocks eBits (size 64) in
  let dLen = blocks dBits (size 64) in
  let skeyLen:size_t = add #SIZE (add #SIZE (add #SIZE (add #SIZE nLen eLen) dLen) pLen) qLen in

  let n = Buffer.sub #uint64 #(v skeyLen) #(v nLen) skey (size 0) nLen in
  let e = Buffer.sub #uint64 #(v skeyLen) #(v eLen) skey nLen eLen in
  let d = Buffer.sub #uint64 #(v skeyLen) #(v dLen) skey (add #SIZE nLen eLen) dLen in
  let p = Buffer.sub #uint64 #(v skeyLen) #(v pLen) skey (add #SIZE (add #SIZE nLen eLen) dLen) pLen in
  let q = Buffer.sub #uint64 #(v skeyLen) #(v qLen) skey (add #SIZE ((add #SIZE (add #SIZE nLen eLen) dLen)) pLen) qLen in

  let k = blocks modBits (size 8) in
  let emBits = sub #SIZE modBits (size 1) in
  let emLen = blocks emBits (size 8) in

  assume (2 * v nLen + 2 * (v pLen + v qLen) + 1 < max_size_t);
  let n2Len = add #SIZE nLen nLen in
  let pqLen = add #SIZE pLen qLen in
  let stLen:size_t = add #SIZE n2Len (add #SIZE (add #SIZE pqLen pqLen) (size 1)) in

  alloc #uint8 #unit #(v emLen) emLen (u8 0) [BufItem skey; BufItem msg; BufItem salt] [BufItem sgnt]
  (fun h0 _ h1 -> True)
  (fun em ->
    pss_encode #sLen #msgLen #(v emLen) ssLen salt mmsgLen msg emBits em;

    alloc #uint64 #unit #(v stLen) stLen (u64 0) [BufItem skey; BufItem em] [BufItem sgnt]
    (fun h0 _ h1 -> True)
    (fun tmp ->
      let m = Buffer.sub #uint64 #(v stLen) #(v nLen) tmp (size 0) nLen in
      let s = Buffer.sub #uint64 #(v stLen) #(v nLen) tmp nLen nLen in
      let phi_n = Buffer.sub #uint64 #(v stLen) #(v pqLen) tmp n2Len pqLen in
      let p1 = Buffer.sub #uint64 #(v stLen) #(v pLen) tmp (add #SIZE n2Len pqLen) pLen in
      let q1 = Buffer.sub #uint64 #(v stLen) #(v qLen) tmp (add #SIZE (add #SIZE n2Len pqLen) pLen) qLen in
      let dLen':size_t = add #SIZE (add #SIZE pLen qLen) (size 1) in
      let d' = Buffer.sub #uint64 #(v stLen) #(v dLen') tmp (add #SIZE n2Len pqLen) dLen' in

      text_to_nat emLen em m;
      bn_sub_u64 pLen p (u64 1) p1; // p1 = p - 1
      bn_sub_u64 qLen q (u64 1) q1; // q1 = q - 1
      bn_mul pLen p1 qLen q1 phi_n; // phi_n = p1 * q1
      bn_mul_u64 pqLen phi_n rBlind d'; //d' = phi_n * rBlind
      assume (v dLen <= v dLen' /\ v dLen' * 64 < max_size_t);
      bn_add dLen' d' dLen d d'; //d' = d' + d
      assume (v nLen = v (bits_to_bn modBits));
      mod_exp pow2_i modBits nLen n m (mul #SIZE dLen' (size 64)) d' s;
      nat_to_text k s sgnt
    )
  )

val rsa_verify:
  #msgLen:size_nat -> #nLen:size_nat ->
  pow2_i:size_t -> modBits:size_t{0 < v modBits /\ nLen = v (blocks modBits (size 64))} ->
  eBits:size_t{0 < v eBits /\ v eBits <= v modBits /\ nLen + v (blocks eBits (size 64)) < max_size_t} ->
  pkey:lbignum (nLen + v (blocks eBits (size 64))) ->
  sLen:size_t{v sLen + v hLen + 8 < max_size_t /\ v (blocks modBits (size 8)) - v sLen - v hLen - 2 >= 0} ->
  sgnt:lbytes (v (blocks modBits (size 8))) ->
  mmsgLen:size_t{v mmsgLen == msgLen} -> msg:lbytes msgLen -> Stack bool
  (requires (fun h -> live h msg /\ live h sgnt /\ live h pkey /\ disjoint msg sgnt))
  (ensures (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies0 h0 h1))
let rsa_verify #msgLen #nLen pow2_i modBits eBits pkey sLen sgnt mmsgLen msg =
  let nLen = blocks modBits (size 64) in
  let eLen = blocks eBits (size 64) in
  let pkeyLen:size_t = add #SIZE nLen eLen in

  let n = Buffer.sub #uint64 #(v pkeyLen) #(v nLen) pkey (size 0) nLen in
  let e = Buffer.sub #uint64 #(v pkeyLen) #(v eLen) pkey nLen eLen in

  let k = blocks modBits (size 8) in
  let emBits = sub #SIZE modBits (size 1) in
  let emLen = blocks emBits (size 8) in

  let n2Len:size_t = add #SIZE nLen nLen in

  alloc #uint64 #bool #(v n2Len) n2Len (u64 0) [BufItem pkey; BufItem msg; BufItem sgnt] []
  (fun h0 _ h1 -> True)
  (fun tmp ->
    alloc #uint8 #bool #(v k) k (u8 0) [BufItem pkey; BufItem msg; BufItem sgnt] [BufItem tmp]
    (fun h0 _ h1 -> True)
    (fun em ->
      let m = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp (size 0) nLen in
      let s = Buffer.sub #uint64 #(v n2Len) #(v nLen) tmp nLen nLen in
      text_to_nat k sgnt s;

      if (bn_is_less nLen s nLen n) then begin
        mod_exp pow2_i modBits nLen n s eBits e m;
        nat_to_text emLen m em;
        pss_verify #msgLen #(v emLen) sLen mmsgLen msg emBits em end
      else false
    )
  )
