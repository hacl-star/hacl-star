module Hacl.Bignum

friend Hacl.Spec.Bignum

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let bn_mask_lt len a b =
  push_frame ();
  let acc = create 1ul (u64 0) in

  [@inline_let]
  let refl h i : GTot uint64 = Lib.Sequence.index (as_seq h acc) 0 in
  [@inline_let]
  let footprint i = loc acc in
  [@inline_let]
  let spec h = S.bn_mask_lt_f (as_seq h a) (as_seq h b) in

  let h0 = ST.get () in
  loop h0 len (S.bn_mask_lt_t (v len)) refl footprint spec
  (fun i ->
    Loops.unfold_repeat_gen (v len) (S.bn_mask_lt_t (v len)) (spec h0) (refl h0 0) (v i);
    let beq = eq_mask a.(i) b.(i) in
    let blt = lt_mask a.(i) b.(i) in
    acc.(0ul) <-
      Hacl.Spec.Bignum.Definitions.mask_select beq acc.(0ul)
      (Hacl.Spec.Bignum.Definitions.mask_select blt (ones U64 SEC) (zeros U64 SEC))
  );
  let mask = acc.(0ul) in
  pop_frame ();
  mask

let bn_add_eq_len aLen a b res =
  Hacl.Bignum.Addition.bn_add_eq_len aLen a b res

let bn_sub_eq_len aLen a b res =
  Hacl.Bignum.Addition.bn_sub_eq_len aLen a b res

let bn_add aLen a bLen b res =
  Hacl.Bignum.Addition.bn_add aLen a bLen b res

let bn_sub aLen a bLen b res =
  Hacl.Bignum.Addition.bn_sub aLen a bLen b res

let bn_add_mod_n len n a b res =
  push_frame ();
  let tmp = create len (u64 0) in
  let c0 = bn_add_eq_len len a b res in
  let c1 = bn_sub_eq_len len res n tmp in
  let c = c0 -. c1 in
  map2T len res (Hacl.Spec.Bignum.Definitions.mask_select c) res tmp;
  pop_frame()

let bn_mul aLen a bLen b =
  Hacl.Bignum.Multiplication.bn_mul aLen a bLen b

let bn_mul1_lshift_add_in_place aLen a b j res =
  Hacl.Bignum.Multiplication.bn_mul1_lshift_add aLen a b j res

let bn_rshift len b i res =
  copy res (sub b i (len -! i))

let bn_sub_mask len n a =
  push_frame ();
  let mask = create 1ul (ones U64 SEC) in
  let mod_mask = create len (u64 0) in
  let mask = Lib.ByteBuffer.buf_eq_mask n a len mask in
  mapT len mod_mask (logand mask) n;
  let _ = Hacl.Bignum.Addition.bn_sub_eq_len len a mod_mask a in
  pop_frame ()

[@CInline]
let bn_is_less len a b =
  let mask = bn_mask_lt len a b in
  if UInt64.eq (Lib.RawIntTypes.u64_to_UInt64 mask) 0uL then false else true

let bn_is_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  let tmp = input.(i) in
  let tmp = (tmp >>. j) &. u64 1 in
  eq_u64 tmp (u64 1)

let bn_bit_set len input ind =
  let i = ind /. 64ul in
  let j = ind %. 64ul in
  input.(i) <- input.(i) |. (u64 1 <<. j)

let bn_from_bytes_be len b res =
  Hacl.Bignum.Convert.bn_from_bytes_be len b res

let bn_to_bytes_be len b res =
  Hacl.Bignum.Convert.bn_to_bytes_be len b res

let bn_from_bytes_le len b res =
  Hacl.Bignum.Convert.bn_from_bytes_le len b res

let bn_to_bytes_le len b res =
  Hacl.Bignum.Convert.bn_to_bytes_le len b res
