module Hacl.Bignum

friend Hacl.Spec.Bignum

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let bn_add aLen a bLen b res =
  Hacl.Bignum.Addition.bn_add aLen a bLen b res

let bn_sub aLen a bLen b res =
  Hacl.Bignum.Addition.bn_sub aLen a bLen b res

let bn_mul aLen a bLen b res =
  Hacl.Bignum.Multiplication.bn_mul aLen a bLen b res

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
  let _ = Hacl.Bignum.Addition.bn_sub len a len mod_mask a in
  pop_frame ()


val bn_is_less_:
    len:size_t
  -> a:lbignum len
  -> b:lbignum len
  -> i:size_t{v i <= v len} ->
  Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures  fun h0 _ h1 -> h0 == h1)

let rec bn_is_less_ len a b i =
  if i >. 0ul then
    let i = i -. 1ul in
    let t1 = a.(i) in
    let t2 = b.(i) in
    (if not (eq_u64 t1 t2) then
      if lt_u64 t1 t2 then true else false
    else bn_is_less_ len a b i)
  else false


[@CInline]
let bn_is_less len a b = admit();
  bn_is_less_ len a b len


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
