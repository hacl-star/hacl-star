module Spec.PBKDF2

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

///   https://tools.ietf.org/html/rfc2898
///   PBKDF2 (P, S, c, dkLen)
///
///   Options:        PRF        underlying pseudorandom function (hLen
///                              denotes the length in octets of the
///                              pseudorandom function output)
///
///   Input:          P          password, an octet string
///                   S          salt, an octet string
///                   c          iteration count, a positive integer
///                   dkLen      intended length in octets of the derived
///                              key, a positive integer, at most
///                              (2^32 - 1) * hLen
///
///   Output:         DK         derived key, a dkLen-octet string

(* Definition: Base types *)
type lbytes (s:size_t) = intseq U8 s
// TODO: get the correct size of size_t
let numbytes_size_t = 4

///  F is defined as the exclusive-or sum of the
///  first c iterates of the underlying pseudorandom function PRF
///  applied to the password P and the concatenation of the salt S
///  and the block index i:
///  F (P, S, c, i) = U_1 \xor U_2 \xor ... \xor U_c
///
///  where
///
///   U_1 = PRF (P, S || INT (i)) ,
///   U_2 = PRF (P, U_1) ,
///   ...
///   U_c = PRF (P, U_{c-1}) .
///
///  Here, INT (i) is a four-octet encoding of the integer i, most
///  significant octet first.
val f:
  prf:Hash.algorithm ->
  p_len:size_t{p_len < Hash.size_hash prf} ->
  pwd:lbytes p_len ->
  s_len:size_t{let x = s_len + numbytes_size_t + Hash.size_block prf in
    x <= max_size_t /\
    x < Hash.max_input prf} ->
  salt:lbytes s_len ->
  counter:size_t{1 <= counter} ->
  i:size_t
  -> Tot (lbytes (Hash.size_hash prf))
let f prf p_len pwd s_len salt counter i =
  let input = create (s_len + numbytes_size_t) (u8 0) in
  let s_i = update_sub input 0 s_len salt in
  let i_bytes = uint_to_bytes_be #U32 (u32 i) in
  let s_i = update_sub s_i s_len numbytes_size_t i_bytes in
  let u_1 = Spec.HMAC.hmac prf p_len pwd (s_len + numbytes_size_t) s_i in
  let u, _ = repeat_range 1 counter (fun i (u, u_p) ->
      let u_i = Spec.HMAC.hmac prf p_len pwd (Hash.size_hash prf) u_p in
      map2 (fun x y -> x ^. y) u u_i, u_i
    ) (u_1, u_1) in u

val pbkdf2:
  prf:Hash.algorithm ->
  p_len:size_t{p_len < Hash.size_hash prf} ->
  pwd:lbytes p_len ->
  s_len:size_t{let x = s_len + numbytes_size_t + Hash.size_block prf in
    x <= max_size_t /\
    x < Hash.max_input prf} ->
  salt:lbytes s_len ->
  counter:size_t{1 <= counter} ->
  dkLen:size_t{ let hLen =  (Hash.size_hash prf) in
                let l =  dkLen / hLen + 1 in
                dkLen <= (pow2 32 - 1) * hLen /\
                (l + 1) * hLen <= max_size_t}
  -> Tot (lbytes dkLen)
let pbkdf2 prf p_len pwd s_len salt counter dkLen =
/// 1. If dkLen > (2^32 - 1) * hLen, output "derived key too long" and
///  stop.
/// -> precondition

/// 2. Let l be the number of hLen-octet blocks in the derived key,
///  rounding up, and let r be the number of octets in the last
///  block:
///
///            l = CEIL (dkLen / hLen) ,
///            r = dkLen - (l - 1) * hLen .
  let hLen = (Hash.size_hash prf) in
  let l = dkLen / hLen + 1 in
  let r = dkLen - (l - 1) * hLen in

///  Here, CEIL (x) is the "ceiling" function, i.e. the smallest
///  integer greater than, or equal to, x.
///
/// 3. For each block of the derived key apply the function F defined
///  below to the password P, the salt S, the iteration count c, and
///  the block index to compute the block:
///
///            T_1 = F (P, S, c, 1) ,
///            T_2 = F (P, S, c, 2) ,
///            ...
///            T_l = F (P, S, c, l) ,
///
///  where the function F is defined above.
  let dk_x_size: size_t = l * hLen in
  let dk_0 = create (l * hLen) (u8 0) in
  let dk_t = repeat_range 0 l (fun i dk_x ->
      let dk_i = f prf p_len pwd s_len salt counter (i + 1) in
      update_sub #uint8 #dk_x_size dk_x (i * hLen) hLen dk_i
    ) dk_0 in

///  4. Concatenate the blocks and extract the first dkLen octets to
///  produce a derived key DK:
///
///   DK = T_1 || T_2 ||  ...  || T_l<0..r-1>
///
///  5. Output the derived key DK.
  sub dk_t 0 dkLen
