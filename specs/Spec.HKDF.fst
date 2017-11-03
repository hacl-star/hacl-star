module Spec.HKDF

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

open Spec.SHA2
open Spec.HMAC

#set-options "--z3rlimit 25"

module Hash = Spec.SHA2
module HMAC = Spec.HMAC


/// HKDF-Extract(salt, IKM) -> PRK
///
/// Options:
///    Hash     a hash function; HashLen denotes the length of the
///             hash function output in octets
///
/// Inputs:
///    salt     optional salt value (a non-secret random value);
///             if not provided, it is set to a string of HashLen zeros.
///    IKM      input keying material
///
/// Output:
///    PRK      a pseudorandom key (of HashLen octets)
///
/// The output PRK is calculated as follows:
///
/// PRK = HMAC-Hash(salt, IKM)

let hkdf_extract_core
  (p:Hash.parameters)
  (salt:lbytes (Hash.size_block p))
  (len_ikm:size_t{Hash.size_block p + len_ikm < max_size_t /\ Hash.size_block p + len_ikm < Hash.maxInput p})
  (ikm:lbytes len_ikm) =
  HMAC.hmac_core p salt len_ikm ikm

let hkdf_extract
  (p:Hash.parameters)
  (len_salt:size_t)
  (salt:lbytes len_salt)
  (len_ikm:size_t{Hash.size_block p + len_ikm < max_size_t /\ Hash.size_block p + len_ikm < Hash.maxInput p})
  (ikm:lbytes len_ikm) =
  if len_salt = 0 then
    let salt = create (p.size_hash) (u8 0) in
    HMAC.hmac p p.size_hash salt len_ikm ikm
  else
    HMAC.hmac p len_salt salt len_ikm ikm

/// HKDF-Expand(PRK, info, L) -> OKM
///
///    Options:
///       Hash     a hash function; HashLen denotes the length of the
///                hash function output in octets
///
///    Inputs:
///       PRK      a pseudorandom key of at least HashLen octets
///                (usually, the output from the extract step)
///       info     optional context and application specific information
///                (can be a zero-length string)
///       L        length of output keying material in octets
///                (<= 255*HashLen)
///
///    Output:
///       OKM      output keying material (of L octets)
///
///    The output OKM is calculated as follows:
///
///    N = ceil(L/HashLen)
///    T = T(1) | T(2) | T(3) | ... | T(N)
///    OKM = first L octets of T
///
///    where:
///    T(0) = empty string (zero length)
///    T(1) = HMAC-Hash(PRK, T(0) | info | 0x01)
///    T(2) = HMAC-Hash(PRK, T(1) | info | 0x02)
///    T(3) = HMAC-Hash(PRK, T(2) | info | 0x03)
///    ...


let hkdf_expand (p:Hash.parameters) (len_prk:size_t) (prk:lbytes len_prk) (len_info:size_t) (info:lbytes len_info) (len:size_t) =
  // Compute the number of blocks required for the final output
  assume(p.size_hash <> 0);
  let n = len / p.size_hash + 1 in
  // Create the final output space
  let _T = create (n * p.size_hash) (u8 0) in
  // Create the intermediate _Ti space
  let tic = create (p.size_hash + len_info + 1) (u8 0) in
  let tic = update_slice tic p.size_hash (p.size_hash + len_info) info in
  // Repeat the computation and store into the final T
  let _T = repeati n (fun i t ->
    let min = i * p.size_hash in
    let max = (i + 1) * p.size_hash in
    let _Ti =
      if i = 0 then begin
        let tic0 = slice tic p.size_hash (p.size_hash + len_info + 1) in
        HMAC.hmac p len_prk prk (len_info + 1) tic0 end
      else begin
        let _Ti_prev = slice _T min max in
        let tic = update_slice tic 0 p.size_hash _Ti_prev in
        let tic = tic.[p.size_hash + len_info] <- u8 i in
        HMAC.hmac p len_prk prk (p.size_hash + len_info + 1) tic end in
    update_slice _T min max _Ti) _T in
  slice _T 0 len
