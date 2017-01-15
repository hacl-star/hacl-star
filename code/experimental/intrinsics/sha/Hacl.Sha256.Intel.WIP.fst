module Hacl.Sha256.Intel


(* Types definitions *)
new type u8  = Hacl.UInt8.t
new type u64 = Hacl.UInt64.t
new type __m128i = Hacl.UInt128.t


(* Conversion functions *)
assume val __m128i_of_bytes: __m128i -> bytes -> nat -> STL unit (requires True) (ensures True)


(* Intrinsic operations *)
assume val _mm_loadu_si128: __m128i -> STL __m128i (requires True) (ensures True)
assume val _mm_shuffle_epi8: __m128i -> ??? -> STL ??? (requires True) (ensures True)
assume val _mm_shuffle_epi32: __m128i -> u8 -> STL __m128i (requires True) (ensures True)
assume val _mm_alignr_epi8: __m128i -> __m128i -> u8 -> STL __m128i (requires True) (ensures True)
assume val _mm_blend_epi16: __m128i -> __m128i -> u8 -> STL __m128i (requires True) (ensures True)
assume val _mm_set_epi64x: u64 -> u64 -> STL __m128i (requires True) (ensures True)
assume val _mm_add_epi32: __m128i -> __m128i -> STL ??? (requires True) (ensures True)

(* Intrinsics dedicated to SHA256 *)
assume val _mm_sha256rnds2_epu32: __m128i -> __m128i -> __m128i -> STL __m128i (requires True) (ensures True)



(* Call to the inner compression function using dedicated instructions *)
let rec sha256_update_loop state digest data rounds_data =

  (* Process all blocks *)
  if U32.gt rounds_data 0ul then

    (* Keep track of the initial state *)
    let abef_save = state0 in
    let cdgh_save = state1 in

    // Rounds 0-3
    let data0   = SB.sub data 0ul 16ul in
    let msg     = _mm_loadu_si128 data0 in
    let msgtmp0 = _mm_shuffle_epi8 msg shuf_mask in
        let msg    = _mm_add_epi32 msgtmp0 (_mm_set_epi64x 0xE9B5DBA5B5C0FBCFuL 0x71374491428A2F98uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
        let msg    = _mm_shuffle_epi32 msg 0x0Euy in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in

    // Rounds 4-7
    let data16 = SB.sub data 16ul 16ul in
    let msgtmp1 = _mm_loadu_si128 data16 in
    let msgtmp1 = _mm_shuffle_epi8 msgtmp1 shuf_mask in
        let msg    = _mm_add_epi32 msgtmp1 (_mm_set_epi64x 0xAB1C5ED5923F82A4uL 0x59F111F13956C25BuL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp0 = _mm_sha256msg1_epu32 msgtmp0 msgtmp1 in

    // Rounds 8-11
    let data32 = SB.sub data 32ul 16ul in
    let msgtmp2 = _mm_loadu_si128 data32 in
    let msgtmp2 = _mm_shuffle_epi8 msgtmp2 shuf_mask in
        let msg    = _mm_add_epi32 msgtmp2 (_mm_set_epi64x 0x550C7DC3243185BEuL 0x12835B01D807AA98uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
        let msg    = _mm_shuffle_epi32 msg 0x0Euy in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp1 = _mm_sha256msg1_epu32 msgtmp1 msgtmp2 in

    // Rounds 12-15
    let data48 = SB.sub data 48ul 16ul in
    let msgtmp3 = _mm_loadu_si128 data48 in
    let msgtmp3 = _mm_shuffle_epi8 msgtmp3 shuf_mask in
        let msg    = _mm_add_epi32 msgtmp3 (_mm_set_epi64x 0xC19BF1749BDC06A7uL 0x80DEB1FE72BE5D74uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp3 msgtmp2 4 in
    let msgtmp0 = _mm_add_epi32 msgtmp0 tmp in
    let msgtmp0 = _mm_sha256msg2_epu32 msgtmp0 msgtmp3 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp2 = _mm_sha256msg1_epu32 msgtmp2 msgtmp3 in

    // Rounds 16-19
    let msg    = _mm_add_epi32 msgtmp0 (_mm_set_epi64x 0x240CA1CC0FC19DC6uL 0xEFBE4786E49B69C1uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp0 msgtmp3 4 in
    let msgtmp1 = _mm_add_epi32 msgtmp1 tmp in
    let msgtmp1 = _mm_sha256msg2_epu32 msgtmp1 msgtmp0 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp3 = _mm_sha256msg1_epu32 msgtmp3 msgtmp0 in

    // Rounds 20-23
        let msg    = _mm_add_epi32 msgtmp1 (_mm_set_epi64x 0x76F988DA5CB0A9DCuL 0x4A7484AA2DE92C6FuL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp1 msgtmp0 4 in
    let msgtmp2 = _mm_add_epi32 msgtmp2 tmp in
    let msgtmp2 = _mm_sha256msg2_epu32 msgtmp2 msgtmp1 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp0 = _mm_sha256msg1_epu32 msgtmp0 msgtmp1 in

    // Rounds 24-27
        let msg    = _mm_add_epi32 msgtmp2 (_mm_set_epi64x 0xBF597FC7B00327C8uL 0xA831C66D983E5152uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp2 msgtmp1 4 in
    let msgtmp3 = _mm_add_epi32 msgtmp3 tmp in
    let msgtmp3 = _mm_sha256msg2_epu32 msgtmp3 msgtmp2 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp1 = _mm_sha256msg1_epu32 msgtmp1 msgtmp2 in

    // Rounds 28-31
        let msg    = _mm_add_epi32 msgtmp3 (_mm_set_epi64x 0x1429296706CA6351uL 0xD5A79147C6E00BF3uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp3 msgtmp2 4 in
    let msgtmp0 = _mm_add_epi32 msgtmp0 tmp in
    let msgtmp0 = _mm_sha256msg2_epu32 msgtmp0 msgtmp3 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp2 = _mm_sha256msg1_epu32 msgtmp2 msgtmp3 in

    // Rounds 32-35
        let msg    = _mm_add_epi32 msgtmp0 (_mm_set_epi64x 0x53380D134D2C6DFCuL 0x2E1B213827B70A85uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp0 msgtmp3 4 in
    let msgtmp1 = _mm_add_epi32 msgtmp1 tmp in
    let msgtmp1 = _mm_sha256msg2_epu32 msgtmp1 msgtmp0 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp3 = _mm_sha256msg1_epu32 msgtmp3 msgtmp0 in

    // Rounds 36-39
        let msg    = _mm_add_epi32 msgtmp1 (_mm_set_epi64x 0x92722C8581C2C92EuL 0x766A0ABB650A7354uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp1 msgtmp0 4 in
    let msgtmp2 = _mm_add_epi32 msgtmp2 tmp in
    let msgtmp2 = _mm_sha256msg2_epu32 msgtmp2 msgtmp1 in
        let  msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp0 = _mm_sha256msg1_epu32 msgtmp0 msgtmp1 in

    // Rounds 40-43
        let msg    = _mm_add_epi32 msgtmp2 (_mm_set_epi64x 0xC76C51A3C24B8B70uL 0xA81A664BA2BFE8A1uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp2 msgtmp1 4 in
    let msgtmp3 = _mm_add_epi32 msgtmp3 tmp in
    let msgtmp3 = _mm_sha256msg2_epu32 msgtmp3 msgtmp2 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp1 = _mm_sha256msg1_epu32 msgtmp1 msgtmp2 in

    // Rounds 44-47
        let msg    = _mm_add_epi32 msgtmp3 (_mm_set_epi64x 0x106AA070F40E3585uL 0xD6990624D192E819uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp3 msgtmp2 4 in
    let msgtmp0 = _mm_add_epi32 msgtmp0 tmp in
    let msgtmp0 = _mm_sha256msg2_epu32 msgtmp0 msgtmp3 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp2 = _mm_sha256msg1_epu32 msgtmp2 msgtmp3 in

    // Rounds 48-51
        let msg    = _mm_add_epi32 msgtmp0 (_mm_set_epi64x 0x34B0BCB52748774CuL 0x1E376C0819A4C116uL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp0 msgtmp3 4 in
    let msgtmp1 = _mm_add_epi32 msgtmp1 tmp in
    let msgtmp1 = _mm_sha256msg2_epu32 msgtmp1 msgtmp0 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in
    let msgtmp3 = _mm_sha256msg1_epu32 msgtmp3 msgtmp0 in

    // Rounds 52-55
        let msg    = _mm_add_epi32 msgtmp1
                  _mm_set_epi64x 0x682E6FF35B9CCA4FuL 0x4ED8AA4A391C0CB3uL  in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp1 msgtmp0 4 in
    let msgtmp2 = _mm_add_epi32 msgtmp2 tmp in
    let msgtmp2 = _mm_sha256msg2_epu32 msgtmp2 msgtmp1 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in

    // Rounds 56-59
        let msg    = _mm_add_epi32 msgtmp2
                  _mm_set_epi64x 0x8CC7020884C87814uL 0x78A5636F748F82EEuL  in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
    let tmp     = _mm_alignr_epi8 msgtmp2 msgtmp1 4 in
    let msgtmp3 = _mm_add_epi32 msgtmp3 tmp in
    let msgtmp3 = _mm_sha256msg2_epu32 msgtmp3 msgtmp2 in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in

    // Rounds 60-63
        let msg    = _mm_add_epi32 msgtmp3 (_mm_set_epi64x 0xC67178F2BEF9A3F7uL 0xA4506CEB90BEFFFAuL) in
        let state1 = _mm_sha256rnds2_epu32 state1 state0 msg in
        let msg    = _mm_shuffle_epi32 msg 0x0E in
        let state0 = _mm_sha256rnds2_epu32 state0 state1 msg in

    (* Add current hash values to initial values *)
    let state0 = _mm_add_epi32 state0 abef_save in
    let state1 = _mm_add_epi32 state1 cdgh_save in

    (* Store the new state *)
    // BB. TODO

    (* Recursive call *)
    sha256_update_loop state digest data (rounds_data @- 1ul)
  else ()


let sha256_update digest data rounds_data =

  (* Create the state *)
  // BB. TODO

  // Load initial hash values
  // Need to reorder these appropriately
  // DCBA, HGFE -> ABEF, CDGH
  let d0 = sub digest 0ul 4ul in
  let d1 = sub digest 4ul 4ul in

  let tmp    = _mm_loadu_si128 d0 in
  let state1 = _mm_loadu_si128 d1 in
  let tmp    = _mm_shuffle_epi32 tmp 0xB1uy in // CDAB
  let state1 = _mm_shuffle_epi32 state1 0x1Buy in // EFGH
  let state0 = _mm_alignr_epi8 tmp state1 8ul in // ABEF    // BB. 8 ???
  let state1 = _mm_blend_epi16 state1 tmp 0xF0uy in // CDGH

  let shuf_mask = _mm_set_epi64x 0x0c0d0e0f08090a0buL 0x0405060700010203uL in

  (* Call the underlying compression function *)
  sha256_update_loop state digest data rounds_data;

  (* Write hash values back in the correct order *)
  let tmp    = _mm_shuffle_epi32 state0 0x1Buy in   // FEBA
  let state1 = _mm_shuffle_epi32 state1 0xB1uy in   // DCHG
  let state0 = _mm_blend_epi16 tmp state1 0xF0uy in // DCBA
  let state1 = _mm_alignr_epi8 state1 tmp 8ul in    // ABEF // BB. 8 ???

  (* Store the final hash *)
  // BB. TODO
  //_mm_store_si128((__m128i*) digest, state0);
  //_mm_store_si128((__m128i*) (digest+4), state1);
