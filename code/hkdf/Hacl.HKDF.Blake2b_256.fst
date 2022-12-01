module Hacl.HKDF.Blake2b_256

open Spec.Hash.Definitions
open Hacl.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
let expand_blake2b_256: expand_st Blake2B =
  mk_expand Blake2B Hacl.HMAC.Blake2b_256.compute_blake2b_256

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
let extract_blake2b_256: extract_st Blake2B =
  mk_extract Blake2B Hacl.HMAC.Blake2b_256.compute_blake2b_256
