module Hacl.Impl.QTesla.Constants

open Lib.IntTypes
open Hacl.SHA3

//NS:
//size is in terms of uint, which is abstract
//normalize on constants is redundant
let shake128_rate = size (normalize_term 168)
let shake256_rate = size (normalize_term 136)

// Implementation of cSHAKE gets inlined for extraction. To make things easier to compare to the
// reference code, we enclose it in our own wrapper so it appears as a function call in callers.
let cshake128_qtesla input_len input cstm output_len output = cshake128_frodo input_len input cstm output_len output
let cshake256_qtesla input_len input cstm output_len output = cshake256_frodo input_len input cstm output_len output

