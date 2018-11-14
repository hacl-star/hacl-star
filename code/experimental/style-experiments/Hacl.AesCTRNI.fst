module Hacl.AesCTRNI

let aes128_ctr_encrypt out inp in_len k n c = 
  Hacl.Impl.Aes.NI.aes128_ctr_encrypt out inp in_len k n c

let aes128_ctr_decrypt out inp in_len k n c = 
  Hacl.Impl.Aes.NI.aes128_ctr_decrypt out inp in_len k n c

