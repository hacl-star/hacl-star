module Spec.Cryptoverif

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


assume val probability: Type0
assume val bitstringbot: Type0

(******************************** Key generation ************************************************)

(* The symmetric primitives no longer include a key generation function.
   If you want to add one, you can use the following macro

   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   key: type of keys, must be "bounded"

   kgen: key generation function

   The types keyseed and key must be declared before this macro is
   expanded. The function kgen is declared by this macro. It must
   not be declared elsewhere, and it can be used only after
   expanding the macro.  *)

assume val keygen__keyseed: Type0
assume val keygen__key: Type0
assume val keygen: keygen__keyseed -> Tot keygen__key


(***************************** Symmetric encryption *********************************************)

(* IND-CPA probabilistic symmetric encryption
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   enc_r': symbol that replaces enc_r after game transformation
   dec: decryption function
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, l): probability of breaking the IND-CPA property in time
   t for one key and N encryption queries with cleartexts of length at
   most l

   The types key, cleartext, ciphertext, enc_seed and the
   probability Penc must be declared before this macro is
   expanded. The functions enc, enc_r, enc_r', dec, injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

assume val ind_cpa_sym_enc__key: Type0
assume val ind_cpa_sym_enc__cleartext: Type0
assume val ind_cpa_sym_enc__ciphertext: Type0

[@"bounded"]
assume val ind_cpa_sym_enc__enc_seed: Type0


assume val ind_cpa_sym_enc__enc_r: ind_cpa_sym_enc__cleartext -> ind_cpa_sym_enc__key -> ind_cpa_sym_enc__enc_seed -> Tot ind_cpa_sym_enc__ciphertext

assume val ind_cpa_sym_enc__dec: ind_cpa_sym_enc__ciphertext -> ind_cpa_sym_enc__key -> Tot bitstringbot

assume val ind_cpa_sym_enc__enc_r': ind_cpa_sym_enc__cleartext -> ind_cpa_sym_enc__key -> ind_cpa_sym_enc__enc_seed -> Tot ind_cpa_sym_enc__ciphertext

[@"data"]
assume val ind_cpa_sym_enc__injbot: ind_cpa_sym_enc__cleartext -> Tot bitstringbot

assume val ind_cpa_sym_enc__enc: ind_cpa_sym_enc__cleartext -> ind_cpa_sym_enc__key -> Tot ind_cpa_sym_enc__ciphertext

assume val ind_cpa_sym_enc__Z: ind_cpa_sym_enc__cleartext -> Tot ind_cpa_sym_enc__cleartext

assume val ind_cpa_sym_enc__Penc: probability


(* IND-CPA and INT-CTXT probabilistic symmetric encryption
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   enc_r': symbol that replaces enc_r after game transformation
   dec: decryption function
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, l): probability of breaking the IND-CPA property in time
   t for one key and N encryption queries with cleartexts of length at
   most l
   Pencctxt(t, N, N', l, l'): probability of breaking the INT-CTXT property
   in time t for one key, N encryption queries, N' decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l'.

   The types key, cleartext, ciphertext, enc_seed and the
   probabilities Penc, Pencctxt must be declared before this macro is
   expanded. The functions enc, enc_r, enc_r', dec, injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

assume val ind_cpa_int_ctxt_sym_enc__key: Type0
assume val ind_cpa_int_ctxt_sym_enc__cleartext: Type0
assume val ind_cpa_int_ctxt_sym_enc__ciphertext: Type0

[@"bounded"]
assume val ind_cpa_int_ctxt_sym_enc__enc_seed: Type0

assume val ind_cpa_int_ctxt_sym_enc__Penc: probability
assume val ind_cpa_int_ctxt_sym_enc__Pencctxt: probability

assume val ind_cpa_int_ctxt_sym_enc__enc_r: ind_cpa_int_ctxt_sym_enc__cleartext -> ind_cpa_int_ctxt_sym_enc__key -> ind_cpa_int_ctxt_sym_enc__enc_seed -> Tot ind_cpa_int_ctxt_sym_enc__ciphertext

assume val ind_cpa_int_ctxt_sym_enc__dec: ind_cpa_int_ctxt_sym_enc__ciphertext -> ind_cpa_int_ctxt_sym_enc__key -> Tot bitstringbot

assume val ind_cpa_int_ctxt_sym_enc__enc_r': ind_cpa_int_ctxt_sym_enc__cleartext -> ind_cpa_int_ctxt_sym_enc__key -> ind_cpa_int_ctxt_sym_enc__enc_seed -> Tot ind_cpa_int_ctxt_sym_enc__ciphertext

[@"data"]
assume val ind_cpa_int_ctxt_sym_enc__injbot: ind_cpa_int_ctxt_sym_enc__cleartext -> Tot bitstringbot

assume val ind_cpa_int_ctxt_sym_enc__Z: ind_cpa_int_ctxt_sym_enc__cleartext -> Tot ind_cpa_int_ctxt_sym_enc__cleartext

assume val ind_cpa_int_ctxt_sym_enc__enc: ind_cpa_int_ctxt_sym_enc__cleartext -> ind_cpa_int_ctxt_sym_enc__key -> Tot ind_cpa_int_ctxt_sym_enc__ciphertext


(* AEAD (authenticated encryption with additional data)
   This is similar to IND-CPA and INT-CTXT authenticated encryption,
   except that some additional data is just authenticated.

   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   add_data: type of additional data that is just authenticated
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   enc_r': symbol that replaces enc_r after game transformation
   dec: decryption function
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, l): probability of breaking the IND-CPA property in time
   t for one key and N encryption queries with cleartexts of length at
   most l
   Pencctxt(t, N, N', l, l', ld, ld'): probability of breaking the INT-CTXT property
   in time t for one key, N encryption queries, N' decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l',
   additional data for encryption of length at most ld, and
   additional data for decryption of length at most ld'.

   The types key, cleartext, ciphertext, add_data, enc_seed and the
   probabilities Penc, Pencctxt must be declared before this macro is
   expanded. The functions enc, enc_r, enc_r', dec, injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

assume val aead__key: Type0
assume val aead__cleartext: Type0
assume val aead__ciphertext: Type0
assume val aead__add_data: Type0

[@"bounded"]
assume val aead__enc_seed: Type0


assume val aead__Penc: probability
assume val aead__Pencctxt: probability


assume val aead__enc_r: aead__cleartext -> aead__add_data -> aead__key -> aead__enc_seed -> Tot aead__ciphertext

assume val aead__dec: aead__ciphertext -> aead__add_data -> aead__key -> Tot bitstringbot

assume val aead__enc_r': aead__cleartext -> aead__add_data -> aead__key -> aead__enc_seed -> Tot aead__ciphertext

[@"data"]
assume val aead__injbot: aead__cleartext -> Tot bitstringbot

assume val aead__Z: aead__cleartext -> Tot aead__cleartext

assume val aead__enc: aead__cleartext -> aead__add_data -> aead__key -> Tot aead__ciphertext


(* AEAD (authenticated encryption with additional data) with a nonce.
   This is similar to the AEAD macro, but it uses a nonce
   (which must have a different value in each call to encryption)
   instead of random coins generated by encryption.
   A typical example is AES-GCM.

   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   add_data: type of additional data that is just authenticated
   nonce: type of the nonce

   enc: encryption function
   enc': symbol that replaces enc after game transformation
   dec: decryption function
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, l): probability of breaking the IND-CPA property in time
   t for one key and N encryption queries with cleartexts of length at
   most l
   Pencctxt(t, N, N', l, l', ld, ld'): probability of breaking the INT-CTXT property
   in time t for one key, N encryption queries, N' decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l',
   additional data for encryption of length at most ld, and
   additional data for decryption of length at most ld'.

   The types key, cleartext, ciphertext, add_data, nonce and the
   probabilities Penc, Pencctxt must be declared before this macro is
   expanded. The functions enc, enc', dec, injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

type aead_nonce__key (#a:Spec.AEAD.algorithm) = Spec.AEAD.key a
type aead_nonce__cleartext = bytes
type aead_nonce__ciphertext = bytes
type aead_nonce__add_data = bytes
type aead_nonce__nonce (#a:Spec.AEAD.algorithm) = Spec.AEAD.nonce a
type aead_nonce__bitstringbot (#a:Spec.AEAD.algorithm) (#clen: size_nat{Spec.AEAD.size_tag a <= clen}) = (option (lbytes (clen - Spec.AEAD.size_tag a)))

assume val aead_nonce__Penc: probability
assume val aead_nonce__Pencctxt: probability


val aead_nonce__enc:
    #a:Spec.AEAD.algorithm
  -> plaintext: aead_nonce__cleartext{length plaintext <= max_size_t
           /\ length plaintext + Spec.AEAD.size_block a <= max_size_t
           /\ length plaintext + Spec.AEAD.padlen a (length plaintext) <= max_size_t}
  -> aad: aead_nonce__add_data{length aad <= max_size_t /\ length aad + Spec.AEAD.padlen a (length aad) <= max_size_t}
  -> key: aead_nonce__key #a
  -> nonce: aead_nonce__nonce #a ->
  Tot aead_nonce__ciphertext

let aead_nonce__enc #a plaintext aad key nonce =
  Spec.AEAD.aead_encrypt a key nonce plaintext aad


val aead_nonce__dec:
    #a:Spec.AEAD.algorithm
  -> ciphertext: aead_nonce__ciphertext{Spec.AEAD.size_tag a <= length ciphertext /\ length ciphertext <= max_size_t}
  -> aad: aead_nonce__add_data{length aad <= max_size_t
             /\ (length ciphertext + length aad) / 64 <= max_size_t
             /\ length aad + Spec.AEAD.padlen a (length aad) <= max_size_t}
  -> nonce: aead_nonce__nonce #a
  -> key: aead_nonce__key #a ->

  Tot (aead_nonce__bitstringbot #a #(length ciphertext))

let aead_nonce__dec #a ciphertext aad nonce key =
  Spec.AEAD.aead_decrypt a key nonce ciphertext aad

val aead_nonce__enc':
    #a:Spec.AEAD.algorithm
  -> plaintext: aead_nonce__cleartext{length plaintext <= max_size_t
           /\ length plaintext + Spec.AEAD.size_block a <= max_size_t
           /\ length plaintext + Spec.AEAD.padlen a (length plaintext) <= max_size_t}
  -> aad: aead_nonce__add_data{length aad <= max_size_t /\ length aad + Spec.AEAD.padlen a (length aad) <= max_size_t}
  -> key: aead_nonce__key #a
  -> nonce: aead_nonce__nonce #a ->
  Tot aead_nonce__ciphertext

let aead_nonce__enc' #a plaintext aad key nonce = aead_nonce__enc #a plaintext aad key nonce

[@"data"]
assume val aead_nonce__injbot: aead_nonce__cleartext -> Tot bitstringbot

assume val aead_nonce__Z: aead_nonce__cleartext -> Tot aead_nonce__cleartext


(* IND-CCA2 probabilistic symmetric encryption
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   dec: decryption function
   enc_r', dec': symbols that replace enc_r and dec respectively after game transformation
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, Nu, N', l, l'): probability of breaking the IND-CCA2 property
   in time t for one key, N modified encryption queries,
   N unchanged encryption queries, and N' decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l'.

   The types key, cleartext, ciphertext, enc_seed and the
   probability Penc must be declared before this macro is
   expanded. The functions enc, enc_r, enc_r', dec, dec', injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

assume val ind_cca2_sym_enc__key: Type0
assume val ind_cca2_sym_enc__cleartext: Type0
assume val ind_cca2_sym_enc__ciphertext: Type0
assume val ind_cca2_sym_enc__enc_seed: Type0

assume val ind_cca2_sym_enc__enc_r: ind_cca2_sym_enc__cleartext -> ind_cca2_sym_enc__key -> ind_cca2_sym_enc__enc_seed -> Tot ind_cca2_sym_enc__ciphertext

assume val ind_cca2_sym_enc__dec: ind_cca2_sym_enc__ciphertext -> ind_cca2_sym_enc__key -> Tot bitstringbot

assume val ind_cca2_sym_enc__enc_r': ind_cca2_sym_enc__cleartext -> ind_cca2_sym_enc__key -> ind_cca2_sym_enc__enc_seed -> Tot ind_cca2_sym_enc__ciphertext

assume val ind_cca2_sym_enc__dec': ind_cca2_sym_enc__ciphertext -> ind_cca2_sym_enc__key -> Tot bitstringbot

assume val ind_cca2_sym_enc__injbot: ind_cca2_sym_enc__cleartext -> Tot bitstringbot

assume val ind_cca2_sym_enc__Z: ind_cca2_sym_enc__cleartext -> Tot ind_cca2_sym_enc__cleartext

assume val ind_cca2_sym_enc__enc: ind_cca2_sym_enc__cleartext -> ind_cca2_sym_enc__key -> Tot ind_cca2_sym_enc__ciphertext


(* INT-PTXT probabilistic symmetric encryption
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   dec: decryption function
   dec': symbol that replaces dec after game transformation
   injbot: natural injection from cleartext to bitstringbot

   Pencptxt(t, N, N', Nu', l, l'): probability of breaking the INT-PTXT property
   in time t for one key, N encryption queries, N' modified decryption queries,
   Nu' unchanged decryption queries, with
   cleartexts of length at most l and ciphertexts of length at most l'.

   The types key, cleartext, ciphertext, enc_seed and the
   probability Pencptxt must be declared before this macro is
   expanded. The functions enc, enc_r, dec, dec', and injbot are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.
*)

assume val int_ptxt_sym_enc__key: Type0
assume val int_ptxt_sym_enc__cleartext: Type0
assume val int_ptxt_sym_enc__ciphertext: Type0
assume val int_ptxt_sym_enc__enc_seed: Type0

assume val int_ptxt_sym_enc__enc_r: int_ptxt_sym_enc__cleartext -> int_ptxt_sym_enc__key -> int_ptxt_sym_enc__enc_seed -> Tot int_ptxt_sym_enc__ciphertext

assume val int_ptxt_sym_enc__dec: int_ptxt_sym_enc__ciphertext -> int_ptxt_sym_enc__key -> Tot bitstringbot

assume val int_ptxt_sym_enc__dec': int_ptxt_sym_enc__ciphertext -> int_ptxt_sym_enc__key -> Tot bitstringbot

assume val int_ptxt_sym_enc__injbot: int_ptxt_sym_enc__cleartext -> Tot bitstringbot

assume val int_ptxt_sym_enc__enc: int_ptxt_sym_enc__cleartext -> int_ptxt_sym_enc__key -> Tot int_ptxt_sym_enc__ciphertext


(* IND-CCA2 and INT-PTXT probabilistic symmetric encryption
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   dec: decryption function
   enc_r', dec': symbols that replace enc_r and dec respectively after game transformation
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N, Nu, N', l, l'): probability of breaking the IND-CCA2 property
   in time t for one key, N modified encryption queries, Nu unchanged
   encryption queries, and N' decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l'.
   Pencptxt(t, N, N', Nu', l, l'): probability of breaking the INT-PTXT property
   in time t for one key, N encryption queries, N' modified decryption queries,
   and Nu' unchanged decryption queries with
   cleartexts of length at most l and ciphertexts of length at most l'.

   The types key, cleartext, ciphertext, enc_seed and the
   probabilities Penc, Pencctxt must be declared before this macro is
   expanded. The functions enc, enc_r, enc_r', dec, dec', injbot, and Z are declared
   by this macro. They must not be declared elsewhere, and they can be
   used only after expanding the macro.

   CryptoVerif often needs manual guidance with this property,
   because it does not know which property (IND-CCA2 or INT-PTXT)
   to apply first. Moreover, when empty plaintexts are not allowed,
   IND-CCA2 and INT-PTXT is equivalent to IND-CPA and INT-CTXT,
   which is much easier to use for CryptoVerif, so we recommend
   using the latter property when possible.
*)

assume val ind_cca2_int_ptxt_sym_enc__key: Type0
assume val ind_cca2_int_ptxt_sym_enc__cleartext: Type0
assume val ind_cca2_int_ptxt_sym_enc__ciphertext: Type0
assume val ind_cca2_int_ptxt_sym_enc__enc_seed: Type0

assume val ind_cca2_int_ptxt_sym_enc__Penc: probability
assume val ind_cca2_int_ptxt_sym_enc__Pencptxt: probability

assume val ind_cca2_int_ptxt_sym_enc__enc_r: ind_cca2_int_ptxt_sym_enc__cleartext -> ind_cca2_int_ptxt_sym_enc__key -> ind_cca2_int_ptxt_sym_enc__enc_seed -> Tot ind_cca2_int_ptxt_sym_enc__ciphertext

assume val ind_cca2_int_ptxt_sym_enc__dec: ind_cca2_int_ptxt_sym_enc__ciphertext -> ind_cca2_int_ptxt_sym_enc__key -> Tot bitstringbot

assume val ind_cca2_int_ptxt_sym_enc__enc_r': ind_cca2_int_ptxt_sym_enc__cleartext -> ind_cca2_int_ptxt_sym_enc__key -> ind_cca2_int_ptxt_sym_enc__enc_seed -> Tot ind_cca2_int_ptxt_sym_enc__ciphertext

assume val ind_cca2_int_ptxt_sym_enc__dec': ind_cca2_int_ptxt_sym_enc__ciphertext -> ind_cca2_int_ptxt_sym_enc__key -> Tot bitstringbot

assume val ind_cca2_int_ptxt_sym_enc__injbot: ind_cca2_int_ptxt_sym_enc__cleartext -> Tot bitstringbot

assume val ind_cca2_int_ptxt_sym_enc__Z: ind_cca2_int_ptxt_sym_enc__cleartext -> Tot ind_cca2_int_ptxt_sym_enc__cleartext

assume val ind_cca2_int_ptxt_sym_enc__enc: ind_cca2_int_ptxt_sym_enc__cleartext -> ind_cca2_int_ptxt_sym_enc__key -> Tot ind_cca2_int_ptxt_sym_enc__ciphertext


(* SPRP block cipher
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   blocksize: type of the input and output of the cipher, must be "fixed" and "large".
   (The modeling of SPRP block ciphers is not perfect in that, in
   order to encrypt a new message, one chooses a fresh random number,
   not necessarily different from previously generated random
   numbers. Then CryptoVerif needs to eliminate collisions between
   those random numbers, so blocksize must really be "large".)

   enc: encryption function
   dec: decryption function

   Penc(t, N, N'): probability of breaking the SPRP property
   in time t for one key, N encryption queries, and N' decryption queries.

   The types key, blocksize and the probability Penc must be
   declared before this macro is expanded. The functions enc,
   dec are declared by this macro. They must not be declared
   elsewhere, and they can be used only after expanding the macro.

 *)

assume val sprp_cipher__key: Type0
assume val sprp_cipher__blocksize: Type0
assume val sprp_cipher__Penc: probability

assume val sprp_cipher__enc: sprp_cipher__blocksize -> sprp_cipher__key -> Tot sprp_cipher__blocksize

assume val sprp_cipher__dec: sprp_cipher__blocksize -> sprp_cipher__key -> Tot sprp_cipher__blocksize


(* PRP block cipher
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   blocksize: type of the input and output of the cipher, must be "fixed" and "large".
   (The modeling of PRP block ciphers is not perfect in that, in order
   to encrypt a new message, one chooses a fresh random number, not
   necessarily different from previously generated random numbers. In
   other words, we model a PRF rather than a PRP, and apply the
   PRF/PRP switching lemma to make sure that this is sound. Then
   CryptoVerif needs to eliminate collisions between those random
   numbers, so blocksize must really be "large".)

   enc: encryption function
   dec: decryption function

   Penc(t, N): probability of breaking the PRP property
   in time t for one key and N encryption queries.

   The types key, blocksize and the probability Penc must be
   declared before this macro is expanded. The functions enc,
   dec are declared by this macro. They must not be declared
   elsewhere, and they can be used only after expanding the macro.

 *)

assume val prp_cipher__key: Type0
assume val prp_cipher__blocksize: Type0
assume val prp_cipher__Penc: probability

assume val prp_cipher__enc: prp_cipher__blocksize -> prp_cipher__key -> Tot prp_cipher__blocksize

assume val prp_cipher__dec: prp_cipher__blocksize -> prp_cipher__key -> Tot prp_cipher__blocksize


(* Ideal Cipher Model
   cipherkey: type of keys that correspond to the choice of the scheme, must be "bounded", typically "fixed".
   key: type of keys (typically "large")
   blocksize: type of the input and output of the cipher, must be "fixed" and "large".
   (The modeling of the ideal cipher model is not perfect in that, in
   order to encrypt a new message, one chooses a fresh random number,
   not necessarily different from previously generated random
   numbers. Then CryptoVerif needs to eliminate collisions between
   those random numbers, so blocksize must really be "large".)

   enc: encryption function
   dec: decryption function
   WARNING: the encryption and decryption functions take 2 keys as
   input: the key of type cipherkey that corresponds to the choice of
   the scheme, and the normal encryption/decryption key. The cipherkey
   must be chosen once and for all at the beginning of the game and
   the encryption and decryption oracles must be made available to the
   adversary, by including a process enc_dec_oracle(ck) where
   ck is the cipherkey.
   qE is the number of calls of the encryption oracle
   qD is the number of calls of the decryption oracle

   The types cipherkey, key, blocksize must be declared before this
   macro is expanded. The functions enc, dec, the process
   enc_dec_oracle, and the parameters qE, qD are declared by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

 *)

assume val icm_cipher__cipherkey: Type0
assume val icm_cipher__key: Type0
assume val icm_cipher__blocksize: Type0

assume val icm_cipher__enc_dec_oracle: Type0
assume val icm_cipher__qE: Type0
assume val icm_cipher__qD: Type0

assume val icm_cipher__enc: icm_cipher__cipherkey -> icm_cipher__blocksize -> icm_cipher__key -> Tot icm_cipher__blocksize

assume val icm_cipher__dec: icm_cipher__cipherkey -> icm_cipher__blocksize -> icm_cipher__key -> Tot icm_cipher__blocksize


(*************************************** MACs ***************************************)


(* SUF-CMA deterministic mac (strongly unforgeable MAC)
   The difference between a UF-CMA MAC and a SUF-CMA MAC is that, for a UF-CMA MAC, the adversary may
   easily forge a new MAC for a message for which he has already seen a MAC. Such a forgery is guaranteed
   to be hard for a SUF-CMA MAC. For deterministic MACs, the verification can be done by recomputing
   the MAC, and in this case, an UF-CMA MAC is always SUF-CMA, so we model only SUF-CMA deterministic MACs. This macro transforms tests mac(k,m) = m' into check(k, m, m'), so that the MAC verification can also be written mac(k,m) = m'.

   mkey: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   macinput: type of inputs of MACs
   macres: type of result of MACs

   mac: MAC function
   mac': symbol that replaces mac after game transformation
   check: verification function

   Pmac(t, N, N', Nu', l): probability of breaking the SUF-CMA property in
   time t for one key, N MAC queries, N' modified verification queries
   and Nu' unchanged verification queries for
   messages of length at most l.

   The types mkey, macinput, macres and the probability Pmac
   must be declared before this macro is expanded. The functions
   mac, mac', check are declared by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

*)

assume val suf_cma_det_mac__mkey: Type0
assume val suf_cma_det_mac__macinput: Type0
assume val suf_cma_det_mac__macres: Type0

assume val suf_cma_det_mac__Pmac: probability

assume val suf_cma_det_mac__mac: suf_cma_det_mac__macinput -> suf_cma_det_mac__mkey -> Tot suf_cma_det_mac__macres

assume val suf_cma_det_mac__check: suf_cma_det_mac__macinput -> suf_cma_det_mac__mkey -> suf_cma_det_mac__macres -> Tot bool

assume val suf_cma_det_mac__mac': suf_cma_det_mac__macinput -> suf_cma_det_mac__mkey -> Tot suf_cma_det_mac__macres


(* UF-CMA probabilistic mac
   mkey: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   macinput: type of inputs of MACs
   macres: type of result of MACs
   mac_seed: type of random coins for MAC (must be "bounded"; omitted in the second version of the macro).

   mac: MAC function that generates coins internally
   mac_r: MAC function that takes coins as argument (omitted in the second version of the macro).
   check: verification function
   mac_r', check': symbols that replace mac_r and check respectively after game transformation

   Pmac(t, N, N', Nu', l): probability of breaking the UF-CMA property in
   time t for one key, N MAC queries, N' modified verification queries,
   and Nu' unchanged verification queries for
   messages of length at most l.

   The types mkey, macinput, macres, mac_seed and the probability Pmac
   must be declared before this macro is expanded. The functions
   mac, mac_r, mac_r', check, check' are declared by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

*)

assume val uf_cma_proba_mac__mkey: Type0
assume val uf_cma_proba_mac__macinput: Type0
assume val uf_cma_proba_mac__macres: Type0
assume val uf_cma_proba_mac__mac_seed: Type0

assume val uf_cma_proba_mac__Pmac: probability


assume val uf_cma_proba_mac__mac_r: uf_cma_proba_mac__macinput -> uf_cma_proba_mac__mkey -> uf_cma_proba_mac__mac_seed -> Tot uf_cma_proba_mac__macres

assume val uf_cma_proba_mac__check: uf_cma_proba_mac__macinput -> uf_cma_proba_mac__mkey -> uf_cma_proba_mac__macres -> Tot bool

assume val uf_cma_proba_mac__mac_r': uf_cma_proba_mac__macinput -> uf_cma_proba_mac__mkey -> uf_cma_proba_mac__mac_seed -> Tot uf_cma_proba_mac__macres

assume val uf_cma_proba_mac__check': uf_cma_proba_mac__macinput -> uf_cma_proba_mac__mkey -> uf_cma_proba_mac__macres -> Tot bool

assume val uf_cma_proba_mac__mac: uf_cma_proba_mac__macinput -> uf_cma_proba_mac__mkey -> Tot uf_cma_proba_mac__macres


(* SUF-CMA probabilistic mac (strongly unforgeable MAC)
   The difference between a UF-CMA MAC and a SUF-CMA MAC is that, for a UF-CMA MAC, the adversary may
   easily forge a new MAC for a message for which he has already seen a MAC. Such a forgery is guaranteed
   to be hard for a SUF-CMA MAC.

   mkey: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   macinput: type of inputs of MACs
   macres: type of result of MACs
   mac_seed: type of random coins for MAC (must be "bounded"; omitted in the second version of the macro).

   mac: MAC function that generates coins internally
   mac_r: MAC function that takes coins as argument (omitted in the second version of the macro).
   mac_r': symbol that replaces mac_r after game transformation
   check: verification function

   Pmac(t, N, N', Nu', l): probability of breaking the SUF-CMA property in
   time t for one key, N MAC queries, N' modified verification queries,
   Nu' unchanged verification queries for
   messages of length at most l.

   The types mkey, macinput, macres, mac_seed and the probability Pmac
   must be declared before this macro is expanded. The functions
   mac, mac_r, mac_r', check are declared by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

*)

assume val suf_cma_proba_mac__mkey: Type0
assume val suf_cma_proba_mac__macinput: Type0
assume val suf_cma_proba_mac__macres: Type0
assume val suf_cma_proba_mac__mac_seed: Type0

assume val suf_cma_proba_mac__Pmac: probability


assume val suf_cma_proba_mac__mac_r: suf_cma_proba_mac__macinput -> suf_cma_proba_mac__mkey -> suf_cma_proba_mac__mac_seed -> Tot suf_cma_proba_mac__macres

assume val suf_cma_proba_mac__check: suf_cma_proba_mac__macinput -> suf_cma_proba_mac__mkey -> suf_cma_proba_mac__macres -> Tot bool

assume val suf_cma_proba_mac__mac_r': suf_cma_proba_mac__macinput -> suf_cma_proba_mac__mkey -> suf_cma_proba_mac__mac_seed -> Tot suf_cma_proba_mac__macres

assume val suf_cma_proba_mac__mac: suf_cma_proba_mac__macinput -> suf_cma_proba_mac__mkey -> Tot suf_cma_proba_mac__macres


(******************************* Public-key encryption *******************************)

(* IND-CCA2 probabilistic public-key encryption
   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   cleartext: type of cleartexts
   ciphertext: type of ciphertexts
   enc_seed: type of random coins for encryption (must be "bounded"; omitted in the second version of the macro).

   pkgen: public-key generation function
   skgen: secret-key generation function
   enc: encryption function that generates coins internally
   enc_r: encryption function that takes coins as argument (omitted in the second version of the macro).
   dec: decryption function
   pkgen2, skgen2, enc_r2, dec2: symbols that replace pkgen, skgen, enc_r, and dec respectively after game transformation
   injbot: natural injection from cleartext to bitstringbot
   Z: function that returns for each cleartext a cleartext of the same length consisting only of zeroes.

   Penc(t, N): probability of breaking the IND-CCA2 property
   in time t for one key and N decryption queries.
   Penccoll: probability of collision between independently generated keys

   The types keyseed, pkey, skey, cleartext, ciphertext, enc_seed and the
   probabilities Penc, Penccoll must be declared before this macro is
   expanded. The functions pkgen, skgen, enc, enc_r, dec, pkgen2,
   skgen2, enc_r2, dec2, injbot, and Z
   are declared by this macro. They must not be declared
   elsewhere, and they can be used only after expanding the macro.
*)

assume val ind_cca2_public_key_enc__keyseed: Type0
assume val ind_cca2_public_key_enc__pkey: Type0
assume val ind_cca2_public_key_enc__skey: Type0
assume val ind_cca2_public_key_enc__cleartext: Type0
assume val ind_cca2_public_key_enc__ciphertext: Type0
assume val ind_cca2_public_key_enc__enc_seed: Type0

assume val ind_cca2_public_key_enc__Penc: probability
assume val ind_cca2_public_key_enc__Penccoll: probability

assume val ind_cca2_public_key_enc__enc_r: ind_cca2_public_key_enc__cleartext -> ind_cca2_public_key_enc__pkey -> ind_cca2_public_key_enc__enc_seed -> Tot ind_cca2_public_key_enc__ciphertext

assume val ind_cca2_public_key_enc__skgen: ind_cca2_public_key_enc__keyseed -> Tot ind_cca2_public_key_enc__skey

assume val ind_cca2_public_key_enc__pkgen: ind_cca2_public_key_enc__keyseed -> Tot ind_cca2_public_key_enc__pkey

assume val ind_cca2_public_key_enc__dec: ind_cca2_public_key_enc__ciphertext -> ind_cca2_public_key_enc__skey -> Tot bitstringbot

assume val ind_cca2_public_key_enc__enc_r2: ind_cca2_public_key_enc__cleartext -> ind_cca2_public_key_enc__pkey -> ind_cca2_public_key_enc__enc_seed -> Tot ind_cca2_public_key_enc__ciphertext

assume val ind_cca2_public_key_enc__skgen2: ind_cca2_public_key_enc__keyseed -> Tot ind_cca2_public_key_enc__skey

assume val ind_cca2_public_key_enc__pkgen2: ind_cca2_public_key_enc__keyseed -> Tot ind_cca2_public_key_enc__pkey

assume val ind_cca2_public_key_enc__dec2: ind_cca2_public_key_enc__ciphertext -> ind_cca2_public_key_enc__skey -> Tot bitstringbot

assume val ind_cca2_public_key_enc__enc: ind_cca2_public_key_enc__cleartext -> ind_cca2_public_key_enc__pkey -> Tot ind_cca2_public_key_enc__ciphertext

assume val ind_cca2_public_key_enc__injbot: ind_cca2_public_key_enc__cleartext -> Tot bitstringbot

assume val ind_cca2_public_key_enc__Z: ind_cca2_public_key_enc__cleartext -> Tot ind_cca2_public_key_enc__cleartext


(*************************************** Signatures ******************************)

(* UF-CMA deterministic signatures
   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   signinput: type of inputs of signatures
   signature: type of signatures

   pkgen: public-key generation function
   skgen: secret-key generation function
   sign: signature function
   check: verification function
   pkgen2, skgen2, sign2, check2: symbols that replace pkgen, skgen, sign, and check respectively after game transformation

   Psign(t, N, l): probability of breaking the UF-CMA property
   in time t, for one key, N signature queries with messages of length
   at most l.
   Psigncoll: probability of collision between independently generated keys

   The types keyseed, pkey, skey, signinput, signature and the
   probabilities Psign, Psigncoll must be declared before this macro
   is expanded. The functions pkgen, skgen, sign, check, pkgen2,
   skgen2, sign2, check2 are declared by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.
*)

assume val uf_cma_det_signature__keyseed: Type0
assume val uf_cma_det_signature__pkey: Type0
assume val uf_cma_det_signature__skey: Type0
assume val uf_cma_det_signature__signinput: Type0
assume val uf_cma_det_signature__signature: Type0

assume val uf_cma_det_signature__Psign: probability
assume val uf_cma_det_signature__Psigncoll: probability

assume val uf_cma_det_signature__sign: uf_cma_det_signature__signinput -> uf_cma_det_signature__skey -> Tot uf_cma_det_signature__signature

assume val uf_cma_det_signature__skgen: uf_cma_det_signature__keyseed -> Tot uf_cma_det_signature__skey

assume val uf_cma_det_signature__pkgen: uf_cma_det_signature__keyseed -> Tot uf_cma_det_signature__pkey

assume val uf_cma_det_signature__check: uf_cma_det_signature__signinput -> uf_cma_det_signature__pkey -> uf_cma_det_signature__signature -> Tot bool

assume val uf_cma_det_signature__sign2: uf_cma_det_signature__signinput -> uf_cma_det_signature__skey -> Tot uf_cma_det_signature__signature

assume val uf_cma_det_signature__skgen2: uf_cma_det_signature__keyseed -> Tot uf_cma_det_signature__skey

assume val uf_cma_det_signature__pkgen2: uf_cma_det_signature__keyseed -> Tot uf_cma_det_signature__pkey

assume val uf_cma_det_signature__check2: uf_cma_det_signature__signinput -> uf_cma_det_signature__pkey -> uf_cma_det_signature__signature -> Tot bool


(* SUF-CMA deterministic signatures
   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   signinput: type of inputs of signatures
   signature: type of signatures

   pkgen: public-key generation function
   skgen: secret-key generation function
   sign: signature function
   check: verification function
   pkgen2, skgen2, sign2, check2: symbols that replace pkgen, skgen, sign, and check respectively after game transformation

   Psign(t, N, l): probability of breaking the SUF-CMA property
   in time t, for one key, N signature queries with messages of length
   at most l.
   Psigncoll: probability of collision between independently generated keys

   The types keyseed, pkey, skey, signinput, signature and the
   probabilities Psign, Psigncoll must be declared before this macro
   is expanded. The functions pkgen, skgen, sign, check, pkgen2,
   skgen2, sign2, check2 are declared by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.
*)


assume val suf_cma_det_signature__keyseed: Type0
assume val suf_cma_det_signature__pkey: Type0
assume val suf_cma_det_signature__skey: Type0
assume val suf_cma_det_signature__signinput: Type0
assume val suf_cma_det_signature__signature: Type0

assume val suf_cma_det_signature__Psign: probability
assume val suf_cma_det_signature__Psigncoll: probability

assume val suf_cma_det_signature__sign: suf_cma_det_signature__signinput -> suf_cma_det_signature__skey -> Tot suf_cma_det_signature__signature

assume val suf_cma_det_signature__skgen: suf_cma_det_signature__keyseed -> Tot suf_cma_det_signature__skey

assume val suf_cma_det_signature__pkgen: suf_cma_det_signature__keyseed -> Tot suf_cma_det_signature__pkey

assume val suf_cma_det_signature__check: suf_cma_det_signature__signinput -> suf_cma_det_signature__pkey -> suf_cma_det_signature__signature -> Tot bool

assume val suf_cma_det_signature__sign2: suf_cma_det_signature__signinput -> suf_cma_det_signature__skey -> Tot suf_cma_det_signature__signature

assume val suf_cma_det_signature__skgen2: suf_cma_det_signature__keyseed -> Tot suf_cma_det_signature__skey

assume val suf_cma_det_signature__pkgen2: suf_cma_det_signature__keyseed -> Tot suf_cma_det_signature__pkey

assume val suf_cma_det_signature__check2: suf_cma_det_signature__signinput -> suf_cma_det_signature__pkey -> suf_cma_det_signature__signature -> Tot bool


(* UF-CMA probabilistic signatures
   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   signinput: type of inputs of signatures
   signature: type of signatures
   sign_seed: type of random coins for signature (must be "bounded"; omitted in the second version of the macro).

   pkgen: public-key generation function
   skgen: secret-key generation function
   sign: signature function that generates coins internally
   sign_r: signature function that takes coins as argument (omitted in the second version of the macro).
   check: verification function
   pkgen2, skgen2, sign_r2, check2: symbols that replace pkgen, skgen, sign, and check respectively after game transformation

   Psign(t, N, l): probability of breaking the UF-CMA property
   in time t, for one key, N signature queries with messages of length
   at most l.
   Psigncoll: probability of collision between independently generated keys

   The types keyseed, pkey, skey, signinput, signature, seed and the
   probabilities Psign, Psigncoll must be declared before this macro
   is expanded. The functions pkgen, skgen, sign, check, pkgen2,
   skgen2, sign_r2, check2 are declared by this macro. They must not
   be declared elsewhere, and they can be used only after expanding
   the macro.
*)

assume val uf_cma_proba_signature__keyseed: Type0
assume val uf_cma_proba_signature__pkey: Type0
assume val uf_cma_proba_signature__skey: Type0
assume val uf_cma_proba_signature__signinput: Type0
assume val uf_cma_proba_signature__signature: Type0
assume val uf_cma_proba_signature__sign_seed: Type0

assume val uf_cma_proba_signature__Psign: probability
assume val uf_cma_proba_signature__Psigncoll: probability

assume val uf_cma_proba_signature__sign_r: uf_cma_proba_signature__signinput -> uf_cma_proba_signature__skey -> uf_cma_proba_signature__sign_seed -> Tot uf_cma_proba_signature__signature

assume val uf_cma_proba_signature__skgen: uf_cma_proba_signature__keyseed -> Tot uf_cma_proba_signature__skey

assume val uf_cma_proba_signature__pkgen: uf_cma_proba_signature__keyseed -> Tot uf_cma_proba_signature__pkey

assume val uf_cma_proba_signature__check: uf_cma_proba_signature__signinput -> uf_cma_proba_signature__pkey -> uf_cma_proba_signature__signature -> Tot bool


assume val uf_cma_proba_signature__sign_r2: uf_cma_proba_signature__signinput -> uf_cma_proba_signature__skey -> uf_cma_proba_signature__sign_seed -> Tot uf_cma_proba_signature__signature

assume val uf_cma_proba_signature__skgen2: uf_cma_proba_signature__keyseed -> Tot uf_cma_proba_signature__skey

assume val uf_cma_proba_signature__pkgen2: uf_cma_proba_signature__keyseed -> Tot uf_cma_proba_signature__pkey

assume val uf_cma_proba_signature__check2: uf_cma_proba_signature__signinput -> uf_cma_proba_signature__pkey -> uf_cma_proba_signature__signature -> Tot bool

assume val uf_cma_proba_signature__sign: uf_cma_proba_signature__signinput -> uf_cma_proba_signature__skey -> Tot uf_cma_proba_signature__signature


(* SUF-CMA probabilistic signatures
   keyseed: type of key seeds, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   signinput: type of inputs of signatures
   signature: type of signatures
   sign_seed: type of random coins for signature (must be "bounded"; omitted in the second version of the macro).

   pkgen: public-key generation function
   skgen: secret-key generation function
   sign: signature function that generates coins internally
   sign_r: signature function that takes coins as argument (omitted in the second version of the macro).
   check: verification function
   pkgen2, skgen2, sign_r2, check2: symbols that replace pkgen, skgen, sign, and check respectively after game transformation

   Psign(t, N, l): probability of breaking the SUF-CMA property
   in time t, for one key, N signature queries with messages of length
   at most l.
   Psigncoll: probability of collision between independently generated keys

   The types keyseed, pkey, skey, signinput, signature, seed and the
   probabilities Psign, Psigncoll must be declared before this macro
   is expanded. The functions pkgen, skgen, sign, check, pkgen2,
   skgen2, sign_r2, check2 are declared by this macro. They must not
   be declared elsewhere, and they can be used only after expanding
   the macro.
*)

assume val suf_cma_proba_signature__keyseed: Type0
assume val suf_cma_proba_signature__pkey: Type0
assume val suf_cma_proba_signature__skey: Type0
assume val suf_cma_proba_signature__signinput: Type0
assume val suf_cma_proba_signature__signature: Type0
assume val suf_cma_proba_signature__sign_seed: Type0

assume val suf_cma_proba_signature__Psign: probability
assume val suf_cma_proba_signature__Psigncoll: probability

assume val suf_cma_proba_signature__sign_r: suf_cma_proba_signature__signinput -> suf_cma_proba_signature__skey -> suf_cma_proba_signature__sign_seed -> Tot suf_cma_proba_signature__signature

assume val suf_cma_proba_signature__skgen: suf_cma_proba_signature__keyseed -> Tot suf_cma_proba_signature__skey

assume val suf_cma_proba_signature__pkgen: suf_cma_proba_signature__keyseed -> Tot suf_cma_proba_signature__pkey

assume val suf_cma_proba_signature__check: suf_cma_proba_signature__signinput -> suf_cma_proba_signature__pkey -> suf_cma_proba_signature__signature -> Tot bool


assume val suf_cma_proba_signature__sign_r2: suf_cma_proba_signature__signinput -> suf_cma_proba_signature__skey -> suf_cma_proba_signature__sign_seed -> Tot suf_cma_proba_signature__signature

assume val suf_cma_proba_signature__skgen2: suf_cma_proba_signature__keyseed -> Tot suf_cma_proba_signature__skey

assume val suf_cma_proba_signature__pkgen2: suf_cma_proba_signature__keyseed -> Tot suf_cma_proba_signature__pkey

assume val suf_cma_proba_signature__check2: suf_cma_proba_signature__signinput -> suf_cma_proba_signature__pkey -> suf_cma_proba_signature__signature -> Tot bool

assume val suf_cma_proba_signature__sign: suf_cma_proba_signature__signinput -> suf_cma_proba_signature__skey -> Tot suf_cma_proba_signature__signature


(******************************* Hash functions ****************************)

(* Hash function in the random oracle model
   key: type of the key of the hash function, which models the choice of the hash function, must be "bounded", typically "fixed"
   hashinput: type of the input of the hash function
   hashoutput: type of the output of the hash function, must be "bounded" and "large", typically "fixed".

   hash: the hash function.
   WARNING: hash is a keyed hash function.
   The key must be generated once and for all at the beginning of the game
   and the hash oracle must be made available to the adversary,
   by including the process hashoracle(k) where k is the key.
   qH is the number of calls to hashoracle.

   The types key, hashinput, and hashoutput must be declared before
   this macro. The function hash, the process hashoracle, and
   the parameter qH are defined by this macro. They must not
   be declared elsewhere, and they can be used only after expanding the
   macro.

 *)

assume val rom_hash__key: Type0
assume val rom_hash__hashinput: Type0
assume val rom_hash__hashoutput: Type0

assume val rom_hash__hashOracle: Type0
assume val rom_hash__qH: Type0

assume val rom_hash__hash: rom_hash__key -> rom_hash__hashinput -> Tot rom_hash__hashoutput


(* ROM_hash_pair, ROM_hash_triple, and ROM_hash_quad are similar
   to ROM_hash, for random oracle with 2, 3, and 4 arguments
   respectively. Letting N be the number of arguments of the oracle,
   hashinput1...hashinputN are the types of the inputs of the hash function
*)

assume val rom_hash_pair__key: Type0
assume val rom_hash_pair__hashinput1: Type0
assume val rom_hash_pair__hashinput2: Type0
assume val rom_hash_pair__hashoutput: Type0

assume val rom_hash_pair__hashOracle: Type0
assume val rom_hash_pair__qH: Type0

assume val rom_hash_pair__hash: rom_hash_pair__key -> rom_hash_pair__hashinput1 -> rom_hash_pair__hashinput2 -> Tot rom_hash_pair__hashoutput


assume val rom_hash_triple__key: Type0
assume val rom_hash_triple__hashinput1: Type0
assume val rom_hash_triple__hashinput2: Type0
assume val rom_hash_triple__hashinput3: Type0
assume val rom_hash_triple__hashoutput: Type0

assume val rom_hash_triple__hashOracle: Type0
assume val rom_hash_triple__qH: Type0

assume val rom_hash_triple__hash: rom_hash_triple__key -> rom_hash_triple__hashinput1 -> rom_hash_triple__hashinput2 -> rom_hash_triple__hashinput3 -> Tot rom_hash_pair__hashoutput


assume val rom_hash_quad__key: Type0
assume val rom_hash_quad__hashinput1: Type0
assume val rom_hash_quad__hashinput2: Type0
assume val rom_hash_quad__hashinput3: Type0
assume val rom_hash_quad__hashoutput: Type0

assume val rom_hash_quad__hashOracle: Type0
assume val rom_hash_quad__qH: Type0

assume val rom_hash_quad__hash: rom_hash_quad__key -> rom_hash_quad__hashinput1 -> rom_hash_quad__hashinput2 -> rom_hash_quad__hashinput3 -> Tot rom_hash_pair__hashoutput


(* Collision resistant hash function
   key: type of the key of the hash function, must be "bounded", typically "fixed"
   hashinput: type of the input of the hash function
   hashoutput: type of the output of the hash function

   hash: the hash function.
   Phash: probability of breaking collision resistance.
   WARNING: A collision resistant hash function is a keyed hash function.
   The key must be generated once and for all at the beginning of the game,
   and immediately made available to the adversary, for instance by
   including the process hashoracle(k), where k is the key.

   The types key, hashinput, hashoutput, and the probability Phash
   must be declared before this macro.  The function hash and the
   process hashoracle are defined by this macro. They must not be
   declared elsewhere, and they can be used only after expanding the
   macro.

 *)

assume val collision_resistant_hash__key: Type0
assume val collision_resistant_hash__hashinput: Type0
assume val collision_resistant_hash__hashoutput: Type0

assume val collision_resistant_hash__hashoracle: Type0
assume val collision_resistant_hash__Phash: probability

assume val collision_resistant_hash__hash: collision_resistant_hash__key -> collision_resistant_hash__hashinput -> Tot collision_resistant_hash__hashoutput


(******************************** Diffie-Hellman ***************************)

(* Computational Diffie-Hellman
   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pCDH: the probability of breaking the CDH assumption

   The types G and Z and the probability pCDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

*)

assume val cdh__G: Type0
assume val cdh__Z: Type0
assume val cdh__g: cdh__G

assume val cdh__pCDH: probability

assume val cdh__exp: cdh__G -> cdh__Z -> Tot cdh__G

assume val cdh__exp': cdh__G -> cdh__Z -> Tot cdh__G

assume val cdh__mult: cdh__Z -> cdh__Z -> Tot cdh__Z


(* Decisional Diffie-Hellman
   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pDDH: the probability of breaking the DDH assumption

   The types G and Z and the probability pDDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.
*)

assume val ddh__G: Type0
assume val ddh__Z: Type0
assume val ddh__g: ddh__G

assume val ddh__pDDH: probability

assume val ddh__exp: ddh__G -> ddh__Z -> Tot ddh__G

assume val ddh__exp': ddh__G -> ddh__Z -> Tot ddh__G

assume val ddh__mult: ddh__Z -> ddh__Z -> Tot ddh__Z


(* Gap Diffie-Hellman
   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pGDH: the probability of breaking the GDH assumption

   The types G and Z and the probability pGDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

*)

assume val gdh__G: Type0
assume val gdh__Z: Type0
assume val gdh__g: gdh__G

assume val gdh__pGDH: probability

assume val gdh__exp: gdh__G -> gdh__Z -> Tot gdh__G

assume val gdh__exp': gdh__G -> gdh__Z -> Tot gdh__G

assume val gdh__mult: gdh__Z -> gdh__Z -> Tot gdh__Z



assume val gdh_prime_order__G: Type0
assume val gdh_prime_order__Z: Type0
assume val gdh_prime_order__g: gdh_prime_order__G

assume val gdh_prime_order__pGDH_PRIME_ORDER: probability

assume val gdh_prime_order__exp: gdh_prime_order__G -> gdh_prime_order__Z -> Tot gdh_prime_order__G

assume val gdh_prime_order__exp': gdh_prime_order__G -> gdh_prime_order__Z -> Tot gdh_prime_order__G

assume val gdh_prime_order__mult: gdh_prime_order__Z -> gdh_prime_order__Z -> Tot gdh_prime_order__Z


(* square Computational Diffie-Hellman and Computational Diffie-Hellman.

   When the group is of prime order, the square CDH assumption is
   equivalent to the CDH assumption (but CryptoVerif can prove more
   using the square variant).

   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pCDH: the probability of breaking the square CDH assumption

   The types G and Z and the probability pCDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

*)

assume val square_cdh__G: Type0
assume val square_cdh__Z: Type0
assume val square_cdh__g: square_cdh__G

assume val square_cdh__pCDH: probability

assume val square_cdh__exp: square_cdh__G -> square_cdh__Z -> Tot square_cdh__G

assume val square_cdh__exp': square_cdh__G -> square_cdh__Z -> Tot square_cdh__G

assume val square_cdh__mult: square_cdh__Z -> square_cdh__Z -> Tot square_cdh__Z


(* square Decisional Diffie-Hellman and Decisional Diffie-Hellman

   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pDDH: the probability of breaking the square DDH assumption

   The types G and Z and the probability pDDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.
*)

assume val square_ddh__G: Type0
assume val square_ddh__Z: Type0
assume val square_ddh__g: square_ddh__G

assume val square_ddh__pDDH: probability

assume val square_ddh__exp: square_ddh__G -> square_ddh__Z -> Tot square_ddh__G

assume val square_ddh__exp': square_ddh__G -> square_ddh__Z -> Tot square_ddh__G

assume val square_ddh__mult: square_ddh__Z -> square_ddh__Z -> Tot square_ddh__Z

(* square Gap Diffie-Hellman and Gap Diffie-Hellman.

   When the group is of prime order, the square GDH assumption is
   equivalent to the GDH assumption (but CryptoVerif can prove more
   using the square variant).

   G: type of group elements (must be "bounded" and "large", of cardinal
   a prime q)
   Z: type of exponents (must be "bounded" and "large", supposed to be
   {1, ..., q-1})

   g: a generator of the group
   exp: the exponentiation function
   exp': symbol that replaces exp after game transformation
   mult: the multiplication function for exponents, product modulo q in
   {1, ..., q-1}, i.e. in the group (Z/qZ)*

   pGDH: the probability of breaking the square GDH assumption

   The types G and Z and the probability pGDH must be declared before
   this macro.  The functions g, exp, and mult are defined by this
   macro. They must not be declared elsewhere, and they can be used
   only after expanding the macro.

*)

assume val square_gdh__G: Type0
assume val square_gdh__Z: Type0
assume val square_gdh__g: square_gdh__G

assume val square_gdh__pGDH: probability

assume val square_gdh__exp: square_gdh__G -> square_gdh__Z -> Tot square_gdh__G

assume val square_gdh__exp': square_gdh__G -> square_gdh__Z -> Tot square_gdh__G

assume val square_gdh__mult: square_gdh__Z -> square_gdh__Z -> Tot square_gdh__Z


assume val square_gdh_prime_order__G: Type0
assume val square_gdh_prime_order__Z: Type0
assume val square_gdh_prime_order__g: square_gdh_prime_order__G

assume val square_gdh_prime_order__pGDH: probability

assume val square_gdh_prime_order__exp: square_gdh_prime_order__G -> square_gdh_prime_order__Z -> Tot square_gdh_prime_order__G

assume val square_gdh_prime_order__exp': square_gdh_prime_order__G -> square_gdh_prime_order__Z -> Tot square_gdh_prime_order__G

assume val square_gdh_prime_order__mult: square_gdh_prime_order__Z -> square_gdh_prime_order__Z -> Tot square_gdh_prime_order__Z


(********************************* Miscellaneous ***************************)

(* One-way trapdoor permutation
   seed: type of random seeds to generate keys, must be "bounded", typically "fixed"
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   D: type of the input and output of the permutation, must be "bounded", typically "fixed"

   pkgen: public-key generation function
   skgen: secret-key generation function
   f: the permutation (taking as argument the public key)
   invf: the inverse permutation of f (taking as argument the secret key,
         i.e. the trapdoor)
   pkgen', f': symbols that replace pkgen and f respectively after game transformation

   POW(t): probability of breaking the one-wayness property
   in time t, for one key and one permuted value.

   The types seed, pkey, skey, D, and the probability POW must be
   declared before this macro. The functions pkgen, skgen, f, invf
   are defined by this macro. They must not be declared elsewhere, and
   they can be used only after expanding the macro.
*)

assume val ow_trapdoor_perm__seed: Type0
assume val ow_trapdoor_perm__pkey: Type0
assume val ow_trapdoor_perm__skey: Type0
assume val ow_trapdoor_perm__D: Type0
assume val ow_trapdoor_perm__POW: probability

assume val ow_trapdoor_perm__pkgen: ow_trapdoor_perm__seed -> Tot ow_trapdoor_perm__pkey

assume val ow_trapdoor_perm__pkgen': ow_trapdoor_perm__seed -> Tot ow_trapdoor_perm__pkey

assume val ow_trapdoor_perm__skgen: ow_trapdoor_perm__seed -> Tot ow_trapdoor_perm__skey

assume val ow_trapdoor_perm__f: ow_trapdoor_perm__pkey -> ow_trapdoor_perm__D -> Tot ow_trapdoor_perm__D

assume val ow_trapdoor_perm__f': ow_trapdoor_perm__pkey -> ow_trapdoor_perm__D -> Tot ow_trapdoor_perm__D

assume val ow_trapdoor_perm__invf: ow_trapdoor_perm__skey -> ow_trapdoor_perm__D -> Tot ow_trapdoor_perm__D

(* One-way trapdoor permutation, with random self-reducibility.
   Same as above, but with a smaller probability of attack
*)

assume val ow_trapdoor_perm_rsr__seed: Type0
assume val ow_trapdoor_perm_rsr__pkey: Type0
assume val ow_trapdoor_perm_rsr__skey: Type0
assume val ow_trapdoor_perm_rsr__D: Type0
assume val ow_trapdoor_perm_rsr__POW: probability

assume val ow_trapdoor_perm_rsr__pkgen: ow_trapdoor_perm_rsr__seed -> Tot ow_trapdoor_perm_rsr__pkey

assume val ow_trapdoor_perm_rsr__pkgen': ow_trapdoor_perm_rsr__seed -> Tot ow_trapdoor_perm_rsr__pkey

assume val ow_trapdoor_perm_rsr__skgen: ow_trapdoor_perm_rsr__seed -> Tot ow_trapdoor_perm_rsr__skey

assume val ow_trapdoor_perm_rsr__f: ow_trapdoor_perm_rsr__pkey -> ow_trapdoor_perm_rsr__D -> Tot ow_trapdoor_perm_rsr__D

assume val ow_trapdoor_perm_rsr__f': ow_trapdoor_perm_rsr__pkey -> ow_trapdoor_perm_rsr__D -> Tot ow_trapdoor_perm_rsr__D

assume val ow_trapdoor_perm_rsr__invf: ow_trapdoor_perm_rsr__skey -> ow_trapdoor_perm_rsr__D -> Tot ow_trapdoor_perm_rsr__D


(* Set partial-domain one-way trapdoor permutation
   seed: type of random seeds to generate keys, must be "bounded", typically "fixed"
   pkey: type of public keys, must be "bounded"
   skey: type of secret keys, must be "bounded"
   D: type of the input and output of the permutation, must be "bounded", typically "fixed"
   The domain D consists of the concatenation of bitstrings in Dow and Dr.
   Dow is the set of sub-bitstrings of D on which one-wayness holds (it is difficult to compute the
   random element x of Dow knowing f(pk, concat(x,y)) where y is a random element of Dr).
   Dow and Dr must be "bounded", typically "fixed".

   pkgen: public-key generation function
   skgen: secret-key generation function
   f: the permutation (taking as argument the public key)
   invf: the inverse permutation of f (taking as argument the secret key,
         i.e. the trapdoor)
   concat(Dow, Dr):D is bitstring concatenation
   pkgen', f': symbols that replace pkgen and f respectively after game transformation

   P_PD_OW(t,l): probability of breaking the set partial-domain one-wayness property
   in time t, for one key, one permuted value, and l tries.

   The types seed, pkey, skey, D, Dow, Dr and the probability P_PD_OW must be
   declared before this macro. The functions pkgen, skgen, f, invf, concat
   are defined by this macro. They must not be declared elsewhere, and
   they can be used only after expanding the macro.
*)

assume val set_pd_ow_trapdoor_perm__seed: Type0
assume val set_pd_ow_trapdoor_perm__pkey: Type0
assume val set_pd_ow_trapdoor_perm__skey: Type0
assume val set_pd_ow_trapdoor_perm__D: Type0
assume val set_pd_ow_trapdoor_perm__Dow: Type0
assume val set_pd_ow_trapdoor_perm__Dr: Type0

assume val set_pd_ow_trapdoor_perm__P_PD_OW: probability



assume val set_pd_ow_trapdoor_perm__pkgen: set_pd_ow_trapdoor_perm__seed -> Tot set_pd_ow_trapdoor_perm__pkey

assume val set_pd_ow_trapdoor_perm__pkgen': set_pd_ow_trapdoor_perm__seed -> Tot set_pd_ow_trapdoor_perm__pkey

assume val set_pd_ow_trapdoor_perm__skgen: set_pd_ow_trapdoor_perm__seed -> Tot set_pd_ow_trapdoor_perm__skey

assume val set_pd_ow_trapdoor_perm__f: set_pd_ow_trapdoor_perm__pkey -> set_pd_ow_trapdoor_perm__D -> Tot set_pd_ow_trapdoor_perm__D

assume val set_pd_ow_trapdoor_perm__f': set_pd_ow_trapdoor_perm__pkey -> set_pd_ow_trapdoor_perm__D -> Tot set_pd_ow_trapdoor_perm__D

assume val set_pd_ow_trapdoor_perm__invf: set_pd_ow_trapdoor_perm__skey -> set_pd_ow_trapdoor_perm__D -> Tot set_pd_ow_trapdoor_perm__D

assume val set_pd_ow_trapdoor_perm__concat: set_pd_ow_trapdoor_perm__Dow -> set_pd_ow_trapdoor_perm__Dr -> Tot set_pd_ow_trapdoor_perm__D


(* Pseudo random function (PRF)
   key: type of keys, must be "bounded" (to be able to generate random numbers from it), typically "fixed" and "large".
   input: type of the input of the PRF.
   output: type of the output of the PRF, must be "bounded", typically "fixed".

   f: PRF function

   Pprf(t, N, l): probability of breaking the PRF property
   in time t, for one key, N queries to the PRF of length at most l.

   The types key, input, output and the probability Pprf must
   be declared before this macro is expanded. The function f
   is declared by this macro. It must not be declared elsewhere,
   and it can be used only after expanding the macro.

*)

assume val prf__key: Type0
assume val prf__input: Type0
assume val prf__output: Type0
assume val prf__Pprf: probability

assume val prf__f: prf__key -> prf__input -> Tot prf__output


(* Xor
   D: domain on which xor applies
   xor: the exclusive or function
   zero: the neutral element

   The type D must be declared before this macro is expanded. The
   function xor and the constant zero are declared by this macro. They
   must not be declared elsewhere, and they can be used only after
   expanding the macro.
 *)

assume val xor__D: Type0
assume val xor__zero: xor__D

assume val xor__xor: xor__D -> xor__D -> Tot xor__D


(* *********** Composition of several primitives ********************

TODO

*)
