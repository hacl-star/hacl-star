module NaCl

open FStar.HyperStack


////////////////////////////////////////////////////////////////// 
//
// Hashing functions
//

// @hash : location of the resulting data
// @data : location of the data to be processed
// @len  : length of the data to be processed

val crypto_hash: hash:bytes -> data:bytes -> len:nat -> STL int
val crypto_hash_sha256: hash:bytes -> data:bytes -> len:nat -> STL int
val crypto_hash_sha512: hash:bytes -> data:bytes -> len:nat -> STL int


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for secret-key cryptography
//

// Function : crypto_secretbox
//
// The crypto_secretbox function encrypts and authenticates a 
// message m[0], m[1], ..., m[mlen-1] using a 
// secret key k[0], ..., k[crypto_secretbox_KEYBYTES-1] and a 
// nonce n[0], n[1], ..., n[crypto_secretbox_NONCEBYTES-1]. 
// The crypto_secretbox function puts the ciphertext into c[0], c[1], ..., c[mlen-1].
// The crypto_secretbox function then returns 0.
//
// WARNING: Messages in the C NaCl API are 0-padded versions of messages in the C++ NaCl API.
// Specifically: The caller must ensure, before calling the C NaCl crypto_secretbox function,
// that the first crypto_secretbox_ZEROBYTES bytes of the message m are all 0. 
// Typical higher-level applications will work with the remaining bytes of the message; 
// note, however, that mlen counts all of the bytes, including the bytes required to be 0.
//
// Similarly, ciphertexts in the C NaCl API are 0-padded versions of messages in the C++ NaCl API. 
// Specifically: The crypto_secretbox function ensures that the first crypto_secretbox_BOXZEROBYTES
// bytes of the ciphertext c are all 0.
//
// @ciphertext : location of the resulting data
// @message    : bytes of the message
// @len        : length of the message
// @nonce      : bytes of the nonce
// @key        : bytes of the key

val crypto_secretbox: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int
val crypto_secretbox_aes256gcm: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int
val crypto_secretbox_xsalsa20poly1305: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int

// Function : crypto_secretbox_open
//
// The crypto_secretbox_open function verifies and decrypts a 
// ciphertext c[0], c[1], ..., c[clen-1] using a 
// secret key k[0], k[1], ..., k[crypto_secretbox_KEYBYTES-1] and a 
// nonce n[0], ..., n[crypto_secretbox_NONCEBYTES-1]. 
// The crypto_secretbox_open function puts the plaintext into m[0], m[1], ..., m[clen-1].
// The crypto_secretbox_open function then returns 0.
//
// If the ciphertext fails verification, crypto_secretbox_open instead returns -1, 
// possibly after modifying m[0], m[1], etc.
// The caller must ensure, before calling the crypto_secretbox_open function,
// that the first crypto_secretbox_BOXZEROBYTES bytes of the ciphertext c are all 0. 
// The crypto_secretbox_open function ensures (in case of success) that the 
// first crypto_secretbox_ZEROBYTES bytes of the plaintext m are all 0.
//
// @message    : location of the resulting data
// @ciphertext : bytes of the message
// @len        : length of the ciphertext
// @nonce      : bytes of the nonce
// @key        : bytes of the key

val crypto_secretbox_open: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int
val crypto_secretbox_open_aes256gcm: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int
val crypto_secretbox_open_xsalsa20poly1305: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> key:bytes -> STL int


////////////////////////////////////////////////////////////////// 
//
// Authenticated encryption functions for public-key cryptography
//


// Function : crypto_box_keypair
//
// The crypto_box_keypair function randomly generates a secret key and a corresponding public key. 
// It puts the secret key into sk[0], sk[1], ..., sk[crypto_box_SECRETKEYBYTES-1] and puts 
// the public key into pk[0], pk[1], ..., pk[crypto_box_PUBLICKEYBYTES-1].
// 
// @pkey : location of the resulting public key
// @skey : location of the resulting secret key

val crypto_box_keypair: pkey:bytes -> skey:bytes -> STL int

// Function : crypto_box
//
// The crypto_box function encrypts and authenticates a message m using 
// the sender's secret key sk, the receiver's public key pk, and a
// nonce n[0], n[1], ..., n[crypto_box_NONCEBYTES-1]. 
// The crypto_box function puts the ciphertext into c[0], c[1], ..., c[mlen-1].
// The crypto_box function then returns 0.
// 
// WARNING: Messages in the C NaCl API are 0-padded versions of messages in the C++ NaCl API. 
// Specifically: The caller must ensure, before calling the C NaCl crypto_box function,
// that the first crypto_box_ZEROBYTES bytes of the message m are all 0. 
// Typical higher-level applications will work with the remaining bytes of the message;
// note, however, that mlen counts all of the bytes, including the bytes required to be 0.
//
// Similarly, ciphertexts in the C NaCl API are 0-padded versions of messages in the C++ NaCl API.
// Specifically: The crypto_box function ensures that the first crypto_box_BOXZEROBYTES bytes of the ciphertext c are all 0.
//
// @ciphertext : location of the resulting data
// @message    : bytes of the message
// @len        : length of the message
// @nonce      : bytes of the nonce
// @pkey       : bytes of the receiver's public key
// @skey       : bytes of the sender's secret key

val crypto_box: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int
val crypto_box_nistp256aes256gcm: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int
val crypto_box_curve25519xsalsa20poly1305: ciphertext:bytes -> message:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int

// Function : crypto_box_open
//
// The crypto_box_open function verifies and decrypts a ciphertext c[0], ..., c[clen-1] 
// using the receiver's secret key sk[0], sk[1], ..., sk[crypto_box_SECRETKEYBYTES-1], 
// the sender's public key pk[0], pk[1], ..., pk[crypto_box_PUBLICKEYBYTES-1], and a 
// nonce n[0], ..., n[crypto_box_NONCEBYTES-1]. 
// The crypto_box_open function puts the plaintext into m[0], m[1], ..., m[clen-1].
// The crypto_box_open function then returns 0.
//
// If the ciphertext fails verification, crypto_box_open instead returns -1, possibly after modifying m[0], m[1], etc.
// The caller must ensure, before calling the crypto_box_open function, that the 
// first crypto_box_BOXZEROBYTES bytes of the ciphertext c are all 0. 
// The crypto_box_open function ensures (in case of success) that the first crypto_box_ZEROBYTES 
// bytes of the plaintext m are all 0.

// @message : location of the resulting data
// @ciphertext : bytes of the message
// @len        : length of the ciphertext
// @nonce      : bytes of the nonce
// @pkey       : bytes of the receiver's public key
// @skey       : bytes of the sender's secret key

val crypto_box_open: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int
val crypto_box_open_nistp256aes256gcm: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int
val crypto_box_open_curve25519xsalsa20poly1305: message:bytes -> ciphertext:bytes -> len:nat -> nonce:bytes -> pkey:bytes -> skey:bytes -> STL int

