#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "tmp/Crypto_Indexing.h"
#include "tmp/Crypto_Symmetric_Bytes.h"
#include "tmp/Crypto_Symmetric_MAC.h"
#include "tmp/Crypto_AEAD.h"

typedef Crypto_AEAD_Invariant_aead_state_______ AEAD_ST;
typedef Crypto_Indexing_id ID;

typedef struct {
        AEAD_ST *st;
        ID id;
} ST;

#define ST_val(v) (*((ST**) Data_custom_val(v)))

static value Val_some(value mlvalue) {
    CAMLparam1(mlvalue);
    CAMLlocal1(aout);

    aout = caml_alloc(1, 0);
    Store_field(aout, 0, mlvalue);

    CAMLreturn(aout);
}

#define Val_none Val_int(0)

static void ocaml_ST_finalize(value st) {
    ST* s = ST_val(st);

    if(s != NULL) {
        AEAD_ST *st = s->st;
        if(st != NULL) {
                free(st);
        }
        free(s);
    }
}

static struct custom_operations st_ops = {
  .identifier  = "ocaml_st",
  .finalize    = ocaml_ST_finalize,
  .compare     = custom_compare_default,
  .hash        = custom_hash_default,
  .serialize   = custom_serialize_default,
  .deserialize = custom_deserialize_default,
};

CAMLprim value ocaml_AEAD_create(value alg, value impl, value key) {
        CAMLparam2(alg, key);
        Crypto_Indexing_aeadAlg calg;
	Crypto_Indexing_aesImpl aesimpl;

        switch(Int_val(alg)){
                case 0:
                        calg = Crypto_Indexing_AES_128_GCM;
                        break;
                case 1:
                        calg = Crypto_Indexing_AES_256_GCM;
                        break;
                case 2:
                        calg = Crypto_Indexing_CHACHA20_POLY1305;
                        break;
                default:
                        caml_failwith("LowCProvider: unsupported AEAD alg");
        }

	switch(Int_val(impl)){
		case 0:
			aesimpl = Crypto_Indexing_HaclAES;
			break;
		case 1:
			aesimpl = Crypto_Indexing_ValeAES;
			break;
		default:
			caml_failwith("LowCProvider: invalid AES implementation");
	}

        Crypto_Indexing_id id = Crypto_Indexing_testId(calg);
	id.aesi = aesimpl;

        AEAD_ST* st = malloc(sizeof(AEAD_ST));
       	*st = Crypto_AEAD_coerce(id, (uint8_t*)String_val(key));

        ST *s = malloc(sizeof(ST));
        s->st = st;
        s->id = id;

        CAMLlocal1(mlret);
        mlret = caml_alloc_custom(&st_ops, sizeof(ST*), 0, 1);
        ST_val(mlret) = s;
        CAMLreturn(mlret);
}

CAMLprim value ocaml_AEAD_encrypt(value state, value iv, value ad, value plain) {
        CAMLparam4(state, iv, ad, plain);

        ST* st = ST_val(state);
        AEAD_ST *ast = st->st;
        ID id = st->id; 
        uint8_t* civ = (uint8_t*) String_val(iv);
        FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128((uint32_t )caml_string_length(iv), civ);
        uint8_t* cad = (uint8_t*) String_val(ad);
        uint32_t adlen = caml_string_length(ad);
        uint8_t* cplain = (uint8_t*) String_val(plain);
        uint32_t plainlen = caml_string_length(plain);

        CAMLlocal1(cipher);
        cipher = caml_alloc_string(plainlen + Crypto_Symmetric_MAC_taglen);
        uint8_t* ccipher = (uint8_t*) String_val(cipher);
        Crypto_AEAD_Encrypt_encrypt(id, *ast, n, adlen, cad, plainlen, cplain, ccipher);
        CAMLreturn(cipher);
}

CAMLprim value ocaml_AEAD_decrypt(value state, value iv, value ad, value cipher) {
        CAMLparam4(state, iv, ad, cipher);

        ST* st = ST_val(state);
        AEAD_ST *ast = st->st;
        ID id = st->id;
        uint8_t* civ = (uint8_t*) String_val(iv);
        FStar_UInt128_t n = Crypto_Symmetric_Bytes_load_uint128((uint32_t)caml_string_length(iv), civ);
        uint8_t* cad = (uint8_t*) String_val(ad);
        uint32_t adlen = caml_string_length(ad);
        uint8_t* ccipher = (uint8_t*) String_val(cipher);
        uint32_t cipherlen = caml_string_length(cipher);
        if(cipherlen < Crypto_Symmetric_MAC_taglen)
	     	CAMLreturn(Val_none);

        CAMLlocal1(plain);
        uint32_t plainlen = cipherlen - Crypto_Symmetric_MAC_taglen;
        plain = caml_alloc_string(plainlen);
        uint8_t* cplain = (uint8_t*) String_val(plain);
        
        if(Crypto_AEAD_Decrypt_decrypt(id, *ast, n, adlen, cad, plainlen, cplain, ccipher))
        {
                CAMLreturn(Val_some(plain));
        }

	CAMLreturn(Val_none);
}

