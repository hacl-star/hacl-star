/* Adapted 2014 by Lennart Beringer from OpenSSL091c crypto/hmac/hmac.c
 * Copyright (c) 2004 The OpenSSL Project.  All rights reserved
 * according to the OpenSSL license.

 * Specializes openssl's file to use the hash function sha256, avoiding
 * use of "object-oriented" programming style (engines etc) used in
 * recent versions of openssl.
 */

/* crypto/hmac/hmac.c */
/* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
 * All rights reserved.
 *
 * This package is an SSL implementation written
 * by Eric Young (eay@cryptsoft.com).
 * The implementation was written so as to conform with Netscapes SSL.
 *
 * This library is free for commercial and non-commercial use as long as
 * the following conditions are aheared to.  The following conditions
 * apply to all code found in this distribution, be it the RC4, RSA,
 * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
 * included with this distribution is covered by the same copyright terms
 * except that the holder is Tim Hudson (tjh@cryptsoft.com).
 *
 * Copyright remains Eric Young's, and as such any Copyright notices in
 * the code are not to be removed.
 * If this package is used in a product, Eric Young should be given attribution
 * as the author of the parts of the library used.
 * This can be in the form of a textual message at program startup or
 * in documentation (online or textual) provided with the package.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.]
 */

#include "sha.h"

/****From hmac.h, and specialized to use of sha256 *************/
#define HMAC_MAX_MD_CBLOCK	64 //i.e. SHA256_BLOCK_SIZE

typedef struct hmac_ctx_st
	{
	  //	EVP_MD *md; We fix this to be sha256

        SHA256_CTX md_ctx; //SHA structure for current hmac application -
         //is used for calculation of "short key", and later holds the
         //inner sha structure, to avoid overwriting i_ctx
        //unsigned char md_ctx[32]; holds short-key

        SHA256_CTX i_ctx; //the SHA structure for the inner sha application
        //unsigned char i_ctx[HMAC_MAX_MD_CBLOCK];

	SHA256_CTX o_ctx; //the SHA structure for the outer sha application
        //unsigned char o_ctx[HMAC_MAX_MD_CBLOCK];

	//unsigned int key_length;
	//unsigned char key[HMAC_MAX_MD_CBLOCK];
	} HMAC_CTX;

/***************************************************************/

void HMAC_Init(HMAC_CTX *ctx, unsigned char *key, int len)
     //final parameter fixed to SHA256, so omitted EVP_MD *md;
{
     int i,j,reset=0;
     unsigned char pad[HMAC_MAX_MD_CBLOCK];

     unsigned char aux; //temporary, for the initialization loops

     //unsigned int ctx_key_length;
     unsigned char ctx_key[HMAC_MAX_MD_CBLOCK];


  /*
  if (md != NULL)
  {
  reset=1;
  ctx->md=md;
  }
  else
  md=ctx->md;
  */	

     if (key != NULL)
       {
         reset=1;
         //j=EVP_MD_block_size(md);
         j= HMAC_MAX_MD_CBLOCK;
      	 if (j < len)
	   { //apply sha to key get a 32byte-key, then pad to 64
	     //EVP_DigestInit(&ctx->md_ctx,md);
	     //EVP_DigestUpdate(&ctx->md_ctx,key,len);
	     //EVP_DigestFinal(&(ctx->md_ctx),ctx->key, &ctx->key_length);

	     SHA256_Init(&ctx->md_ctx);
	     SHA256_Update(&ctx->md_ctx,key,len);
	     SHA256_Final(ctx_key,&(ctx->md_ctx));
	     memset(&(ctx_key[32]),0,32);
	     //ctx_key_length=32; //in analogy to what's 6 lines below
	   }
	 else
	   {
	     memcpy(ctx_key,key,len);
	     memset(&(ctx_key[len]),0,sizeof(ctx_key)-len);
	     //ctx_key_length=len;
           }
       }

     if (reset)	
       {
	 for (i=0; i<HMAC_MAX_MD_CBLOCK; i++) {
           aux = ctx_key[i];
	   aux = 0x36^aux;
           pad[i]=aux;
         }

         //Initialize inner SHA structure, and hash ipad
	 //EVP_DigestInit(&ctx->i_ctx,md);
	 //EVP_DigestUpdate(&ctx->i_ctx,pad,EVP_MD_block_size(md));
	 SHA256_Init(&ctx->i_ctx);
	 SHA256_Update(&ctx->i_ctx,pad,HMAC_MAX_MD_CBLOCK);
	
	
	 for (i=0; i<HMAC_MAX_MD_CBLOCK; i++) {
           aux = ctx_key[i];
	   pad[i]=0x5c^aux;
         }

         //Initialize outer SHA structure, and hash opad
	 //EVP_DigestInit(&ctx->o_ctx,md);
	 //EVP_DigestUpdate(&ctx->o_ctx,pad,EVP_MD_block_size(md));
	 SHA256_Init(&ctx->o_ctx);
	 SHA256_Update(&ctx->o_ctx,pad,HMAC_MAX_MD_CBLOCK);
       }

     //copy inner sha structure to "current" sha structure
     memcpy(&ctx->md_ctx,&ctx->i_ctx,sizeof(ctx->i_ctx));
}

//Changed to match type of sha256update
//void HMAC_Update(HMAC_CTX *ctx, unsigned char *data, int len)
void HMAC_Update(HMAC_CTX *ctx, const void *data, size_t len)
{
  SHA256_Update(&(ctx->md_ctx),data,len);
}

void HMAC_Final(HMAC_CTX *ctx, unsigned char *md)
   //final parameter will return length of hmac-code - but its always 32,
   //so  let's omit it for now, unsigned int *len)
{
  //int j; variable seems essentially dead even in openssl???
  //unsigned int i; not used, since we know the length of sha256 digests
  //unsigned char buf[EVP_MAX_MD_SIZE];
  unsigned char buf[SHA256_DIGEST_LENGTH]; //ie 32

  //j=EVP_MD_block_size(ctx->md); even openssl never reads from j -

  //Finish the inner sha, and store it in buf
  //EVP_DigestFinal(&(ctx->md_ctx),buf,&i);
  SHA256_Final(buf,&(ctx->md_ctx));

  //now make opad the "current" sha context
  memcpy(&(ctx->md_ctx),&(ctx->o_ctx),sizeof(ctx->o_ctx));

  //hash buf (ie result of inner sha) onto opad
  //EVP_DigestUpdate(&(ctx->md_ctx),buf,i);
  SHA256_Update(&(ctx->md_ctx),buf,SHA256_DIGEST_LENGTH);

  //finish outer sha, and return result
  //EVP_DigestFinal(&(ctx->md_ctx),md,len);
  SHA256_Final(md,&(ctx->md_ctx));
}

void HMAC_cleanup(HMAC_CTX *ctx)
{
  memset(ctx,0,sizeof(HMAC_CTX));
}

unsigned char *HMAC(//fixed to SHA256: EVP_MD *evp_md,
                    unsigned char *key, int key_len,
                    unsigned char *d, int n,
                    unsigned char *md)
                    //always 32, unsigned int *md_len)
	{
	HMAC_CTX c;
	//static unsigned char m[EVP_MAX_MD_SIZE];
	static unsigned char m[SHA256_DIGEST_LENGTH];

	if (md == NULL) md=m;

	//HMAC_Init(&c,key,key_len,evp_md);
        HMAC_Init(&c, key, key_len);

	HMAC_Update(&c,d,n);
	HMAC_Final(&c,md); //always 32:,md_len);
	HMAC_cleanup(&c);
	return(md);
	}

unsigned char *HMAC2(//fixed to SHA256: EVP_MD *evp_md,
                    unsigned char *key, int key_len,
                    unsigned char *d, int n,
                    unsigned char *md)
                    //always 64, unsigned int *md_len)
	{
	HMAC_CTX c;
	//static unsigned char m[EVP_MAX_MD_SIZE];
	static unsigned char m[2*SHA256_DIGEST_LENGTH];

	if (md == NULL) md=m;

	//first round
        HMAC_Init(&c, key, key_len);
	HMAC_Update(&c,d,n);
	HMAC_Final(&c,md);

	//second round
        HMAC_Init(&c, NULL, key_len); //only performs memcpy
	HMAC_Update(&c,d,n);
	HMAC_Final(&c,md+SHA256_DIGEST_LENGTH);
	HMAC_cleanup(&c);
	return(md);
	}

