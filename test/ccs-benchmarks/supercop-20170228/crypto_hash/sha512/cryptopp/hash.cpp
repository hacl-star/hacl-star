#include <cryptopp/sha.h>
#include "crypto_hash.h"

int crypto_hash(unsigned char *out,const unsigned char *in,unsigned long long inlen)
{
	CryptoPP::SHA512 sha;
	sha.CalculateDigest(out, in, inlen);
	return 0;
}
