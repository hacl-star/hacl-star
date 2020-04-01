#include "kremlin/internal/types.h"
#include "kremlin/lowstar_endianness.h"
#include <string.h>
#include "lib_intrinsics.h"

#include "Hacl_Kremlib.h"
#include "Hacl_Blake2b_32.h"
#include "Hacl_Spec.h"
#include "Hacl_ECDSA.h"


bool compare_and_print(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  LowStar_Printf_print_string("Expected: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b1);
  LowStar_Printf_print_string("\n");
  LowStar_Printf_print_string("Computed: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b2);
  LowStar_Printf_print_string("\n");
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(b1[i], b2[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool b = z == (uint8_t)255U;
  if (b)
  {
    LowStar_Printf_print_string("PASS\n");
  }
  else
  {
    LowStar_Printf_print_string("FAIL\n");
  }
  return b;
}



uint8_t privateKey0[32U] = {
	0xD6, 0x3F, 0xF7, 0xD5, 0xD8, 0xFB, 0x73, 0x34,
	0x28, 0x7C, 0xB3, 0x97, 0xF8, 0x24, 0xB3, 0x56,
	0x71, 0x78, 0xBB, 0x63, 0x5C, 0xD2, 0xFA, 0xA8,
	0xA3, 0x4D, 0x0B, 0x1B, 0xC6, 0x5F, 0xDA, 0xF2};


uint8_t privateKey1[32U] = {
	0x9D,  0x58,  0x51,  0x60,  0xC3,  0xAD,  0x17,  0x1D,  0x7F,  0x49,  0x25,  0xF3,  0x59,  0xC2,  0xB4,  0xC8,  0x99,  0x27,  0x30,  0xDB,  0xAE,  0xE4,  0xD4,  0xD1,  0x0B,  0x1E,  0x0E,  0x48,  0x9C,  0xCA,  0x34,  0x04};

uint8_t privateKey2[32U] = {
	0x62,  0xFA,  0xA0,  0x69,  0xEE,  0x72,  0x86,  0xD0,  0x27,  0x74,  0x76,  0x56,  0xEC,  0x73,  0x6F,  0x29,  0xD2,  0x0E,  0x5B,  0xF8,  0x27,  0xF1,  0xD5,  0x31,  0xB1,  0xA9,  0xDE,  0x21,  0x5A,  0xF8,  0x76,  0xF3
};

uint8_t privateKey3[32U] = {
	0x2F,  0xE2,  0x1C,  0x08,  0x1F,  0xFA,  0x7C,  0xBD,  0x63,  0x1E,  0x6F,  0x20,  0xB0,  0x5B,  0x87,  0x0D,  0x64,  0xA2,  0x52,  0xA3,  0xB7,  0xE1,  0xA1,  0x25,  0xC3,  0xD0,  0x7E,  0x7B,  0x6B,  0xBF,  0xF4,  0x1B
};

uint8_t privateKey4[32U] = {
	0xBC,  0x8C,  0xB5,  0xB0,  0x5C,  0x30,  0x6B,  0x55,  0x61,  0xCC,  0xBA,  0xAF,  0xE3,  0x77,  0x7C,  0x26,  0x7A,  0x8C,  0xDE,  0xFA,  0x6D,  0x00,  0xB5,  0xCE,  0x2E,  0x65,  0x57,  0x8D,  0xEA,  0x03,  0x0F,  0x3C
};



uint8_t encodedPublicKey0 [33U] = {
	0x02,  0xCA,  0x53,  0x64,  0xC4,  0x30,  0x2C,  0x38,  0xE9,  0x3F,  0x8A,  0x48,  0x50,  0xE6,  0x1A,  0x8F,  0xE6,  0xC2,  0x7E,  0x38,  0x6D,  0x45,  0x41,  0xB8,  0x98,  0xF4,  0xE7,  0x4B,  0xE5,  0xE6,  0xDD,  0x02,  0x56

};

uint8_t encodedPublicKey1 [33U] = {
	0x03,  0xD6,  0x00,  0x8C,  0x2A,  0x65,  0x6D,  0xD4,  0x14,  0xC6,  0x86,  0x95,  0x58,  0xA1,  0xE2,  0x62,  0xF3,  0x8B,  0xD5,  0xA1,  0x42,  0x03,  0x9F,  0xE8,  0x4E,  0x75,  0x03,  0x35,  0xC5,  0x43,  0xB3,  0x76,  0xB9
};

uint8_t encodedPublicKey2 [33U] = {
	0x03,  0x81,  0x24,  0x47,  0xC0,  0x00,  0x50,  0xCA,  0x92,  0x1B,  0x05,  0xA6,  0x09,  0x7C,  0x3F,  0x29,  0xF4,  0xAD,  0xFF,  0x23,  0xC4,  0xDD,  0x60,  0x62,  0xCB,  0xB1,  0x14,  0xDD,  0x5B,  0x91,  0x7D,  0x19,  0x95
};

uint8_t encodedPublicKey3 [33U] = {
	0x03,  0xBB,  0xF4,  0xA1,  0xB5,  0xDF,  0x7E,  0x66,  0xE1,  0xFF,  0xC6,  0x7A,  0xD2,  0x77,  0x8F,  0x5E,  0x3A,  0x78,  0x71,  0x70,  0x27,  0xFE,  0xBF,  0xB9,  0x40,  0xC0,  0xC3,  0xCF,  0xC7,  0x3F,  0x05,  0x25,  0x83
};


uint8_t encodedPublicKey4 [33U] = {
	0x02,  0x76,  0x28,  0x5E,  0xE2,  0x39,  0x63,  0x1F,  0x90,  0x44,  0x01,  0xC2,  0xC2,  0xA2,  0x2C,  0xEF,  0xDF,  0x75,  0x90,  0x54,  0x6E,  0xD3,  0xAA,  0x4E,  0x2B,  0x27,  0x59,  0xF1,  0x6D,  0xD7,  0x70,  0x9D,  0x6B
};



void test0 ()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey0, tempBuffer);
	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	compare_and_print(compressed, encodedPublicKey0, 33);

}

void test1 ()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey1, tempBuffer);
	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	compare_and_print(compressed, encodedPublicKey1, 33);

}

void test2 ()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey2, tempBuffer);
	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	compare_and_print(compressed, encodedPublicKey2, 33);

}


void test3 ()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey3, tempBuffer);
	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	compare_and_print(compressed, encodedPublicKey3, 33);

}

void test4 ()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey4, tempBuffer);
	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	compare_and_print(compressed, encodedPublicKey4, 33);

}


void test5()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* compressed1 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey0, tempBuffer);

	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	Hacl_Impl_ECDSA_decompressionCompressedForm(compressed, compressed1);

	compare_and_print(compressed1, compressed0, 64);

}


void test6()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* compressed1 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey1, tempBuffer);

	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	Hacl_Impl_ECDSA_decompressionCompressedForm(compressed, compressed1);

	compare_and_print(compressed1, compressed0, 64);

}


void test7()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* compressed1 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey2, tempBuffer);

	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	Hacl_Impl_ECDSA_decompressionCompressedForm(compressed, compressed1);

	compare_and_print(compressed1, compressed0, 64);

}


void test8()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* compressed1 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey3, tempBuffer);

	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	Hacl_Impl_ECDSA_decompressionCompressedForm(compressed, compressed1);

	compare_and_print(compressed1, compressed0, 64);

}


void test9()
{
	uint64_t* tempBuffer = (uint64_t*) malloc (sizeof (uint64_t) * 100);
	uint8_t* compressed0 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	uint8_t* compressed = (uint8_t*) malloc (sizeof (uint8_t) * 32);
	uint8_t* compressed1 = (uint8_t*) malloc (sizeof (uint8_t) * 64);
	
	Hacl_Impl_ECDSA_secretToPublicU8(compressed0, privateKey4, tempBuffer);

	Hacl_Impl_ECDSA_compressionCompressedForm(compressed0, compressed);
	Hacl_Impl_ECDSA_decompressionCompressedForm(compressed, compressed1);

	compare_and_print(compressed1, compressed0, 64);

}



int main()
{
	printf("%s\n", "Key compression Testing");

	test0();
	test1();
	test2();
	test3();
	test4();

	printf("%s\n", "Key decompression Testing");

	test5();
	test6();
	test7();
	test8();
	test9();


	return 0;
}