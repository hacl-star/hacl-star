.PHONY: all spec code

all: spec code

spec:
	$(MAKE) -C spec VARIANT=64-cSHAKE
	$(MAKE) -C spec VARIANT=64-AES
	$(MAKE) -C spec VARIANT=640-cSHAKE
	$(MAKE) -C spec VARIANT=640-AES
	$(MAKE) -C spec VARIANT=976-cSHAKE
	$(MAKE) -C spec VARIANT=976-AES

code:
# ====================================================================
# Test 64-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=64-cSHAKE
# ====================================================================
# Reference 640-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET= lib
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET= benchmark KATs
	$(MAKE) -C NIST/Reference_Implementation/reference/FrodoKEM-640 tests
	NIST/Reference_Implementation/reference/FrodoKEM-640/frodo/test_KEM
# ====================================================================
# Optimized x64 640-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET=x64 lib
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET=x64 benchmark KATs
	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-640 tests
	NIST/Additional_Implementations/x64/FrodoKEM-640/frodo/test_KEM
# ====================================================================
# Optimized x64 640-AES
# ====================================================================
	$(MAKE) -C code VARIANT=640-AES TARGET=x64 lib
	$(MAKE) -C code VARIANT=640-AES TARGET=x64 benchmark KATs
	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-640 GENERATION_A=AES128 tests
	NIST/Additional_Implementations/x64/FrodoKEM-640/frodo/test_KEM
# ====================================================================
# Reference 976-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=976-cSHAKE TARGET= lib
	$(MAKE) -C code VARIANT=976-cSHAKE TARGET= benchmark KATs
	$(MAKE) -C NIST/Reference_Implementation/reference/FrodoKEM-976 tests
	NIST/Reference_Implementation/reference/FrodoKEM-976/frodo/test_KEM
# ====================================================================
# Optimized x64 976-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=x64 lib
	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=x64 benchmark KATs
	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-976 tests
	NIST/Additional_Implementations/x64/FrodoKEM-976/frodo/test_KEM
# ====================================================================
# Optimized x64 976-AES
# ====================================================================
	$(MAKE) -C code VARIANT=976-AES TARGET=x64 lib
	$(MAKE) -C code VARIANT=976-AES TARGET=x64 benchmark KATs
	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-976 GENERATION_A=AES128 tests
	NIST/Additional_Implementations/x64/FrodoKEM-976/frodo/test_KEM
