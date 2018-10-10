all:
	$(MAKE) -C spec VARIANT=64-cSHAKE
#	$(MAKE) -C spec VARIANT=640-cSHAKE
#	$(MAKE) -C spec VARIANT=976-cSHAKE
# ====================================================================
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET= lib
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET= benchmark KATs
	$(MAKE) -C NIST/Reference_Implementation/reference/FrodoKEM-640 tests
	NIST/Reference_Implementation/reference/FrodoKEM-640/frodo/test_KEM
# ====================================================================
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET=x64 lib
	$(MAKE) -C code VARIANT=640-cSHAKE TARGET=x64 benchmark KATs
	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-640 tests
	NIST/Additional_Implementations/x64/FrodoKEM-640/frodo/test_KEM
# ====================================================================
#	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=    lib
#	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=    benchmark KATs
#	$(MAKE) -C NIST/Reference_Implementation/reference/FrodoKEM-976 tests
#	NIST/Reference_Implementation/reference/FrodoKEM-976/frodo/test_KEM
# ====================================================================
#	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=x64 lib
#	$(MAKE) -C code VARIANT=976-cSHAKE TARGET=x64 benchmark KATs
#	$(MAKE) -C NIST/Additional_Implementations/x64/FrodoKEM-976 tests
#	NIST/Additional_Implementations/x64/FrodoKEM-976/frodo/test_KEM
