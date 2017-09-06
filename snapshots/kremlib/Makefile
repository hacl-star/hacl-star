.PHONY: nacllib clean

#
# Compilation flags
#
CCOPTS = -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops
CCOPTS32 = -Ofast -mtune=generic -m32 -fwrapv -fomit-frame-pointer -funroll-loops

ifeq ($(SNAPSHOT_DIR),snapshots/hacl-c-compcert)
  LIBFLAGS=$(CCOPTS) $(CFLAGS)
  LIBFLAGS32=$(CCOPTS32) $(CFLAGS)
  OTHER=FStar.c -shared
else
  LIBFLAGS=$(CCOPTS) -fPIC -Wno-discarded-qualifiers
  LIBFLAGS32=$(CCOPTS32) -fPIC -Wno-discarded-qualifiers -DKRML_NOUINT128 -Wno-unused-function
  OTHER=-shared
endif

#
# Files
#

FILES = Salsa20.c Salsa20.h Chacha20.c Chacha20.h Poly1305_64.c Poly1305_64.h AEAD_Poly1305_64.c AEAD_Poly1305_64.h SHA2_512.c SHA2_512.h Ed25519.c Ed25519.h Curve25519.c Curve25519.h Chacha20Poly1305.c Chacha20Poly1305.h Hacl_Policies.c Hacl_Policies.h NaCl.c NaCl.h
TWEETNACL_HOME ?= $(HACL_HOME)/other_providers/tweetnacl

#
# Library (64 bits)
#

libhacl.so: $(FILES)
	$(CC) $(LIBFLAGS) \
	  Salsa20.c -c -o Salsa20.o
	$(CC) $(LIBFLAGS) \
	  Chacha20.c -c -o Chacha20.o
	$(CC) $(LIBFLAGS) \
	  Poly1305_64.c -c -o Poly1305_64.o
	$(CC) $(LIBFLAGS) \
	  AEAD_Poly1305_64.c -c -o AEAD_Poly1305_64.o
	$(CC) $(LIBFLAGS) \
	  SHA2_512.c -c -o SHA2_512.o
	$(CC) $(LIBFLAGS) \
	  Ed25519.c -c -o Ed25519.o
	$(CC) $(LIBFLAGS) \
	  Curve25519.c -c -o Curve25519.o
	$(CC) $(LIBFLAGS) \
	  Chacha20Poly1305.c -c -o Chacha20Poly1305.o
	$(CC) $(OTHER) $(LIBFLAGS) -I ../../test/test-files -I . -Wall \
	  ../../test/test-files/hacl_test_utils.c \
	  Salsa20.o Poly1305_64.o Chacha20.o AEAD_Poly1305_64.o Chacha20Poly1305.o SHA2_512.o Ed25519.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c ../../test/test-files/randombytes.c ../../test/test-files/haclnacl.c \
	  -o libhacl.so

#
# Library (32 bits)
#

libhacl32.so: $(FILES)
	$(CC) $(LIBFLAGS32) \
	  Salsa20.c -c -o Salsa20.o
	$(CC) $(LIBFLAGS32) \
	  Chacha20.c -c -o Chacha20.o
	$(CC) $(LIBFLAGS32) \
	  Poly1305_64.c -c -o Poly1305_64.o
	$(CC) $(LIBFLAGS32) \
	  AEAD_Poly1305_64.c -c -o AEAD_Poly1305_64.o
	$(CC) $(LIBFLAGS32) \
	  SHA2_512.c -c -o SHA2_512.o
	$(CC) $(LIBFLAGS32) \
	  Ed25519.c -c -o Ed25519.o
	$(CC) $(LIBFLAGS32) \
	  Curve25519.c -c -o Curve25519.o
	$(CC) $(LIBFLAGS32) \
	  Chacha20Poly1305.c -c -o Chacha20Poly1305.o
	$(CC) -shared  $(LIBFLAGS32) -I ../../test/test-files -I . -Wall \
	  ../../test/test-files/hacl_test_utils.c \
	  Salsa20.o Poly1305_64.o Chacha20.o AEAD_Poly1305_64.o Chacha20Poly1305.o SHA2_512.o Ed25519.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c ../../test/test-files/randombytes.c ../../test/test-files/haclnacl.c \
	  -o libhacl32.so

unit-tests: libhacl.so
	$(CC) $(CCOPTS) \
	-I . -I ../snapshots/kremlib -I ../../test/test-files/ -I $(TWEETNACL_HOME) \
	$(TWEETNACL_HOME)/tweetnacl.c ../../test/test-files/hacl_test_utils.c \
	../../test/test-files/unit_tests.c libhacl.so -o unit_tests.exe
	./unit_tests.exe

unit-tests32: libhacl32.so 
	$(CC) $(CCOPTS32) \
	-I . -I ../snapshots/kremlib -I ../../test/test-files/ -I $(TWEETNACL_HOME) \
	$(TWEETNACL_HOME)/tweetnacl.c ../../test/test-files/hacl_test_utils.c \
	../../test/test-files/unit_tests.c libhacl32.so -o unit_tests32.exe
	./unit_tests32.exe

clean:
	rm -rf *~ *.exe *.out *.o *.txt *.so
