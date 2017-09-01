.PHONY: nacllib clean

#
# Compilation flags
#

ifeq ($(SNAPSHOT_DIR),snapshots/snapshot-ccomp)
  LIBFLAGS=$(CCOPTS) $(CFLAGS)
  OTHER=FStar.c -shared
else
  LIBFLAGS=$(CFLAGS) -fPIC -Wno-discarded-qualifiers
  OTHER=-shared
endif
LIBFLAGS32=$(LIBFLAGS) -DKRML_NOUINT128 -Wno-unused-function

#
# Files
#

FILES = Salsa20.c Salsa20.h Chacha20.c Chacha20.h Poly1305_64.c Poly1305_64.h AEAD_Poly1305_64.c AEAD_Poly1305_64.h SHA2_512.c SHA2_512.h Ed25519.c Ed25519.h Curve25519.c Curve25519.h Chacha20Poly1305.c Chacha20Poly1305.h Hacl_Policies.c Hacl_Policies.h NaCl.c NaCl.h

#
# Library (64 bits)
#

libnacl.so: $(FILES)
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
	$(CC) $(OTHER) $(LIBFLAGS) -I ../../test/c -I . -Wall \
	  ../../test/c/hacl_test_utils.c \
	  Salsa20.o Poly1305_64.o Chacha20.o AEAD_Poly1305_64.o Chacha20Poly1305.o SHA2_512.o Ed25519.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c ../../test/c/randombytes.c ../../test/c/haclnacl.c \
	  -o libnacl.so

#
# Library (32 bits)
#

libnacl32.so: $(FILES)
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
	$(CC) -shared  $(LIBFLAGS32) -I ../../test/c -I . -Wall \
	  ../../test/c/hacl_test_utils.c \
	  Salsa20.o Poly1305_64.o Chacha20.o AEAD_Poly1305_64.o Chacha20Poly1305.o SHA2_512.o Ed25519.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c ../../test/c/randombytes.c ../../test/c/haclnacl.c \
	  -o libnacl32.so

clean:
	rm -rf *~ *.exe *.out *.o *.txt *.so
