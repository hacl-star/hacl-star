HACL_HOME?=../..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin

.PHONY: snapshot

HAS_CL=$(shell which cl.exe >/dev/null 2>&1 && echo true || echo false)
HAS_CCOMP=$(shell which ccomp >/dev/null 2>&1 && echo true || echo false)

all:
	#$(MAKE) extract-c
	#if $(HAS_CCOMP); then $(MAKE) extract-c KREMLIN_ARGS="-cc compcert"; fi
	#if $(HAS_CL); then $(MAKE) extract-c KREMLIN_ARGS="-cc msvc"; fi
	#$(MAKE) ct
	#$(MAKE) verify
	$(MAKE) verify-crypto
	$(MAKE) -C openssl-engine

travis:
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) -C .. world

extract-c-code:
	$(MAKE) -C ../code extract-c

extract-c-crypto:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

extract-c: extract-c-code extract-c-crypto

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	# Note: the all-hints target fails silently.
	$(MAKE) -C ../secure_api all-ver OTHERFLAGS=--record_hints

hints-code:
	$(MAKE) -C ../code hints

hints-crypto:
	$(MAKE) -C ../secure_api all-hints

hints: hints-code hints-crypto

verify: verify-code verify-crypto

build-snapshot:
	mkdir -p snapshot
	cp $(addprefix ../code/poly1305/poly-c/, Poly1305_64.* AEAD_Poly1305_64.*) \
		../code/curve25519/x25519-c/Curve25519.* \
		../code/salsa-family/chacha-c/Chacha20.* \
		../code/salsa-family/salsa-c/Salsa20.* \
		$(addprefix ../code/api/aead-c/, Chacha20Poly1305.*) \
		$(addprefix ../code/api/box-c/, Hacl_Policies.* NaCl.*) \
		 snapshot
	cp ./c/* snapshot/

CCOMP=gcc-6 -flto -std=c11 -D_GNU_SOURCE

test-snapshot:
	$(MAKE) -C snapshot CC="$(CCOMP)" test

snapshot:
	$(MAKE) extract-c-code
	$(MAKE) build-snapshot
	$(MAKE) test-snapshot

update-snapshot:
	$(build-snapshot)
	$(MAKE) -C snapshot clean
	cp snapshot/*.c snapshot/*.h ../snapshots/hacl-c

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
	rm -rf snapshot *.o *.exe *~
