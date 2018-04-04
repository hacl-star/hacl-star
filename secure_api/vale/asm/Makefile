# All the Vale files we need to bring into this directory for the compilation of
# our wrappers to be standalone; note that HACL*'s CI does NOT bring Vale into
# the picture, so this directory should compile WITHOUT
# -I$(VALE_HOME)/obj/crypto/hashing
VALE_OBJ_FILES=sha256_main_i.c sha256_main_i.h
VALE_UTIL_FILES=DafnyLib.h

.PHONY: import
import:
	@if [ x"$(VALE_HOME)" = x ]; then echo "VALE_HOME not defined"; exit 1; fi
	cp $(VALE_HOME)/obj/aes-gcc.S aes-x86_64.S
	cp $(VALE_HOME)/obj/sha256-gcc.S sha256-x86_64.S
	cp $(VALE_HOME)/obj/aes-macos.S aes-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/sha256-macos.S sha256-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/aes-linux.S aes-x86_64-Linux.S
	cp $(VALE_HOME)/obj/sha256-linux.S sha256-x86_64-Linux.S
	$(SED) -i 's/.section .text/.text/' *.S
	for f in $(VALE_OBJ_FILES); do cp $(VALE_HOME)/obj/crypto/hashing/$$f .; done
	for f in $(VALE_UTIL_FILES); do cp $(VALE_HOME)/src/lib/util/$$f .; done

clean:
	rm -f *.a *.o *~
