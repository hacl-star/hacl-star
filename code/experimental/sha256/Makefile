HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin



extract:
	mkdir -p sha2-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin \
		Hacl.Hash.SHA2.L256.fst Hacl.Test.Hash.SHA2.fst -o sha2.exe -no-prefix Hacl.Test.Hash.SHA2 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar Hacl.Test.Hash.SHA2.fst \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -march=native -ccopt -std=gnu99 -verbose
	./sha2.exe

recompile: compile-sha2 compile-test compile-exe

compile-sha2:
	gcc-6 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_LIB/hyperstack -I /opt/hacl-star/code/lib/kremlin -I /opt/kremlin/kremlib -I sha2-c -march=native -std=gnu99 -c sha2-c/Hacl_Hash_SHA2_L256.c -o sha2-c/Hacl_Hash_SHA2_L256.o

compile-test:
	gcc-6 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_LIB/hyperstack -I /opt/hacl-star/code/lib/kremlin -I /opt/kremlin/kremlib -I sha2-c -march=native -std=gnu99 -c sha2-c/Hacl_Test_Hash_SHA2.c -o sha2-c/Hacl_Test_Hash_SHA2.o

compile-exe:
	gcc-6 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_LIB/hyperstack -I /opt/hacl-star/code/lib/kremlin -I /opt/kremlin/kremlib -I sha2-c -march=native -std=gnu99 sha2-c/Hacl_Hash_Utils.o sha2-c/Hacl_Hash_SHA2_L256.o sha2-c/Hacl_Test_Hash_SHA2.o sha2-c/kremlib.o sha2-c/testlib.o -o sha2.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c
