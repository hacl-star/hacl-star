FSTAR_HOME?=../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME=../..

#include ../lib/hyperstack/Makefile.include

KRML=$(KREMLIN_HOME)/krml -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/api \
	-I $(HACL_HOME)/code/curve25519 -I $(HACL_HOME)/specs -I $(HACL_HOME)/snapshots/hacl-c \
	-drop 'Prims' -drop 'Hacl.Constants' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' \
	-drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' -drop 'FStar' -drop 'Hacl.Cast' \
	-ccopt '-Wno-pointer-sign' -ccopt "-D_GNU_SOURCE"

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/api \
	--include $(HACL_HOME)/code/curve25519 --include $(HACL_HOME)/snapshots/hacl-c \
	--include c_bindings --include $(KREMLIN_HOME)/kremlib


debug:
	gcc-6 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_LIB/hyperstack -I ../../code/lib/kremlin -I ../../code/api -I ../../code/curve25519 -I ../../snapshots/hacl-c -I c_bindings -I /home/jkz/dev/kremlin/kremlib -I tube -Wno-pointer-sign tube/Hacl_Types.o tube/Hacl_Policies.o tube/Box_Ideal.o tube/FileIO_Types.o tube/PaddedFileIO.c tube/SocketIO.c tube/Hacl_Tube_Send.c tube/Hacl_Tube_Receive.c tube/kremlib.o tube/tube.o tube/SocketIO_impl.o -D_GNU_SOURCE c_bindings/PaddedFileIO_impl.c -o tube-star.exe -lsodium -lhacl -L../../snapshots/hacl-c/

../../snapshots/hacl-c/libhacl.so:
	$(MAKE) -C $(HACL_HOME)/snapshots libhacl

tube-star.exe: Box.Ideal.fst c_bindings/PaddedFileIO_impl.c c_bindings/SocketIO_impl.c Hacl.Tube.Send.fst Hacl.Tube.Receive.fst tube.c $(HACL_HOME)/snapshots/hacl-c/libhacl.so
	mkdir -p tube
	$(KRML) $(filter %.c %.fst, $^) \
		-I c_bindings \
		-drop Libsodium,Curve25519,Hacl.Types,NaCl,Spec.\* \
		-bundle "Hacl.Tube.Send=Hacl.Tube.Send" \
		-no-prefix Libsodium -add-include '<sodium.h>' -add-include '"testlib.h"' \
		-add-include '"NaCl.h"' -add-include '"Curve25519.h"' \
		-tmpdir tube -o tube-star.exe -ldopt "-lsodium" -ldopt "-lhacl" -ldopt "-L../../snapshots/hacl-c/"

tube-lax: Hacl.Tube.Receive.fst Hacl.Tube.Send.fst
	$(FSTARB) --lax $^

tube-ver: $(addsuffix -ver, Hacl.Tube.Send.fst Hacl.Tube.Receive.fst)

tube-test: tube-star.exe
	mkdir -p send receive
	cd receive && \
		LD_LIBRARY_PATH=../../../snapshots/hacl-c:"$(LD_LIBRARY_PATH)" \
		DYLD_LIBRARY_PATH=../../../snapshots/hacl-c:"$(DYLD_LIBRARY_PATH)" \
		../tube-star.exe receive 5001 \
			-k dfcf8b782a2a72f65ee24f85fa68ab1a10b3b555751283c5f0bcdb20e1a6e4a8 \
			-p 4d187de7a95fe760ba7ffc9a1ba4229eea9cd1136fe609bdc58816e3cf4d3350 &
	cd send && echo "banana" > banana.txt; \
		LD_LIBRARY_PATH=../../../snapshots/hacl-c:"$(LD_LIBRARY_PATH)" \
		DYLD_LIBRARY_PATH=../../../snapshots/hacl-c:"$(DYLD_LIBRARY_PATH)" \
		../tube-star.exe send banana.txt localhost:5001 \
			-k 4d922658eb6d4aef64a83644a18e60e61a57c245aa8e5e9a93926cb2b317ffd7 \
			-p 223fc224f2c9906fd4bbb1313236ecc4f36ed2f7e95b5fb1deafc459b19ab069
#	@lsof -i tcp:5001 | awk 'NR!=1 {print $$2}' | xargs kill
#	@rm -r send receive


%.fst-ver: %.fst 
	$(FSTARB) $^ --use_hints --record_hints


# send-ver: Hacl.Tube.Send.fst
# 	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api --use_hints \
# 		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

# send-lax: Hacl.Tube.Send.fst
# 	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api -fstop "--lax" \
# 		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

# receive-ver: Hacl.Tube.Receive.fst
# 	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api --use_hints  \
# 		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^

# receive-lax: Hacl.Tube.Receive.fst
# 	$(FSTAR) -I $(HACL_KREMLIN) -I ../lib/io -I ../lib/io/c_bindings -I ../crypto/api -fsopt "--lax" \
# 		-I $(KREMLIB) -I $(KREMTEST) -I $(FSTAR_HOME)/ulib/hyperstack $^ 


clean:
	rm -rf tube send receive
	rm -rf *~ *.exe *.dSYM
