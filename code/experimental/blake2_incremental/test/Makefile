all:
	$(CC) -c /opt/hacl-star/lib/c/Lib_PrintBuffer.c -I/opt/hacl-star/lib
	$(CC) -c /opt/hacl-star/lib/c/Lib_RandomBuffer_System.c -I/opt/hacl-star/lib
	$(CC) -c blake2s-ref.c -I/opt/hacl-star/code/experimental/blake2_incremental/
	$(CC) -c blake2b-ref.c -I/opt/hacl-star/code/experimental/blake2_incremental/
	$(CC) -c /opt/hacl-star/code/blake2/blake2-c/Hacl_Blake2s.c -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2/blake2-c -I/opt/kremlin/include -I/opt/kremlin/include/kremlin -Wno-shift-op-parentheses
	$(CC) -c /opt/hacl-star/code/blake2/blake2-c/Hacl_Blake2b.c -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2/blake2-c -I/opt/kremlin/include -I/opt/kremlin/include/kremlin -Wno-shift-op-parentheses
	$(CC) -c /opt/hacl-star/code/blake2/blake2-c/Hacl_Blake2_Constants.c -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2/blake2-c -I/opt/kremlin/include -I/opt/kremlin/include/kremlin
	$(CC) Lib_PrintBuffer.o Lib_RandomBuffer_System.o blake2s-ref.o blake2b-ref.o Hacl_Blake2_Constants.o Hacl_Blake2s.o Hacl_Blake2b.o C_Test_Blake2.c -lkremlib -o test.exe -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2/blake2-c -L/opt/kremlin/kremlib/dist/generic -I/opt/kremlin/include -I/opt/kremlin/include/kremlin
