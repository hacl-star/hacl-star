all:
	$(CC) -c /opt/hacl-star/lib/c/Lib_PrintBuffer.c -I/opt/hacl-star/lib
	$(CC) -c /opt/hacl-star/lib/c/Lib_RandomBuffer_System.c -I/opt/hacl-star/lib
	$(CC) -c blake2b-ref.c -I/opt/hacl-star/code/blake2b/experimental/blake2b-c
	$(CC) -c Hacl_Blake2b.c -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2b/experimental/blake2b-c -L/opt/kremlin/kremlib/dist/generic -I/opt/kremlin/include -I/opt/kremlin/include/kremlin
	$(CC) Lib_PrintBuffer.o Lib_RandomBuffer_System.o blake2b-ref.o Hacl_Blake2b.o C_Test_Blake2b_Incremental.c -lkremlib -o test.exe -I/opt/hacl-star/lib -I/opt/hacl-star/code/blake2b/experimental/blake2b-c -L/opt/kremlin/kremlib/dist/generic -I/opt/kremlin/include -I/opt/kremlin/include/kremlin
