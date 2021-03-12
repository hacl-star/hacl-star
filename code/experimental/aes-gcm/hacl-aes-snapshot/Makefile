all: test

aes256gcm-ni.exe: Hacl_AES_256_GCM_NI.c aes256gcm-ni-test.c
	$(CC) -maes -march=native -mtune=native -O3 $^ -o aes256gcm-ni.exe

aes256gcm-bitslice.exe: Hacl_AES_256_GCM_M32.c aes256gcm-bitslice-test.c
	$(CC) -march=native -mtune=native -O3 $^ -o aes256gcm-bitslice.exe

test: aes256gcm-ni.exe aes256gcm-bitslice.exe
	./aes256gcm-ni.exe
	./aes256gcm-bitslice.exe

clean:
	rm -f *.exe
