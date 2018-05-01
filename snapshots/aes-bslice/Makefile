
CC ?= gcc-7
all: aes_test.exe tiny_aes_test.exe aes_bslice_test.exe aes_ni_test.exe aes_bslice4_test.exe aes_bslice8_test.exe

aes_test.exe: aes.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native aes.c aes_test.c -o aes_test.exe
	./aes_test.exe

tiny_aes_test.exe: tiny-aes.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native tiny-aes.c aes_test.c -o tiny_aes_test.exe
	./tiny_aes_test.exe

aes_ni_test.exe: aes_ni.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native -maes aes_ni.c aes_test.c -o aes_ni_test.exe
	./aes_ni_test.exe

aes_bslice_test.exe: aes_bslice.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native aes_bslice.c aes_test.c -o aes_bslice_test.exe
	./aes_bslice_test.exe

aes_bslice4_test.exe: aes_bslice4.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native aes_bslice4.c aes_test.c -o aes_bslice4_test.exe
	./aes_bslice4_test.exe

aes_bslice8_test.exe: aes_bslice8.c aes_test.c
	$(CC) -O3 -Wall -Wextra -march=native -mtune=native aes_bslice8.c aes_test.c -o aes_bslice8_test.exe
	./aes_bslice8_test.exe

clean:
	rm -f *.exe
