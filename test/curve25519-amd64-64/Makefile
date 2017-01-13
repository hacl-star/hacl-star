all:
	gcc-6 -Ofast -march=native -mtune=native -m64 -funroll-loops -fomit-frame-pointer *.s fe*.c  mont25519.c test.c -o test.exe
	./test.exe