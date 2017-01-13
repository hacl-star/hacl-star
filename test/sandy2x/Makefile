all:
	gcc-6 -Ofast -march=native -mtune=native -m64 -funroll-loops -fomit-frame-pointer *.S fe*.c scalarmult.c test.c -o test.exe
	./test.exe