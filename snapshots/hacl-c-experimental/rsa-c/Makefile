.PHONY: nacllib clean

#
# Compilation flags
#
CCOPTS = -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops
CCOPTS32 = -Ofast -mtune=generic -m32 -fwrapv -fomit-frame-pointer -funroll-loops


all:
	gcc-7 $(CCOPTS) *.c -o test-rsa.exe
	./test-rsa.exe

clean:
	rm -rf *~ *.exe *.out *.o *.txt *.so
