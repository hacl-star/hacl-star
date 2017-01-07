.PHONY: test clean

test: test-poly	test-salsa test-curve

test-poly:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -l sodium -o test-poly.exe
	./test-poly.exe

test-salsa:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Salsa20.c test-salsa.c -l sodium -o test-salsa.exe
	./test-salsa.exe

test-curve:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Curve25519.c test-curve.c -l sodium -o test-curve.exe
	./test-curve.exe

test-nacl:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Hacl_Policies.c HSalsa20.c Salsa20.c Poly1305_64.c Curve25519.c NaCl.c test-nacl.c -l sodium -o test-nacl.exe
	./test-nacl.exe


clean:
	rm -rf *~ *.exe *.out 
