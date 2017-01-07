
test-poly:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -l sodium -o test-poly.exe
	./test-poly.exe

test-chacha:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Chacha20.c test-chacha.c -l sodium -o test-chacha.exe
	./test-chacha.exe

test-salsa:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Salsa20.c test-salsa.c -l sodium -o test-salsa.exe
	./test-salsa.exe

test-curve:
	gcc-6 -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Curve25519.c test-curve.c -l sodium -o test-curve.exe
	./test-curve.exe

clean:
	rm -rf *~ *.exe *.out 
