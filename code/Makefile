all: extract-c verify 

verify:
	make -C salsa-family verify
	make -C bignum verify
	make -C poly1305 verify
	make -C curve25519 verify

extract-c:
	make -C salsa-family extract-c
	make -C poly1305 extract-c
	make -C curve25519 extract-c

clean:
	rm -rf *~ *.exe *.out 
	make -C salsa-family clean
	make -C bignum clean
	make -C poly1305 clean
	make -C curve25519 clean
