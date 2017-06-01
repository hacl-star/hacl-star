all: Chacha20.result

Chacha20.result:
	z3 -smt2 Chacha20.smt | tee  Chacha20.result | grep -B1 sat

clean:
	rm -f *~ *.result

