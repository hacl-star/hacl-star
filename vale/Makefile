JOBS=$(shell echo $(MAKEFLAGS) | grep -o '\(^\| \)-j[0-9]*')

all:
	./run_scons.sh $(JOBS) --FSTAR-MY-VERSION

clean:
	./run_scons.sh --clean

.PHONY: all clean
