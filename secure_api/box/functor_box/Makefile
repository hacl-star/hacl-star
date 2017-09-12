include ../../../code/Makefile.include

VERIFY= \
  Box.Index \
  Box.Plain \
	Box.AE \
  Box.ODH \
	Box.PKAE \
  Box.KDF \
  Box.Indexing
LAX=

FSTAR_INCLUDES+= \
  --include /home/markulf/everest/FStar/ucontrib/Platform/fst/ \
  --include /home/markulf/everest/FStar/ucontrib/CoreCrypto/fst/ \
  --include /home/markulf/everest/hacl-star/specs/ \
  --include /home/markulf/everest/hacl-star/specs/experimental/ \
  --include /home/markulf/everest/hacl-star/secure_api/utils/ \
  --include /home/markulf/everest/hacl-star/code/lib/ \
  --include /home/markulf/everest/kremlin/kremlib/


all: all-ver $(addsuffix .fst-lax, $(LAX))

verify: $(addsuffix .fst-verify, $(filter-out $(LAX), $(VERIFY)))
hints: $(addsuffix .fst.hints, $(VERIFY))
lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))R

all-ver: verify
all-hints: hints
all-lax: lax

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) $(INCLUDE) \
	$(basename $@).fst

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^
