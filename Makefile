VS := $(shell find . -type f -name '*v')
VERSIONS := logical tmonad
BINS := $(VERSIONS:%=%.bin)
MLS := $(VERSIONS:%=%.ml)
MLIS := $(VERSIONS:%=%.mli)

all: coq $(BINS)
	@echo ""
	@echo ""
	@ ! grep -i admit $(VS)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

%.vo : coq

%.ml : %/extract.vo

%.bin : %.ml %.cmi
	ocamlc $(basename $@).ml -o $@

%.cmi : %.mli
	ocamlc -c $^

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f $(BINS) $(MLS) $(MLIS)
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' \) -exec rm -f {} \;
