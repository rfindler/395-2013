VS := $(shell find . -type f -name '*v')
VERSIONS := logical tmonad
BINS := $(VERSIONS:%=ml/%.bin)
MLS := $(VERSIONS:%=ml/%.ml)
MLIS := $(VERSIONS:%=ml/%.mli)

all: coq $(BINS)
	@echo ""
	@echo ""
	@ ! grep -i admit $(VS)

.PHONY: coq clean clean-ml

clean-ml:
	rm -f $(VERSIONS:%=%/extract.vo)

coq: Makefile.coq
	mkdir -p ml
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

%.vo : coq

%.ml : %/extract.vo

ml/%.ml: %.ml
	mv $^ $@

ml/%.mli: %.mli
	mv $^ $@

ml/%.bin : ml/%.ml ml/%.cmi
	ocamlc -I ml $(basename $@).ml -o $@

ml/%.cmi : ml/%.mli
	ocamlc -c $^

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f $(BINS) $(MLS) $(MLIS)
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' \) -exec rm -f {} \;
