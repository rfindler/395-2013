GEN := $(shell find . -type f -name '*_gen.rkt' $)
VS := $(shell find . -type f -name '*v' | grep -v _gen.v | grep -v /extract.v $)
VERSIONS := tmonad
GEN_DEPS := rkt/tmonad/emit.rkt rkt/tmonad/main.rkt rkt/tmonad/coq.rkt

all: code paper admit

admit:
	@echo ""
	@echo ""
	@ ! grep -i admit $(VS)

paper: paper/paper.pdf

code: coq extract/extract extract/sextract

paper/paper.pdf: paper/paper.scrbl paper/util.rkt paper/l.v paper/lwl.v paper/running-time.scrbl paper/prims.scrbl paper/insert.scrbl paper/monad.scrbl paper/case-study.scrbl */*.v
	(cd paper; scribble --pdf paper.scrbl; cd ..)

.PHONY: coq clean clean-ml

clean-ml:
	rm -f $(VERSIONS:%=%/extract.vo)

coq: Makefile.coq
	mkdir -p ml
	$(MAKE) -f Makefile.coq

# this dependency doesn't exist so this is always built
# not sure how to build this into Makefile.coq and without
# that it is hard to see what to depend on.
extract/extract.ml: coq
	coqc -q -R . Braun extract/extract.v
	mv extract.ml extract/

extract/sextract.ml: coq
	coqc -q -R . Braun smonad/extract.v
	mv sextract.ml extract/

extract/extract: extract/extract.ml
	ocamlc -I ml -o $@ $^

extract/sextract: extract/sextract.ml
	ocamlc -I ml -o $@ $^

tmonad-gen: $(GEN:%.rkt=%.v)

%_gen.v: %_gen.rkt $(GEN_DEPS)
	racket $< > $@

Makefile.coq: tmonad-gen Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

%.vo : coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f paper/paper.pdf
	rm -f extract/extract.ml extract/a.out extract/extract.mli
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' -o -name '*_gen.v' \) -exec rm -f {} \;
