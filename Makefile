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

supp: DNE
	@echo
	@echo did you make clean first?
	@echo
	tar czf supp.tar.gz `ls | grep -v paper`
	du -s -h supp.tar.gz

DNE:

code: coq extract/extract extract/sextract

paper/paper.pdf: paper/paper.scrbl paper/util.rkt paper/running-time.scrbl paper/prims.scrbl paper/insert.scrbl paper/monad.scrbl paper/case-study.scrbl */*.v
	(cd paper; raco make -v paper.scrbl && scribble --pdf paper.scrbl; cd ..)

.PHONY: coq clean clean-ml tmonad-gen

clean-ml:
	rm -f $(VERSIONS:%=%/extract.vo)

coq: Makefile.coq
	mkdir -p ml
	$(MAKE) -f Makefile.coq

extract/extract.ml: extract/extract.vo
	coqc -q -R . Braun extract/extract.v
	mv extract.ml extract/

extract/extract: extract/extract.ml
	ocamlc -I ml -o $@ $^

extract/sextract: extract/sextract.ml
	ocamlc -I ml -o $@ $^

tmonad-gen: $(GEN:%.rkt=%.v)

%_gen.v: %_gen.rkt $(GEN_DEPS)
	raco make $<
	racket $< > $@

Makefile.coq: tmonad-gen Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

%.vo : coq
	@:

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f paper/paper.pdf
	rm -f supp.tar.gz
	rm -f extract/extract.ml extract/a.out extract/extract.mli
	find . -type d -name compiled -exec rm -rf '{}' +
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' -o -name '*_gen.v' \) -exec rm -f {} \;
