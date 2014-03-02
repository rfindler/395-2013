VS := $(shell find . -type f -name '*v' | grep -v _gen.v$)
VERSIONS := logical tmonad
BINS := $(VERSIONS:%=ml/%.bin)
MLS := $(VERSIONS:%=ml/%.ml)
MLIS := $(VERSIONS:%=ml/%.mli)
GEN_DEPS := rkt/emit.rkt rkt/tmonad.rkt rkt/tmonad-coq.rkt

all: coq $(BINS) paper/paper.pdf
	@echo ""
	@echo ""
	@ ! grep -i admit $(VS)

paper/paper.pdf: paper/paper.scrbl paper/background.scrbl paper/util.rkt paper/l.v paper/lwl.v paper/running-time.scrbl paper/insert.scrbl
	(cd paper; scribble --pdf paper.scrbl; cd ..)

.PHONY: coq clean clean-ml

clean-ml:
	rm -f $(VERSIONS:%=%/extract.vo)

coq: Makefile.coq
	mkdir -p ml
	$(MAKE) -f Makefile.coq

tmonad-gen: tmonad/insert_gen.v tmonad/make_array_naive_gen.v \
	    tmonad/copy_fib_gen.v tmonad/size_linear_gen.v \
	    tmonad/copy2_gen.v tmonad/copy_gen.v tmonad/copy_linear_gen.v \
            tmonad/sub1_gen.v tmonad/fold_gen.v

tmonad/insert_gen.v: rkt/insert.rkt $(GEN_DEPS)
	racket rkt/insert.rkt > tmonad/insert_gen.v
tmonad/make_array_naive_gen.v: rkt/make_array_naive.rkt $(GEN_DEPS)
	racket rkt/make_array_naive.rkt > tmonad/make_array_naive_gen.v
tmonad/copy_fib_gen.v: rkt/copy_fib.rkt $(GEN_DEPS)
	racket rkt/copy_fib.rkt > tmonad/copy_fib_gen.v
tmonad/size_linear_gen.v: rkt/size_linear.rkt $(GEN_DEPS)
	racket rkt/size_linear.rkt > tmonad/size_linear_gen.v
tmonad/copy2_gen.v: rkt/copy2.rkt $(GEN_DEPS)
	racket rkt/copy2.rkt > tmonad/copy2_gen.v
tmonad/copy_gen.v: rkt/copy.rkt $(GEN_DEPS)
	racket rkt/copy.rkt > tmonad/copy_gen.v
tmonad/copy_linear_gen.v: rkt/copy_linear.rkt $(GEN_DEPS)
	racket rkt/copy_linear.rkt > tmonad/copy_linear_gen.v
tmonad/sub1_gen.v: rkt/sub1.rkt $(GEN_DEPS)
	racket rkt/sub1.rkt > tmonad/sub1_gen.v
tmonad/fold_gen.v: rkt/fold.rkt $(GEN_DEPS)
	racket rkt/fold.rkt > tmonad/fold_gen.v

Makefile.coq: tmonad-gen Makefile $(VS)
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
	rm -f paper/paper.pdf
	rm -f $(BINS) $(MLS) $(MLIS)
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' \) -exec rm -f {} \;
