VS := $(shell find . -type f -name '*v' | grep -v _gen.v | grep -v /extract.v $)
VERSIONS := tmonad
GEN_DEPS := rkt/emit.rkt rkt/tmonad.rkt rkt/tmonad-coq.rkt

all: coq paper/paper.pdf extract/a.out
	@echo ""
	@echo ""
	@ ! grep -i admit $(VS)

paper/paper.pdf: paper/paper.scrbl paper/background.scrbl paper/util.rkt paper/l.v paper/lwl.v paper/running-time.scrbl paper/insert.scrbl tmonad/*.v
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

extract/a.out: extract/extract.ml
	(cd extract; ocamlc -I ml extract.ml)

tmonad-gen: insert/insert_log_gen.v \
            size/size_linear_gen.v \
            size/diff_gen.v \
            size/size_log_sq_gen.v \
            copy/copy_linear_gen.v \
	    copy/copy_fib_log_gen.v \
            copy/copy_log_sq_gen.v \
	    copy/copy2_gen.v copy/copy_log_gen.v \
            make_array/make_array_nlogn1_gen.v \
            make_array/make_array_nlogn2_gen.v \
            make_array/unravel_gen.v \
            make_array/take_gen.v \
            sub1/sub1_gen.v \
            fold/fold_gen.v

insert/insert_log_gen.v: rkt/insert.rkt $(GEN_DEPS)
	racket rkt/insert.rkt > insert/insert_log_gen.v

size/size_linear_gen.v: rkt/size_linear.rkt $(GEN_DEPS)
	racket rkt/size_linear.rkt > size/size_linear_gen.v
size/diff_gen.v: rkt/diff.rkt $(GEN_DEPS)
	racket rkt/diff.rkt > size/diff_gen.v
size/size_log_sq_gen.v: rkt/size_log_sq.rkt $(GEN_DEPS)
	racket rkt/size_log_sq.rkt > size/size_log_sq_gen.v

copy/copy_linear_gen.v: rkt/copy_linear.rkt $(GEN_DEPS)
	racket rkt/copy_linear.rkt > copy/copy_linear_gen.v
copy/copy_fib_log_gen.v: rkt/copy_fib.rkt $(GEN_DEPS)
	racket rkt/copy_fib.rkt > copy/copy_fib_log_gen.v
copy/copy_log_sq_gen.v: rkt/copy_insert.rkt $(GEN_DEPS)
	racket rkt/copy_insert.rkt > copy/copy_log_sq_gen.v
copy/copy2_gen.v: rkt/copy2.rkt $(GEN_DEPS)
	racket rkt/copy2.rkt > copy/copy2_gen.v
copy/copy_log_gen.v: rkt/copy.rkt $(GEN_DEPS)
	racket rkt/copy.rkt > copy/copy_log_gen.v

make_array/make_array_nlogn1_gen.v: rkt/make_array_naive.rkt $(GEN_DEPS)
	racket rkt/make_array_naive.rkt > make_array/make_array_nlogn1_gen.v
make_array/make_array_nlogn2_gen.v: rkt/make_array_nlogn2.rkt $(GEN_DEPS)
	racket rkt/make_array_nlogn2.rkt > make_array/make_array_nlogn2_gen.v
make_array/unravel_gen.v: rkt/unravel.rkt $(GEN_DEPS)
	racket rkt/unravel.rkt > make_array/unravel_gen.v
make_array/take_gen.v: rkt/take.rkt $(GEN_DEPS)
	racket rkt/take.rkt > make_array/take_gen.v

sub1/sub1_gen.v: rkt/sub1.rkt $(GEN_DEPS)
	racket rkt/sub1.rkt > sub1/sub1_gen.v
fold/fold_gen.v: rkt/fold.rkt $(GEN_DEPS)
	racket rkt/fold.rkt > fold/fold_gen.v

Makefile.coq: tmonad-gen Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

%.vo : coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f paper/paper.pdf
	rm -f extract/extract.ml extract/a.out
	find . \( -name '*.vo' -o -name '*.d' -o -name '*.glob' -o -name '*.cmi' -o -name '*.cmo' -o -name '*_gen.v' \) -exec rm -f {} \;
