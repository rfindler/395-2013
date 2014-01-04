VS := $(shell find . -type f -name '*v')

all: braun
	@echo ""
	@echo ""
	@ ! grep -i admit *v

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Braun $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	find . -name '*.vo' -o -name '*.glob' -o -name '*.cmi' -o -name '*.mli' -o -name 'braun.ml' -o -name 'braun' -exec rm {} \;

VERSIONS := (original omonad logical tmonad)

braun: braun.ml braun.cmi
	ocamlc $@.ml -o $@

braun.cmi: braun.mli
	ocamlc -c $^
