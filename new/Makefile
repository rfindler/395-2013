all: braun
	grep -i admit *v

braun: braun.ml braun.cmi
	ocamlc $@.ml -o $@

braun.cmi: braun.mli
	ocamlc -c $^

braun.mli braun.ml: extract.vo

extract.vo: Makefile.coq
	make -f Makefile.coq all

Makefile.coq: *.v
	coq_makefile *.v > Makefile.coq

clean:
	make -f Makefile.coq clean
	rm -f *.vo *.glob
	rm -f braun.cmi braun.mli braun.ml braun.cmi braun
