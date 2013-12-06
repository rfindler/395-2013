CPDTSRC = cpdt-src
COQC = coqc
GEN_DEPS = braun.vo util.vo

all: same_structure.vo insert.vo copy.vo counting_insert.vo counting_copy.vo

same_structure.vo: same_structure.v $(GEN_DEPS)
	$(COQC) same_structure.v

insert.vo : insert.v $(GEN_DEPS)
	$(COQC) insert.v

counting_insert.vo : counting_insert.v monad.vo $(GEN_DEPS)
	$(COQC) counting_insert.v

copy.vo: copy.v $(GEN_DEPS)
	$(COQC) copy.v

counting_copy.vo : counting_copy.v monad.vo $(GEN_DEPS)
	$(COQC) counting_copy.v

braun.vo: braun.v
	$(COQC) braun.v

util.vo: util.v
	$(COQC) util.v

monad.vo: monad.v
	$(COQC) monad.v

clean:
	rm -f *.vo *.glob
