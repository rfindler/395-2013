CPDTSRC = cpdt-src
COQC = coqc
GEN_DEPS = braun.vo util.vo

all: same_structure.vo insert.vo copy.vo

same_structure.vo: same_structure.v $(GEN_DEPS)
	$(COQC) same_structure.v

insert.vo : insert.v $(GEN_DEPS)
	$(COQC) insert.v

copy.vo: copy.v $(GEN_DEPS)
	$(COQC) copy.v

braun.vo: braun.v
	$(COQC) braun.v

util.vo: util.v
	$(COQC) util.v

monad.vo: monad.v
	$(COQC) monad.v

clean:
	rm -f *.vo *.glob
