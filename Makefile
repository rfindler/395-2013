CPDTSRC = cpdt-src
COQC = coqc
GEN_DEPS = braun.vo util.vo monad.vo log.vo
# log.vo here is more than strictly neccessary,
# because make_array is probably not going to depend on it

all: insert.vo copy.vo size.vo log_sq.vo make_array.vo same_structure.vo

insert.vo : insert.v $(GEN_DEPS)
	$(COQC) insert.v

copy.vo: copy.v $(GEN_DEPS)
	$(COQC) copy.v

size.vo: size.v $(GEN_DEPS)
	$(COQC) size.v

make_array.vo: make_array.v insert.vo le_util.vo $(GEN_DEPS)
	$(COQC) make_array.v

same_structure.vo: same_structure.v braun.vo
	$(COQC) same_structure.v

log_sq.vo: log_sq.v util.vo log.vo le_util.vo
	$(COQC) log_sq.v

braun.vo: braun.v
	$(COQC) braun.v

le_util.vo: le_util.v log.vo util.vo
	$(COQC) le_util.v

util.vo: util.v
	$(COQC) util.v

monad.vo: monad.v util.vo
	$(COQC) monad.v

log.vo: log.v util.vo
	$(COQC) log.v

clean:
	rm -f *.vo *.glob
