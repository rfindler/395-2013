CPDTSRC = cpdt-src
COQC = coqc
GEN_DEPS = braun.vo util.vo monad.vo log.vo
# log.vo here is more than strictly neccessary,
# because make_array is probably not going to depend on it

all: insert.vo copy.vo size.vo log_sq.vo make_array.vo

insert.vo : insert.v $(GEN_DEPS)
	$(COQC) insert.v

copy.vo: copy.v $(GEN_DEPS)
	$(COQC) copy.v

size.vo: copy.v $(GEN_DEPS)
	$(COQC) size.v

make_array.vo: copy.v insert.vo $(GEN_DEPS)
	$(COQC) make_array.v

log_sq.vo: log_sq.v util.vo log.vo
	$(COQC) log_sq.v

braun.vo: braun.v
	$(COQC) braun.v

util.vo: util.v
	$(COQC) util.v

monad.vo: monad.v util.vo
	$(COQC) monad.v

log.vo: log.v util.vo
	$(COQC) log.v

clean:
	rm -f *.vo *.glob
