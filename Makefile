CPDTSRC = cpdt-src
COQC = coqc
GEN_DEPS = braun.vo util.vo

all: same_structure.vo insert.vo copy.vo counting_insert.vo counting_copy.vo

construction: insert_time_by_construction.vo copy_time_by_construction.vo counting_make_array.vo monad2.vo

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

monad.vo: monad.v util.vo
	$(COQC) monad.v

size_time_by_construction.vo: size_time_by_construction.v monad2.vo $(GEN_DEPS)
	$(COQC) size_time_by_construction.v

insert_time_by_construction.vo: insert_time_by_construction.v monad2.vo fl_log.vo $(GEN_DEPS)
	$(COQC) insert_time_by_construction.v

copy_time_by_construction.vo: copy_time_by_construction.v monad2.vo fl_log.vo $(GEN_DEPS)
	$(COQC) copy_time_by_construction.v

counting_make_array.vo: counting_make_array.v monad2.vo fl_log.vo braun.vo
	$(COQC) counting_make_array.v

monad2.vo: monad2.v util.vo
	$(COQC) monad2.v

fl_log.vo: fl_log.v util.vo
	$(COQC) fl_log.v

clean:
	rm -f *.vo *.glob
