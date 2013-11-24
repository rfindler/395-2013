CPDTSRC = cpdt-src
COQC = coqc -I $(CPDTSRC)
GEN_DEPS = braun.vo cpdt-src/CpdtTactics.vo

all: same_structure.vo insert.vo copy.vo

same_structure.vo: same_structure.v $(GEN_DEPS)
	$(COQC) same_structure.v

insert.vo : insert.v $(GEN_DEPS)
	$(COQC) insert.v

copy.vo: copy.v $(GEN_DEPS)
	$(COQC) copy.v

braun.vo: braun.v
	$(COQC) braun.v

cpdt-src/CpdtTactics.vo: cpdt-src/CpdtTactics.v
	$(COQC) cpdt-src/CpdtTactics.v

