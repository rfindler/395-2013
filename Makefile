CPDTSRC = cpdt-src
COQC = coqc -I $(CPDTSRC)
GEN_DEPS = braun.vo cpdt-src/CpdtTactics.vo

all: same_structure.vo insert.vo

same_structure.vo: same_structure.v $(GEN_DEPS)
	$(COQC) same_structure.v

insert.vo : insert.v braun.vo $(GEN_DEPS)
	$(COQC) insert.v

braun.vo: braun.v
	$(COQC) braun.v

cpdt-src/CpdtTactics.vo: cpdt-src/CpdtTactics.v
	$(COQC) cpdt-src/CpdtTactics.v
