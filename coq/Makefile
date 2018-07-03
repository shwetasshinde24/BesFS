COQC = coqc
COQDEP = coqdep

COQ_FLAG = -Q "." SGX

SOURCE := $(shell find "." -type f -name '*.v')

$(SOURCE:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $*.v

depend:
	@$(COQDEP) $(COQ_FLAG) $(SOURCE) > .depend

all: $(SOURCE:%.v=%.vo)

clean:
	@rm *.vo *.glob *.aux

.DEFAULT_GOAL := all

include .depend
