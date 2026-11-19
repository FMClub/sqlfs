all: src/Makefile
	$(MAKE) -C src

install: src/Makefile
	$(MAKE) -C src install

clean: src/Makefile
	$(MAKE) -C src clean

# The makefile of the Coq development is generated from src/_CoqProject.
src/Makefile: src/_CoqProject
	cd src && coq_makefile -f _CoqProject -o Makefile

.PHONY: all install clean
