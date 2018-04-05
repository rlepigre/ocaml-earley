VERSION    := 1.0.2
OCAMLBUILD := ocamlbuild -use-ocamlfind -quiet

all: depchecks library

#### Checking for dependencies ###############################################

OCAMLF := $(shell which ocamlfind  2> /dev/null)
OCAMLB := $(shell which ocamlbuild 2> /dev/null)

.PHONY: depchecks
depchecks:
ifndef OCAMLB
	$(error "The ocamlbuild program is required...")
endif
ifndef OCAMLF
	$(error "The ocamlfind program is required...")
endif

#### Library targets #########################################################

IMPLFILES  := $(wildcard *.ml)
INTFFILES  := $(wildcard *.mli)

.PHONY: library
library: _build/earley.cma _build/earley.cmxa \
	       _build/earleyStr.cma _build/earleyStr.cmxa META

_build/earley.cma: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	@echo "[BYT] $(notdir $@)"
	@$(OCAMLBUILD) earley.cma

_build/earley.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	@echo "[OPT] $(notdir $@)"
	@$(OCAMLBUILD) earley.cmxa

_build/earleyStr.cma: $(IMPLFILES) $(INTFFILES) GNUmakefile earleyStr.mllib
	@echo "[BYT] $(notdir $@)"
	@$(OCAMLBUILD) earleyStr.cma

_build/earleyStr.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earleyStr.mllib
	@echo "[OPT] $(notdir $@)"
	@$(OCAMLBUILD) earleyStr.cmxa

META: GNUmakefile
	@echo "[GEN] $@"
	@echo 'name="earley"'                                   > $@
	@echo 'version="$(VERSION)"'                           >> $@
	@echo 'description="Earley parser combinator library"' >> $@
	@echo 'archive(byte)="earley.cma"'                     >> $@
	@echo 'archive(native)="earley.cmxa"'                  >> $@
	@echo                                                  >> $@
	@echo 'package "str" ('                                >> $@
	@echo '  version="$(VERSION)"'                         >> $@
	@echo '  requires="earley,str"'                        >> $@
	@echo '  description="Str support for Earley"'         >> $@
	@echo '  archive(byte)="earleyStr.cma"'                >> $@
	@echo '  archive(native)="earleyStr.cmxa"'             >> $@
	@echo ')'                                              >> $@

#### Documentation ###########################################################

.PHONY: doc
doc: earley.docdir/index.html

earley.docdir/index.html: $(IMPLFILES) $(INTFFILES)
	$(OCAMLBUILD) $@

#### Cleaning targets ########################################################

clean:
	@$(OCAMLBUILD) -clean

distclean: clean
	@rm -f META
	@find . -name "*~" -type f -exec rm {} \;
	@find . -name "#*" -type f -exec rm {} \;
	@find . -name ".#*" -type f -exec rm {} \;

#### Installation and release ################################################

uninstall:
	@(ocamlfind query earley -qo -qe && ocamlfind remove earley) || true

EXPORTED := charset input regexp earley earleyStr
MLIS := $(addsuffix .mli,$(addprefix _build/,$(EXPORTED)))
CMIS := $(MLIS:.mli=.cmi)
CMXS := $(addprefix _build/,$(IMPLFILES:.ml=.cmx))
LIB  := _build/earley.cma _build/earley.cmxa _build/earley.a \
	      _build/earleyStr.cma _build/earleyStr.cmxa _build/earleyStr.a

install: all uninstall
	@ocamlfind install earley $(MLIS) $(CMIS) $(CMXS) $(LIB) META

.PHONY: release
release: distclean
	git push origin
	git tag -a ocaml-earley_$(VERSION)
	git push origin ocaml-earley_$(VERSION)

#### Tests ###################################################################

.PHONY: tests
tests: all
	@./tests.sh --quick

.PHONY: full_tests
full_tests: all
	@./tests.sh --full
