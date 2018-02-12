VERSION    := 1.0.0
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
	git push origin ocaml-bindlib_$(VERSION)

#### Tests ###################################################################

TESTS = --quick

.PHONY: tests
tests: earley.cmxa earleyStr.cmxa\
       tests/calc_prio_left_ml.ml tests/calc_prio_left2_ml.ml\
       tests/calc_prio_left3_ml.ml tests/calc_prio_left5_ml.ml\
       tests/calc_prio_left6_ml.ml tests/calc_prio_left7_ml.ml\
       tests/calc_prio_left8_ml.ml tests/calc_prio_left9_ml.ml\
       tests/blank_ml.ml tests/gamma3_ml.ml
	$(OCAMLBUILD) tests/test.native
	$(OCAMLBUILD) -pkgs unix,str tests/blank_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left2_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left3_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left5_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left6_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left7_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left8_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left9_ml.native
	$(OCAMLBUILD) -pkgs unix,str tests/gamma3_ml.native
	#$(OCAMLBUILD) -pkgs unix,str tests/calc_prio_left_error_ml.native
	$(OCAMLBUILD) -pkgs unix     tests/calcyacc/calc.native
	./test.native $(TESTS) > /dev/null
	./blank_ml.native $(TESTS) > /dev/null
	./calc_prio_left_ml.native $(TESTS) > /dev/null
	./calc_prio_left2_ml.native --quick > /dev/null #too slow!
	./calc_prio_left3_ml.native $(TESTS) > /dev/null
	./calc_prio_left5_ml.native $(TESTS) > /dev/null
	./calc_prio_left6_ml.native $(TESTS) > /dev/null
	./calc_prio_left7_ml.native $(TESTS) > /dev/null
	./calc_prio_left8_ml.native $(TESTS) > /dev/null
	./calc_prio_left9_ml.native $(TESTS) > /dev/null
	./gamma3_ml.native 30 > /dev/null
	#./calc_prio_left_error_ml.native $(TESTS) > /dev/null

nopatests:
	touch tests/*_ml.ml # avoid rebuild on machine
	make tests          # without pa_ocaml

tests/%_ml.ml: tests/%.ml
	pa_ocaml --ascii $< > $@
