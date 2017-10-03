TESTS = --quick

VERSION    := 1.0.0
OCAMLBUILD := ocamlbuild -use-ocamlfind
IMPLFILES  := $(wildcard *.ml)
INTFFILES  := $(wildcard *.mli)

all: earley.cma earley.cmxa earleyStr.cma earleyStr.cmxa

# Try to find ocamlfind and ocamlbuild.
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

earley.cma: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	$(OCAMLBUILD) $@

earley.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	$(OCAMLBUILD) $@

earleyStr.cma: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	$(OCAMLBUILD) $@

earleyStr.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	$(OCAMLBUILD) $@

.PHONY: doc
doc: earley.docdir/index.html

earley.docdir/index.html: $(IMPLFILES) $(INTFFILES)
	$(OCAMLBUILD) $@

uninstall:
	@ocamlfind remove earley

.PHONY: tests
tests: earley.cmxa earleyStr.cmxa\
       tests/calc_prio_left_ml.ml tests/calc_prio_left2_ml.ml\
       tests/calc_prio_left3_ml.ml tests/calc_prio_left5_ml.ml\
       tests/calc_prio_left6_ml.ml tests/calc_prio_left7_ml.ml\
       tests/calc_prio_left8_ml.ml tests/calc_prio_left9_ml.ml\
       tests/blank_ml.ml
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
	#./calc_prio_left_error_ml.native $(TESTS) > /dev/null

nopatests:
	touch tests/*_ml.ml # avoid rebuild on machine
	make tests          # without pa_ocaml

tests/%_ml.ml: tests/%.ml
	pa_ocaml --ascii $< > $@

IMPL := $(addprefix _build/,$(IMPLFILES))
INTF := $(addprefix _build/,$(INTFFILES))
CMX  := $(IMPL:.ml=.cmx)
CMO  := $(IMPL:.ml=.cmo)
CMI  := $(IMPL:.ml=.cmi)
OBJ  := $(IMPL:.ml=.o)
LIB  := _build/earley.cma _build/earley.cmxa _build/earley.a \
	      _build/earleyStr.cma _build/earleyStr.cmxa _build/earleyStr.a

install: all uninstall META
	@ocamlfind install earley $(INTF) $(CMX) $(CMO) $(CMI) $(OBJ) $(LIB) META

clean:
	$(OCAMLBUILD) -clean

distclean: clean
	- find -name "*~" -type f -exec rm {} \;
	- find -name "#*" -type f -exec rm {} \;
	- find -name ".#*" -type f -exec rm {} \;

.PHONY: release
release: distclean
	git push origin
	git tag -a ocaml-earley_$(VERSION)
	git push origin ocaml-bindlib_$(VERSION)
