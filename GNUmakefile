VERSION    := 1.0.0
OCAMLBUILD := ocamlbuild -use-ocamlfind -pkg bytes -quiet
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
	- rm -f *~ \#*\# .\#*

.PHONY: release
release: distclean
	git push origin
	git tag -a ocaml-earley_$(VERSION)
	git push origin ocaml-earley_$(VERSION)
