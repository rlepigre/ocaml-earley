FLAGS      := -use-ocamlfind -pkg bytes
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
	ocamlbuild $(FLAGS) $@

earley.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	ocamlbuild $(FLAGS) $@

earleyStr.cma: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	ocamlbuild $(FLAGS) $@

earleyStr.cmxa: $(IMPLFILES) $(INTFFILES) GNUmakefile earley.mllib
	ocamlbuild $(FLAGS) $@

.PHONY: doc
doc: earley.docdir/index.html

earley.docdir/index.html: $(IMPLFILES) $(INTFFILES)
	ocamlbuild $@

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
	ocamlfind install earley $(INTF) $(CMX) $(CMO) $(CMI) $(OBJ) $(LIB) META

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~

MAJOR = 20161116
MINOR = alpha
VERSION = $(MAJOR).$(MINOR)

URLSSH=lama.univ-savoie.fr:WWW
URL=https://lama.univ-savoie.fr/~raffalli/earley

tar: clean
	cd ../earley_tar; darcs pull; make distclean; make; make distclean
	cd ..; tar cvfz earley-$(VERSION).tar.gz --exclude=_darcs --transform "s,earley_tar,earley-$(VERSION),"  earley_tar

distrib: tar doc
	darcs push lama.univ-savoie.fr:WWW/repos/earley/
	scp ../earley-$(VERSION).tar.gz $(URLSSH)/earley/
	ssh lama.univ-savoie.fr "cd WWW/earley; ln -sf earley-$(VERSION).tar.gz earley-latest.tar.gz"
	rsync -r earley.docdir/ $(URLSSH)/earley.doc/
