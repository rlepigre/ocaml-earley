OCAMLFIND = ocamlfind
OCAMLC = $(OCAMLFIND) ocamlc -package bytes
OCAMLOPT = $(OCAMLFIND) ocamlopt -package bytes -intf-suffix .cmi
BINDIR = $(dir $(shell which ocamlc))

# do not add earley.cm(x)a because earley in bootstrap is
# does not contain pa_ocaml_prelude and adding earley.cm(x)a
# here will make fail after make distclean
# a more complete all is given below when pa_ocaml binary
# is present

INSTALLED = ahash.cmi ahash.cmo ahash.mli ahash.cmx earley.cmi earley.cmo earley.mli earley.cmx charset.cmi charset.cmo charset.mli charset.cmx regexp.cmi regexp.cmo regexp.mli regexp.cmx input.cmi input.cmo input.mli input.cmx earley.cma earley.cmxa earley.a pa_ocaml_prelude.cmi pa_ocaml_prelude.cmo pa_ocaml_prelude.cmx pa_ocaml.cmi pa_ocaml.cmo pa_ocaml.cmx pa_parser.cmi pa_parser.cmx pa_parser.cmo pa_main.cmi pa_main.cmx pa_main.cmo decap_ocaml.cmxa decap_ocaml.cma earley.a decap_ocaml.a pa_ast.cmx pa_ast.cmo pa_ast.cmi pa_lexing.cmi pa_lexing.cmx pa_lexing.cmo

HAS_PA_OCAML=$(shell if [ -x pa_ocaml ]; then echo 1; else echo 0; fi)
OCAMLVERSION=$(shell ocamlc -version | sed s/+.*//)
BOOTDIR=./bootstrap/$(OCAMLVERSION)
export OCAMLFIND_IGNORE_DUPS_IN = $(BOOTDIR)

ifeq ($(HAS_PA_OCAML),1)
B=.
IB=-I $(B) -I $(BOOTDIR)
PA_OCAML=./pa_ocaml
PP= -pp "$(PA_OCAML) $(ASCII)"
all: pa_ocaml earley.cmxa $(B)/earley.cma $(B)/decap_ocaml.cmxa $(B)/decap_ocaml.cma
else
B=$(BOOTDIR)
IB=-I $(B)
PP=
all: pa_ocaml earley.cmxa $(B)/decap_ocaml.cmxa
endif

MAJOR = 20161011
MINOR = alpha
VERSION = $(MAJOR).$(MINOR)
ASCII =

COMPILER_INC = -I +compiler-libs
COMPILER_LIBS = ocamlcommon.cma
COMPILER_PARSERS =
COMPILER_TOP = ocamlbytecomp.cma ocamltoplevel.cma
COMPILER_LIBO := $(COMPILER_LIBS:.cma=.cmxa)
COMPILER_LIBO := $(COMPILER_LIBO:.cmo=.cmx)
COMPILER_PARSERO := $(COMPILER_PARSERS:.cma=.cmxa)
COMPILER_PARSERO := $(COMPILER_PARSERO:.cmo=.cmx)

ASTTOOLSI=$(BOOTDIR)/compare.cmi $(BOOTDIR)/iter.cmi $(BOOTDIR)/quote.cmi
ASTTOOLSO=$(ASTTOOLSI:.cmi=.cmo)
ASTTOOLSX=$(ASTTOOLSI:.cmi=.cmx)
ASTTOOLSIO=$(ASTTOOLSI) $(ASTTOOLSO)
ASTTOOLSIX=$(ASTTOOLSI) $(ASTTOOLSX)

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.cmo

%.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

earley.cmi: charset.cmi input.cmi regexp.cmi ahash.cmi fixpoint.cmi

earley.cmo: earley.cmi charset.cmi input.cmi regexp.cmi ahash.cmi fixpoint.cmi

earley.cmx: charset.cmx charset.cmi regexp.cmx regexp.cmi input.cmx input.cmi ahash.cmi ahash.cmx fixpoint.cmx

earley.cmxa: charset.cmx input.cmx regexp.cmx ahash.cmx fixpoint.cmx earley.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -a -o $@ $^

earley.cma: charset.cmo input.cmo regexp.cmo ahash.cmo fixpoint.cmo earley.cmo
	$(OCAMLC) $(OCAMLFLAGS) -a -o $@ $^

$(B)/decap_ocaml.cma: $(B)/pa_lexing.cmo $(B)/pa_ast.cmo $(ASTTOOLSO) $(B)/pa_ocaml_prelude.cmo $(B)/pa_parser.cmo $(B)/pa_ocaml.cmo $(B)/pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -a -o $@ $^

$(B)/decap_ocaml.cmxa: $(B)/pa_lexing.cmx $(B)/pa_ast.cmx $(ASTTOOLSX) $(B)/pa_ocaml_prelude.cmx $(B)/pa_parser.cmx $(B)/pa_ocaml.cmx $(B)/pa_main.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -a -o $@ $^

earley.a: earley.cmxa;
decap_ocaml.a: decap_ocaml.cmxa;

$(BOOTDIR)/compare.cmo $(BOOTDIR)/compare.cmi: $(BOOTDIR)/compare.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(BOOTDIR)/compare.cmx: $(BOOTDIR)/compare.ml $(BOOTDIR)/compare.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(BOOTDIR)/iter.cmo $(BOOTDIR)/iter.cmi: $(BOOTDIR)/iter.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(BOOTDIR)/iter.cmx: $(BOOTDIR)/iter.ml $(BOOTDIR)/iter.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(BOOTDIR)/quote.cmo $(BOOTDIR)/quote.cmi: $(BOOTDIR)/quote.ml $(B)/pa_ast.cmi
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(BOOTDIR)/quote.cmx: $(BOOTDIR)/quote.ml $(BOOTDIR)/quote.cmi $(B)/pa_ast.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_lexing.cmo $(B)/pa_lexing.cmi: $(B)/pa_lexing.ml input.cmi earley.cma
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_lexing.cmx: $(B)/pa_lexing.ml $(B)/pa_lexing.cmi input.cmx earley.cmxa
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ocaml_prelude.cmo $(B)/pa_ocaml_prelude.cmi: $(B)/pa_ocaml_prelude.ml charset.cmi input.cmi earley.cma $(B)/pa_ast.cmi $(B)/pa_lexing.cmi
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ocaml_prelude.cmx: $(B)/pa_ocaml_prelude.ml $(B)/pa_ocaml_prelude.cmi charset.cmx input.cmx earley.cmxa $(B)/pa_ast.cmx $(B)/pa_lexing.cmx
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ast.cmo $(B)/pa_ast.cmi: $(B)/pa_ast.ml
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ast.cmx: $(B)/pa_ast.ml $(B)/pa_ast.cmi
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_parser.cmo $(B)/pa_parser.cmi: $(B)/pa_parser.ml $(B)/pa_ast.cmo $(B)/pa_ocaml_prelude.cmo $(ASTTOOLSI) earley.cma
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_parser.cmx: $(B)/pa_parser.ml $(B)/pa_parser.cmi $(B)/pa_ast.cmx $(B)/pa_ocaml_prelude.cmx $(ASTTOOLSIX) earley.cmxa
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ocaml.cmo $(B)/pa_ocaml.cmi: $(B)/pa_ocaml.ml $(ASTTOOLSI) $(B)/pa_ocaml_prelude.cmo earley.cma
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_ocaml.cmx: $(B)/pa_ocaml.ml $(B)/pa_ocaml.cmi $(ASTTOOLSIX) $(B)/pa_ocaml_prelude.cmx earley.cmxa
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_main.cmo $(B)/pa_main.cmi: $(B)/pa_main.ml input.cmi $(B)/pa_ocaml.cmo
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_main.cmx: $(B)/pa_main.ml $(B)/pa_main.cmi input.cmx $(B)/pa_ocaml.cmx
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_default.cmo $(B)/pa_default.cmi: $(B)/pa_default.ml $(B)/pa_ocaml_prelude.cmo $(B)/pa_parser.cmo $(B)/pa_ocaml.cmo $(B)/pa_main.cmo
	$(OCAMLC) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

$(B)/pa_default.cmx: $(B)/pa_default.ml $(B)/pa_default.cmi $(B)/pa_ocaml_prelude.cmx $(B)/pa_parser.cmx $(B)/pa_ocaml.cmx $(B)/pa_main.cmx
	$(OCAMLOPT) $(PP) $(OCAMLFLAGS) $(COMPILER_INC) -c $(IB) $<

pa_ocaml: earley.cmxa $(B)/decap_ocaml.cmxa $(B)/pa_default.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -linkall $(IB) -o $@ unix.cmxa str.cmxa $(COMPILER_LIBO) $^

pa_ocaml.byt: earley.cma $(B)/decap_ocaml.cma $(B)/pa_default.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -linkall $(IB) -o $@ unix.cma str.cma $(COMPILER_LIBS) $^

test_parsers: earley.cmxa $(B)/decap_ocaml.cmxa test_parsers.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -o $@ dynlink.cmxa unix.cmxa str.cmxa	$(COMPILER_INC) $(COMPILER_LIBO) $(COMPILER_PARSERO) $^

asttools: earley.cmxa decap_ocaml.cmxa
	cd ast_tools && make

#BOOTSTRAP OF ONE VERSION (SEE all_boot.sh AND INSTALL opam FOR MULTIPLE OCAML VERSION
boot: BACKUP:=$(BOOTDIR)/$(shell date +%Y-%m-%d-%H-%M-%S)
boot:
	- if [ ! -d $(BOOTDIR) ] ; then mkdir $(BOOTDIR); fi
	- if [ ! -d $(BACKUP) ] ; then \
	     mkdir $(BACKUP) ; \
	     cp $(BOOTDIR)/*.ml $(BACKUP) ; \
	fi
	export OCAMLVERSION=$(OCAMLVERSION); \
	./pa_ocaml --ascii pa_lexing.ml > $(BOOTDIR)/pa_lexing.ml ;\
	./pa_ocaml --ascii pa_ocaml_prelude.ml > $(BOOTDIR)/pa_ocaml_prelude.ml ;\
	./pa_ocaml --ascii pa_parser.ml > $(BOOTDIR)/pa_parser.ml ;\
	./pa_ocaml --ascii pa_ocaml.ml > $(BOOTDIR)/pa_ocaml.ml ;\
	./pa_ocaml --ascii pa_ast.ml > $(BOOTDIR)/pa_ast.ml ;\
	./pa_ocaml --ascii pa_main.ml > $(BOOTDIR)/pa_main.ml ;\
	./pa_ocaml --ascii pa_default.ml > $(BOOTDIR)/pa_default.ml

install: uninstall $(INSTALLED)
	install -m 755 -d $(BINDIR)
	ocamlfind install earley META $(INSTALLED)
	install -m 755 pa_ocaml $(BINDIR)

uninstall:
	ocamlfind remove earley
	rm -f $(BINDIR)/pa_ocaml

clean:
	- rm -f *.cm* *.o *.a
	- rm -f bootstrap/*/*.cm* bootstrap/*/*.o bootstrap/*/*.a
	$(MAKE) -e -j 1 -C ast_tools clean

distclean: clean
	- rm -f pa_ocaml pa_ocaml.byt *~ \#*\#
	$(MAKE) -e -j 1 -C ast_tools distclean

URLSSH=lama.univ-savoie.fr:WWW
URL=https://lama.univ-savoie.fr/~raffalli/earley

doc: charset.mli input.mli fixpoint.mli earley.mli earley.cmxa
	mkdir -p html
	ocamldoc -d html -html earley.mli charset.mli input.mli

tar: doc clean
	cd ../decap_tar; darcs pull; make distclean; make; make; make distclean
	cd ..; tar cvfz earley-$(VERSION).tar.gz --exclude=_darcs --transform "s,decap_tar,earley-$(VERSION),"  decap_tar

distrib: clean tar doc
	darcs push lama.univ-savoie.fr:WWW/repos/earley/
	scp ../earley-$(VERSION).tar.gz $(URLSSH)/earley/
	rsync -r --delete ../decap_tar/examples/ $(URLSSH)/earley/examples/
	ssh lama.univ-savoie.fr "cd WWW/earley; ln -sf earley-$(VERSION).tar.gz earley-latest.tar.gz"
	rsync -r www/ $(URLSSH)/

OPAMREPO=$(HOME)/Caml/opam-repository/packages/earley

opam_git: opam distrib
	mkdir -p $(OPAMREPO)/earley.$(VERSION)
	cp opam $(OPAMREPO)/earley.$(VERSION)/opam
	cp description.txt $(OPAMREPO)/earley.$(VERSION)/descr
	echo -n "archive: \""  > $(OPAMREPO)/earley.$(VERSION)/url
	echo -n "$(URL)/earley-$(VERSION).tar.gz" >> $(OPAMREPO)/earley.$(VERSION)/url
	echo "\"" >> $(OPAMREPO)/earley.$(VERSION)/url
	echo -n "checksum: \"" >> $(OPAMREPO)/earley.$(VERSION)/url
	echo -n `md5sum ../earley-$(VERSION).tar.gz | cut -b -32` >> $(OPAMREPO)/earley.$(VERSION)/url
	echo "\"" >> $(OPAMREPO)/earley.$(VERSION)/url
