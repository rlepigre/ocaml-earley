OCAMLFIND = ocamlfind
OCAMLC = $(OCAMLFIND) ocamlc
OCAMLOPT = $(OCAMLFIND) ocamlopt
BINDIR = /usr/local/bin
LIBDIR = $(shell ocamlc -where)/decap

# do not add decap.cm(x)a because decap in bootstrap is
# does not contain pa_ocaml_prelude and adding decap.cm(x)a
# here will make fail after make distclean
# a more complete all is given below when pa_ocaml binary
# is present

INSTALLED = ahash.cmi ahash.cmo ahash.mli ahash.cmx decap.cmi decap.cmo decap.mli decap.cmx charset.cmi charset.cmo charset.mli charset.cmx input.cmi input.cmo input.mli input.cmx decap.cma decap.cmxa decap.a pa_ocaml_prelude.cmi pa_ocaml_prelude.cmo pa_ocaml_prelude.cmx pa_ocaml.cmi pa_ocaml.cmo pa_ocaml.cmx pa_parser.cmi pa_parser.cmx pa_parser.cmo pa_main.cmi pa_main.cmx pa_main.cmo decap_ocaml.cmxa decap_ocaml.cma decap.a decap_ocaml.a pa_ast.cmx pa_ast.cmo pa_ast.cmi

all: pa_ocaml
HAS_PA_OCAML=$(shell if [ -x pa_ocaml ]; then echo 1; else echo 0; fi)

OCAMLVERSION=$(shell ocamlc -version)
BOOTDIR=./bootstrap/$(OCAMLVERSION)
export OCAMLFIND_IGNORE_DUPS_IN = $(BOOTDIR)

MAJOR = 20160307
MINOR = alpha
VERSION = $(MAJOR).$(MINOR)

COMPILER_INC = -I +compiler-libs
COMPILER_LIBS = ocamlcommon.cma
COMPILER_PARSERS =
COMPILER_TOP = ocamlbytecomp.cma ocamltoplevel.cma
COMPILER_LIBO := $(COMPILER_LIBS:.cma=.cmxa)
COMPILER_LIBO := $(COMPILER_LIBO:.cmo=.cmx)
COMPILER_PARSERO := $(COMPILER_PARSERS:.cma=.cmxa)
COMPILER_PARSERO := $(COMPILER_PARSERO:.cmo=.cmx)

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml %.cmi
	$(OCAMLC) $(OCAMLFLAGS) -c $<

%.cmx: %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

fixpoint.cmi: fixpoint.mli

fixpoint.cmx fixpoint.cmo: fixpoint.ml

decap.cmi: charset.cmi input.cmi ahash.cmi fixpoint.cmi

decap.cmo: charset.cmi input.cmi ahash.cmi fixpoint.cmi

decap.cmx: charset.cmx charset.cmi input.cmx input.cmi ahash.cmi ahash.cmx fixpoint.cmx
decap.cmx: OCAMLFLAGS=-noassert

decap.cmxa: charset.cmx input.cmx ahash.cmx fixpoint.cmx decap.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -a -o $@ $^

decap.cma: charset.cmo input.cmo ahash.cmo fixpoint.cmo decap.cmo
	$(OCAMLC) $(OCAMLFLAGS) -a -o $@ $^

decap_ocaml.cmxa: pa_lexing.cmx pa_ast.cmx $(BOOTDIR)/compare.cmx $(BOOTDIR)/iter.cmx $(BOOTDIR)/quote.cmx pa_ocaml_prelude.cmx pa_parser.cmx pa_ocaml.cmx pa_main.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -a -o $@ $^

decap_ocaml.cma: pa_lexing.cmo pa_ast.cmo $(BOOTDIR)/compare.cmo $(BOOTDIR)/iter.cmo $(BOOTDIR)/quote.cmo pa_ocaml_prelude.cmo pa_parser.cmo pa_ocaml.cmo pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -a -o $@ $^

decap.a: decap.cmxa;
decap_ocaml.a: decap_ocaml.cmxa;

ifeq ($(HAS_PA_OCAML),1)

all: decap.cmxa decap.cma decap_ocaml.cmxa decap_ocaml.cma

$(BOOTDIR)/compare.cmo: $(BOOTDIR)/compare.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

$(BOOTDIR)/compare.cmx: $(BOOTDIR)/compare.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

$(BOOTDIR)/iter.cmo: $(BOOTDIR)/iter.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

$(BOOTDIR)/iter.cmx: $(BOOTDIR)/iter.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

$(BOOTDIR)/quote.cmo: $(BOOTDIR)/quote.ml pa_ast.cmi
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

$(BOOTDIR)/quote.cmx: $(BOOTDIR)/quote.ml pa_ast.cmx pa_ast.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -c $<

pa_lexing.cmo: pa_lexing.ml input.cmi
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_lexing.cmx: pa_lexing.ml input.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_ocaml_prelude.cmo: pa_ocaml_prelude.ml charset.cmi input.cmi decap.cmi pa_ast.cmi pa_lexing.cmi
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_ast.cmi pa_ast.cmo: pa_ast.ml
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_ast.cmx: pa_ast.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_ocaml.cmo: pa_ocaml.ml $(BOOTDIR)/quote.cmi pa_ocaml_prelude.cmo decap.cma
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_parser.cmo: pa_parser.ml pa_ast.cmo pa_ocaml_prelude.cmo  $(BOOTDIR)/compare.cmo $(BOOTDIR)/iter.cmo $(BOOTDIR)/quote.cmo decap.cma
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_main.cmo: pa_main.ml input.cmi pa_ocaml.cmo
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_ocaml_prelude.cmx: pa_ocaml_prelude.ml charset.cmx input.cmx decap.cmx pa_ast.cmx pa_lexing.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_ocaml.cmx: pa_ocaml.ml $(BOOTDIR)/quote.cmx pa_ocaml_prelude.cmx decap.cmxa
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_parser.cmx: pa_parser.ml pa_ast.cmx pa_ocaml_prelude.cmx decap.cmxa $(BOOTDIR)/compare.cmx $(BOOTDIR)/iter.cmx $(BOOTDIR)/quote.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml -I $(BOOTDIR) $(COMPILER_INC) -c $<

pa_opt_main.ml: pa_main.ml
	cp pa_main.ml pa_opt_main.ml

pa_main.cmx: pa_main.ml input.cmi input.cmx pa_ocaml.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_default.cmo: pa_default.ml pa_ocaml_prelude.cmo pa_parser.cmo pa_ocaml.cmo pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_default.cmx: pa_default.ml pa_ocaml_prelude.cmx pa_parser.cmx pa_ocaml.cmx pa_main.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -pp ./pa_ocaml $(COMPILER_INC) -c $<

pa_ocaml: decap.cmxa decap_ocaml.cmxa pa_default.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -linkall -o $@ unix.cmxa str.cmxa $(COMPILER_LIBO) $^

pa_ocaml.byt: decap.cma decap_ocaml.cma pa_default.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -linkall -o $@ unix.cma str.cma $(COMPILER_LIBS) $^

test_parsers: decap.cmxa decap_ocaml.cmxa test_parsers.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I +camlp4 -I +camlp4/Camlp4Parsers -o $@ dynlink.cmxa unix.cmxa str.cmxa camlp4lib.cmxa Camlp4OCamlRevisedParser.cmx Camlp4OCamlParser.cmx	$(COMPILER_INC) $(COMPILER_LIBO) $(COMPILER_PARSERO) $^

else

$(BOOTDIR)/compare.cmo: $(BOOTDIR)/compare.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/compare.cmx: $(BOOTDIR)/compare.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/iter.cmo: $(BOOTDIR)/iter.ml $(BOOTDIR)/pa_ocaml_prelude.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/iter.cmx: $(BOOTDIR)/iter.ml $(BOOTDIR)/pa_ocaml_prelude.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/quote.cmo: $(BOOTDIR)/quote.ml $(BOOTDIR)/pa_ast.cmo $(BOOTDIR)/pa_ast.cmi
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/quote.cmx: $(BOOTDIR)/quote.ml $(BOOTDIR)/pa_ast.cmx $(BOOTDIR)/pa_ast.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_ocaml_prelude.cmo: $(BOOTDIR)/pa_ocaml_prelude.ml $(BOOTDIR)/pa_ast.cmi charset.cmi input.cmi decap.cmi
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/pa_ocaml.cmo: $(BOOTDIR)/pa_ocaml.ml $(BOOTDIR)/pa_ocaml_prelude.cmo decap.cma
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/pa_parser.cmo: $(BOOTDIR)/pa_parser.ml $(BOOTDIR)/pa_ast.cmo $(BOOTDIR)/pa_ocaml_prelude.cmo  $(BOOTDIR)/compare.cmo $(BOOTDIR)/iter.cmo $(BOOTDIR)/quote.cmo decap.cma
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

$(BOOTDIR)/pa_main.cmo: $(BOOTDIR)/pa_main.ml input.cmi $(BOOTDIR)/pa_ocaml.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -c -I $(BOOTDIR) $<

pa_ocaml.byt: decap.cma $(BOOTDIR)/compare.cmo $(BOOTDIR)/iter.cmo $(BOOTDIR)/quote.cmo $(BOOTDIR)/pa_ocaml_prelude.cmo $(BOOTDIR)/pa_ast.cmo $(BOOTDIR)/pa_parser.cmo $(BOOTDIR)/pa_ocaml.cmo $(BOOTDIR)/pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -o $@ unix.cma str.cma  $(COMPILER_LIBS) $(COMPILER_TOP) $^

$(BOOTDIR)/pa_ocaml_prelude.cmx: $(BOOTDIR)/pa_ocaml_prelude.ml $(BOOTDIR)/pa_ast.cmx charset.cmx input.cmx decap.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_ocaml.cmx: $(BOOTDIR)/pa_ocaml.ml $(BOOTDIR)/pa_ocaml_prelude.cmx decap.cmxa
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_parser.cmx: $(BOOTDIR)/pa_parser.ml $(BOOTDIR)/pa_ocaml_prelude.cmx $(BOOTDIR)/pa_ast.cmx  $(BOOTDIR)/compare.cmx decap.cmxa $(BOOTDIR)/iter.cmx $(BOOTDIR)/quote.cmx decap.cmxa
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_main.cmx: $(BOOTDIR)/pa_main.ml input.cmi input.cmx $(BOOTDIR)/pa_ocaml.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/decap_ocaml.cmxa: $(BOOTDIR)/compare.cmx $(BOOTDIR)/iter.cmx $(BOOTDIR)/pa_ast.cmx $(BOOTDIR)/quote.cmx $(BOOTDIR)/pa_ocaml_prelude.cmx $(BOOTDIR)/pa_parser.cmx $(BOOTDIR)/pa_ocaml.cmx $(BOOTDIR)/pa_main.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) -a -o $@ $^

$(BOOTDIR)/decap_ocaml.cma: $(BOOTDIR)/compare.cmo $(BOOTDIR)/iter.cmo $(BOOTDIR)/pa_ast.cmo $(BOOTDIR)/quote.cmo $(BOOTDIR)/pa_ocaml_prelude.cmo $(BOOTDIR)/pa_parser.cmo $(BOOTDIR)/pa_ocaml.cmo $(BOOTDIR)/pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) -a -o $@ $^

$(BOOTDIR)/pa_default.cmo: $(BOOTDIR)/pa_default.ml $(BOOTDIR)/pa_ocaml_prelude.cmo $(BOOTDIR)/pa_parser.cmo $(BOOTDIR)/pa_ocaml.cmo $(BOOTDIR)/pa_main.cmo
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_default.cmx: $(BOOTDIR)/pa_default.ml $(BOOTDIR)/pa_ocaml_prelude.cmx $(BOOTDIR)/pa_parser.cmx $(BOOTDIR)/pa_ocaml.cmx $(BOOTDIR)/pa_main.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_ast.cmi $(BOOTDIR)/pa_ast.cmo: $(BOOTDIR)/pa_ast.ml
	$(OCAMLC) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

$(BOOTDIR)/pa_ast.cmx: $(BOOTDIR)/pa_ast.ml
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC) -I $(BOOTDIR) -c $<

pa_ocaml: decap.cmxa $(BOOTDIR)/decap_ocaml.cmxa $(BOOTDIR)/pa_default.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) $(COMPILER_INC)  -I $(BOOTDIR) -o $@ unix.cmxa str.cmxa $(COMPILER_LIBO) $^

endif

boot: BACKUP:=$(BOOTDIR)/$(shell date +%Y-%m-%d-%H-%M-%S)
boot:
	- if [ ! -d $(BOOTDIR) ] ; then mkdir $(BOOTDIR); fi
	- if [ ! -d $(BACKUP) ] ; then \
	     mkdir $(BACKUP) ; \
	     cp $(BOOTDIR)/*.ml $(BACKUP) ; \
	fi
	export OCAMLVERSION=$(OCAMLVERSION); \
	./pa_ocaml --ascii pa_ocaml_prelude.ml > $(BOOTDIR)/pa_ocaml_prelude.ml ;\
	./pa_ocaml --ascii pa_parser.ml > $(BOOTDIR)/pa_parser.ml ;\
	./pa_ocaml --ascii pa_ocaml.ml > $(BOOTDIR)/pa_ocaml.ml ;\
	./pa_ocaml --ascii pa_ast.ml > $(BOOTDIR)/pa_ast.ml ;\
	./pa_ocaml --ascii pa_main.ml > $(BOOTDIR)/pa_main.ml ;\
	./pa_ocaml --ascii pa_default.ml > $(BOOTDIR)/pa_default.ml

opam: opam.tmpl
	sed -e s/__VERSION__/$(VERSION)/g $< > $@

install: uninstall $(INSTALLED)
	install -m 755 -d $(DESTDIR)/$(LIBDIR)
	install -m 755 -d $(DESTDIR)/$(BINDIR)
	ocamlfind install -destdir $(DESTDIR)/$(dir $(LIBDIR)) decap META $(INSTALLED)
	install -m 755 pa_ocaml $(DESTDIR)/$(BINDIR)

uninstall:
	ocamlfind remove -destdir $(DESTDIR)/$(dir $(LIBDIR)) decap
	rm -rf $(DESTDIR)/$(LIBDIR)
	rm -f $(DESTDIR)/$(BINDIR)/pa_ocaml

clean:
	- rm -f *.cm* *.o *.a
	- rm -f bootstrap/*/*.cm* bootstrap/*/*.o bootstrap/*/*.a
	$(MAKE) -e -j 1 -C ast_tools clean

distclean: clean
	- rm -f pa_ocaml pa_ocaml.byt *~ \#*\#
	$(MAKE) -e -j 1 -C ast_tools distclean

doc: decap.mli charset.mli input.mli
	mkdir -p html
	ocamldoc -d html -html decap.mli charset.mli input.mli
