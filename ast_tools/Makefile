export OCAMLVERSION=$(shell ocamlc -version | sed s/+.*//)
PA_OCAML=../pa_ocaml
OCAMLOPT=ocamlfind ocamlopt -package unix,bytes,earley,earley.str

COMPILER_INC = -I +compiler-libs
COMPILER_LIBS = ocamlcommon.cma
COMPILER_PARSERS =
COMPILER_TOP = ocamlbytecomp.cma ocamltoplevel.cma
COMPILER_LIBO := $(COMPILER_LIBS:.cma=.cmxa)
COMPILER_LIBO := $(COMPILER_LIBO:.cmo=.cmx)
COMPILER_PARSERO := $(COMPILER_PARSERS:.cma=.cmxa)
COMPILER_PARSERO := $(COMPILER_PARSERO:.cmo=.cmx)

BOOTDIR := ../bootstrap/$(OCAMLVERSION)
ASTDIR  := ./ast-$(OCAMLVERSION)

all: pa_eq pa_quote $(BOOTDIR)/compare.ml $(BOOTDIR)/iter.ml $(BOOTDIR)/quote.ml

tests: all compare.cmx iter.cmx quote.cmx

debug:
	echo $(ASTDIR)
	echo $(BOOTDIR)

pa_eq: pa_eq.ml
	$(OCAMLOPT) -pp "$(PA_OCAML) --ascii" -I .. $(COMPILER_INC) $(COMPILER_LIBO) -o $@ pa_lexing.cmx -linkpkg $<

pa_iter: pa_iter.ml
	$(OCAMLOPT) -pp "$(PA_OCAML) --ascii" -I .. $(COMPILER_INC) $(COMPILER_LIBO) -o $@ pa_lexing.cmx -linkpkg $<

pa_quote: pa_quote.ml
	$(OCAMLOPT) -pp "$(PA_OCAML) --ascii" -I .. $(COMPILER_INC) $(COMPILER_LIBO) -o $@ pa_lexing.cmx -linkpkg $<

# FIXME target construction does not fail if pa_eq fails...
$(BOOTDIR)/compare.ml: pa_eq generic_eq.ml $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	$(PA_OCAML) --ascii generic_eq.ml > $@
	@echo "(* asttypes.mli *)" >> $@
	./pa_eq $(ASTDIR)/asttypes.mli >> $@
	@echo "" >> $@
	@echo "(* parsetree.mli *)" >> $@
	./pa_eq $(ASTDIR)/parsetree.mli >> $@

# FIXME target construction does not fail if pa_eq fails...
$(BOOTDIR)/iter.ml: pa_iter generic_iter.ml $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	$(PA_OCAML) --ascii generic_iter.ml > $@
	@echo "(* asttypes.mli *)" >> $@
	./pa_iter $(ASTDIR)/asttypes.mli >> $@
	@echo "" >> $@
	@echo "(* parsetree.mli *)" >> $@
	./pa_iter $(ASTDIR)/parsetree.mli >> $@

# FIXME target construction does not fail if pa_quote fails...
$(BOOTDIR)/quote.ml: pa_quote generic_quote.ml $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	$(PA_OCAML) --ascii generic_quote.ml > $@
	@echo "(* asttypes.mli *)" >> $@
	./pa_quote $(ASTDIR)/asttypes.mli >> $@
	@echo "" >> $@
	@echo "(* parsetree.mli *)" >> $@
	./pa_quote $(ASTDIR)/parsetree.mli >> $@

compare.cmx: $(BOOTDIR)/compare.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

compare.cmo: $(BOOTDIR)/compare.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

iter.cmx: $(BOOTDIR)/iter.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

iter.cmo: $(BOOTDIR)/iter.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

quote.cmx: $(BOOTDIR)/quote.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

quote.cmo: $(BOOTDIR)/quote.ml
	$(OCAMLOPT) -c $(COMPILER_INC) $(COMPILER_LIBO) $<

clean:
	rm -f *.cmi *.cmx *.cmo *.cma *.cmxa *.o

distclean: clean
	rm -f pa_eq pa_quote pa_iter
