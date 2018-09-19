VERSION    = 1.0.2
OCAMLFIND  = ocamlfind
J          = 1
OCAMLBUILD = ocamlbuild -j $(J)
BINDIR     = $(dir $(shell which ocamlc))

HAS_PA_OCAML=$(shell if [ -x pa_ocaml ]; then echo 1; else echo 0; fi)
OCAMLVERSION=$(shell ocamlc -version | sed s/+.*//)
BOOTDIR=./bootstrap/$(OCAMLVERSION)
ASTTOOLS=ast_tools
ASTDIR=$(ASTTOOLS)/$(OCAMLVERSION)
ASTHELP=ast_helper
HELPDIR=$(ASTHELP)/$(OCAMLVERSION)

PACKAGES  = earley,earley.str,unix,str,compiler-libs
LINKFLOGS = -lflags -I,+compiler-libs,ocamlbytecomp.cmxa,ocamlcommon.cmxa
LINKFLAGS = -lflags -I,+compiler-libs,ocamlbytecomp.cma,ocamlcommon.cma

INSTALLED = _build/*.cm* _build/*.a
PA_OCAML=`pwd`/pa_ocaml

BOOT=1
Q=@

ifeq ($(HAS_PA_OCAML),1)
PP= -pp "$(PA_OCAML) $(ASCII)"
all: pa_ocaml earley_ocaml.cmxa earley_ocaml.cma
else
PP=
all: cold
endif

SRCS=pa_default.ml pa_main.ml pa_ocaml_prelude.ml pa_parser.ml\
     pa_ast.ml pa_lexing.ml pa_ocaml.ml

ASTML=compare.ml iter.ml quote.ml
HLPML=helper.ml helper.mli astextra.ml astextra.mli

.PHONY: cold
cold:
	@printf "\033[93mCOMPILING FROM $(BOOTDIR)\033[0m\n"
	$(Q)cd $(BOOTDIR); \
	$(OCAMLBUILD) -use-ocamlfind -pkgs $(PACKAGES) $(LINKFLOGS) pa_default.native
	cp -f $(BOOTDIR)/pa_default.native pa_ocaml

helper.mli: $(ASTHELP)/helper.mli
	cp $< $@
helper.ml: $(HELPDIR)/helper.ml
	cp $< $@
astextra.mli: $(HELPDIR)/astextra.mli
	cp $< $@
astextra.ml: $(HELPDIR)/astextra.ml
	cp $< $@

pa_default.native: $(SRCS) $(ASTML) $(HLPML)
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -use-ocamlfind -pp $(PA_OCAML) -pkgs $(PACKAGES) $(LINKFLOGS) $@

pa_default.byte: $(SRCS) $(ASTML) $(HLPML)
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -use-ocamlfind -pp $(PA_OCAML) -pkgs $(PACKAGES) $(LINKFLAGS) $@

pa_ocaml: pa_default.native
	cp -f $< $@

earley_ocaml.cma: $(SRCS) $(ASTML) $(HLPML)
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -use-ocamlfind -pp $(PA_OCAML) -pkgs $(PACKAGES) earley_ocaml.cma

earley_ocaml.cmxa: $(SRCS) $(ASTML) $(HLPML)
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -use-ocamlfind -pp $(PA_OCAML) -pkgs $(PACKAGES) earley_ocaml.cmxa

test_parsers.native: earley_ocaml.cmxa test_parsers.ml
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -use-ocamlfind -pp $(PA_OCAML) -pkgs $(PACKAGES) $(LINKFLOGS) $@

$(ASTTOOLS)/pa_eq.native: $(ASTTOOLS)/pa_eq.ml
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -pp "$(PA_OCAML) --ascii" -pkgs $(PACKAGES) $(LINKFLOGS) $@
	$(Q)cp -f ./pa_eq.native $(ASTTOOLS)/ # avoid rebuild

compare.ml: $(ASTTOOLS)/pa_eq.native $(ASTTOOLS)/generic_eq.ml \
            $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	@printf "\033[93mGENERATING $@\033[0m\n"
	$(Q)$(PA_OCAML) --ascii $(ASTTOOLS)/generic_eq.ml > $@
	$(Q)printf "(* asttypes.mli *)\n" >> $@
	$(Q)./pa_eq.native $(ASTDIR)/asttypes.mli >> $@
	$(Q)printf "\n" >> $@
	$(Q)printf "(* parsetree.mli *)\n" >> $@
	$(Q)./pa_eq.native $(ASTDIR)/parsetree.mli >> $@

$(ASTTOOLS)/pa_iter.native: $(ASTTOOLS)/pa_iter.ml
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -pp "$(PA_OCAML) --ascii" -pkgs $(PACKAGES) $(LINKFLOGS) $@
	$(Q)cp -f ./pa_iter.native $(ASTTOOLS)/ # avoid rebuild

iter.ml: $(ASTTOOLS)/pa_iter.native $(ASTTOOLS)/generic_iter.ml \
         $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	@printf "\033[93mGENERATING $@\033[0m\n"
	$(Q)$(PA_OCAML) --ascii $(ASTTOOLS)/generic_iter.ml > $@
	$(Q)printf "(* asttypes.mli *)\n" >> $@
	$(Q)./pa_iter.native $(ASTDIR)/asttypes.mli >> $@
	$(Q)printf "\n(* parsetree.mli *)\n" >> $@
	$(Q)./pa_iter.native $(ASTDIR)/parsetree.mli >> $@

$(ASTTOOLS)/pa_quote.native: $(ASTTOOLS)/pa_quote.ml
	@printf "\033[93mBUILDING $@\033[0m\n"
	$(Q)$(OCAMLBUILD) -pp "$(PA_OCAML) --ascii" -pkgs $(PACKAGES) $(LINKFLOGS) $@
	$(Q)cp -f ./pa_quote.native $(ASTTOOLS)/ # avoid rebuild

quote.ml: $(ASTTOOLS)/pa_quote.native $(ASTTOOLS)/generic_quote.ml \
          $(ASTDIR)/parsetree.mli $(ASTDIR)/asttypes.mli
	@printf "\033[93mGENERATING $@\033[0m\n"
	$(Q)$(PA_OCAML) --ascii $(ASTTOOLS)/generic_quote.ml > $@
	@printf "(* asttypes.mli *)\n" >> $@
	$(Q)./pa_quote.native $(ASTDIR)/asttypes.mli >> $@
	@printf "\n(* parsetree.mli *)\n" >> $@
	$(Q)./pa_quote.native $(ASTDIR)/parsetree.mli >> $@

.PHONY: bootstrap
bootstrap:
	@printf "\033[93mBOOTSTRAP\033[0m\n"
	$(Q)if [ ! -d tmp ] ; then mkdir tmp; fi
	@printf "\033[93mMAIN FILES\033[0m\n"
	$(Q)export OCAMLVERSION=$(OCAMLVERSION); \
	     rm -rf tmp/* ;\
	     $(PA_OCAML) --ascii pa_lexing.ml > tmp/pa_lexing.ml ;\
	     $(PA_OCAML) --ascii pa_ocaml_prelude.ml > tmp/pa_ocaml_prelude.ml ;\
	     $(PA_OCAML) --ascii pa_parser.ml > tmp/pa_parser.ml ;\
	     $(PA_OCAML) --ascii pa_ocaml.ml > tmp/pa_ocaml.ml ;\
	     $(PA_OCAML) --ascii pa_ast.ml > tmp/pa_ast.ml ;\
	     $(PA_OCAML) --ascii pa_main.ml > tmp/pa_main.ml ;\
	     $(PA_OCAML) --ascii pa_default.ml > tmp/pa_default.ml

.PHONY: backup
backup: BACKUP:=$(BOOTDIR)/$(shell date +%Y-%m-%d-%H-%M-%S)
backup:
	$(Q)printf "\033[93mBACKUP $(BOOTDIR) IN $(BACKUP)\033[0m\n"
	$(Q)mkdir $(BACKUP)
	$(Q)cp $(BOOTDIR)/*.ml* $(BACKUP)

.PHONY: new
new:
	@printf "\033[93mCREATING FRESH BOOTSTRAP FOR $(OCAMLVERSION)\033[0m\n"
	$(Q)make bootstrap
	$(Q)OCAMLVERSION=$(OCAMLVERSION) make $(ASTML)
	$(Q)OCAMLVERSION=$(OCAMLVERSION) make $(HLPML)
	$(Q)if [ ! -d $(BOOTDIR) ] ; then mkdir $(BOOTDIR); fi
	$(Q)make backup
	$(Q)mv tmp/*.ml* $(BOOTDIR)

#BOOTSTRAP OF ONE VERSION (SEE all_boot.sh AND INSTALL opam FOR MULTIPLE OCAML VERSION
.PHONY: boot
boot:
	$(Q)make distclean && make
	$(Q)printf "\033[93mCOMPILING USING V1\033[0m\n"
	$(Q)make
	$(Q)printf "\033[93mCOMPILING USING V2\033[0m\n"
	$(Q)make clean && make
	$(Q)make bootstrap
	$(Q)printf "\033[93mHELPER AND ASTTOOLS\033[0m\n"
	$(Q)cp $(ASTML) $(HLPML) tmp/
	$(Q)touch .fixpoint
	$(Q)cd tmp/ ; for f in *.ml; do\
               if ! diff -q $$f ../$(BOOTDIR)/$$f; then rm ../.fixpoint; fi ;\
	     done
	$(Q)if [ ! -d $(BOOTDIR) ] ; then mkdir $(BOOTDIR); fi
	$(Q)if [ -f .fixpoint ]; then printf "\033[93mFIXPOINT REACHED\033[0m\n";\
	     elif [ $(BOOT) -eq 1 ] ; then \
	       make backup ;\
	       printf "\033[93mCOPYING TO $(BOOTDIR)\033[0m\n" ; \
	       cp -f tmp/*.ml $(BOOTDIR)/ ;\
	       rm -rf tmp ;\
	     fi

tests_pa_ocaml/$(OCAMLVERSION)/expected: pa_ocaml
	@printf "\033[93mCREATING $@\033[0m\n"
	$(Q)./tests_pa_ocaml.sh --no-color > $@

.PHONY: expected
expected: tests_pa_ocaml/$(OCAMLVERSION)/expected

.PHONY: tests
tests:
	@printf "\033[93mTEST FIXPOINT\033[0m\n"
	$(Q)make BOOT=0 boot
	$(Q)if [ ! -f .fixpoint ]; then \
	       printf "\033[93mFIXPOINT NOT REACHED\033[0m\n" ;\
	       exit 1; \
	     fi
	$(Q)printf "\033[93mREGRESSION TEST\033[0m\n"
	$(Q)./tests_pa_ocaml.sh --no-color > tests_pa_ocaml/$(OCAMLVERSION)/result
	$(Q)if ! diff tests_pa_ocaml/$(OCAMLVERSION)/result \
                       tests_pa_ocaml/$(OCAMLVERSION)/expected; then \
	       printf "\033[93mREGRESSION TESTS FAILED\033[0m\n" ;\
	       exit 1;\
	     fi
	$(Q)printf "\033[93mNO REGRESSION\033[0m\n"

META: GNUmakefile
	@printf "[GEN] $@\n"
	@echo 'name="earley_ocaml"'                                > $@
	@echo 'version="$(VERSION)"'                              >> $@
	@echo 'requires="compiler-libs.common,earley,earley.str"' >> $@
	@echo 'archive(native)="earley_ocaml.cmxa"'               >> $@
	@echo 'archive(byte)="earley_ocaml.cma"'                  >> $@

.PHONY: clean
clean:
	@printf "\033[93mCLEAN\033[0m\n"
	$(Q)$(OCAMLBUILD) -clean
	$(Q)rm -f $(ASTTOOLS)/*.native $(BOOTDIR)/*.native
	$(Q)cd $(BOOTDIR); $(OCAMLBUILD) -clean
	$(Q)$(MAKE) -e -j 1 -C doc/examples clean
	$(Q)if which patoline ; then cd doc; patoline --clean; fi
	$(Q)./tests_pa_ocaml.sh --clean

.PHONY: distclean
distclean: clean
	@printf "\033[93mDISTCLEAN\033[0m\n"
	$(Q)rm -f pa_ocaml .fixpoint $(ASTML) $(HLPML)
	$(Q)rm -f META
	$(Q)rm -rf tmp
	$(Q)find . -name "*~" -type f -exec rm {} \;
	$(Q)find . -name "#*" -type f -exec rm {} \;
	$(Q)find . -name ".#*" -type f -exec rm {} \;
	$(Q)$(MAKE) -e -j 1 -C doc/examples distclean
	$(Q)rm -f doc/doc.pdf

.PHONY: install
install: uninstall $(INSTALLED) META
	install -m 755 -d $(BINDIR)
	$(OCAMLFIND) install earley_ocaml META $(INSTALLED)
	install -m 755 pa_ocaml $(BINDIR)

.PHONY: uninstall
uninstall:
	$(OCAMLFIND) remove earley_ocaml
	rm -f $(BINDIR)/pa_ocaml

.PHONY: release
release: distclean
	git push origin
	git tag -a ocaml-earley-ocaml_$(VERSION)
	git push origin ocaml-earley-ocaml_$(VERSION)
