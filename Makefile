COQMAKEFILE=CoqMakefile
LIBNAME=cbpv
SYNTAX=$(shell ls */syntax.sig */*/syntax.sig)
SYNTAXV=$(patsubst %.sig,%.v,$(SYNTAX))

.PHONY: coq syntax clean fullclean


# compile all .v files in _CoqProject
coq: CoqSrc.mk $(VFILES)
	make -f CoqSrc.mk

CoqSrc.mk: _CoqProject
	 coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module,-notation-overridden' -f _CoqProject -o CoqSrc.mk

# Remove compiled files
clean:
	make -f CoqSrc.mk clean


syntax:	$(SYNTAXV)

# Generate the syntax.v files with Autosubst 2 and add imports
# This will run Autosubst 2 and add_imports_to_syntax.pl.
%/syntax.v: %/syntax.sig Makefile
	as2-exe -i $< -p Coq > $@
	perl add_imports_to_syntax.pl $@


# Generate syntax files and compile all .v files
# This will run Autosubst 2 and add_imports_to_syntax.pl.
fullmake: _CoqProject coq

# Generate syntax.v files and add all .v files to _CoqProject
# This will run Autosubst 2 and add_imports_to_syntax.pl.
_CoqProject : syntax
	{ echo "-R . $(LIBNAME) " ; ls autosubst2/*.v common/*.v general/*.v */CBPV/*.v */CBV/*.v */CBN/*.v ; } > _CoqProject

# Remove compiled files and also remove
# the Autosubst-2-generated syntax.v files and auxiliary make files
# Regenerating syntax.v files will run Autosubst 2 and add_imports_to_syntax.pl.
fullclean: clean
	rm -f $(SYNTAXV)
	rm -f .CoqSrc.mk.d CoqSrc CoqSrc.conf CoqSrc.mk CoqSrc.mk.conf
	rm -f _CoqProject

%.vo: %.v CoqSrc.mk
	make -f CoqSrc.mk $*.vo

vos:  CoqSrc.mk
	@make -f CoqSrc.mk vos

%.vos:  %.v CoqSrc.mk
	@make -f CoqSrc.mk $*.vos
