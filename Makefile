SHELL := /bin/bash
.PHONY: all clean remake coq coq-clean latex-clean coq-nf2 coq-nfo coq-common coq-doc
.DEFAULT_GOAL := all

# SHELL=/bin/bash

all: coq CCP21/main.pdf

clean: coq-clean latex-clean

remake: clean all

# Coq

coq: coq-common coq-nf2 coq-nfo

coq-common: src/Internal/Aux.vos src/Internal/FunExt.vos
coq-nf2: src/NF2/Model.vos src/NF2/Ext.vos src/NF2/Sets.vos src/NF2/ZF.vos src/NF2/Classp.vos
coq-nfo : src/NFO/Xor.vos src/NFO/BoolExpr.vos src/NFO/Model.vos src/NFO/Wff.vos src/NFO/Eeq.vos src/NFO/Iin.vos src/NFO/Sets.vos src/NFO/Morphs.vos src/NFO/Ext.vos src/NFO/Union.vos src/NFO/Main.vos

src/Internal/%.vos: src/Internal/%.v
	coqc -R src "" $<

src/NFO/%.vos: src/NFO/%.v
	coqc -R src "" $<

src/NF2/%.vos: src/NF2/%.v
	coqc -R src "" $<

coq-clean:
	rm -f src/**/*.glob src/**/*.vo src/**/*.vok src/**/*.vos src/**/.*.aux
	rm -rf doc

coq-doc: coq # NFO-only!
	rm -rf doc
	mkdir doc
	coqdoc --light --lib-subtitles -d doc -R "src" "" --verbose --utf8 src/**/*.v

# LaTeX

CCP21/main.pdf:
	cd CCP21 && latexmk main.tex -pdf

latex-clean:
	cd CCP21 && rm -f *.cut *.aux *.fdb-latexmk *.fls *.out *.pdf *.synctex.gz
