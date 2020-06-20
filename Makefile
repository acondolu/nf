.PHONY: all clean remake coq coq-clean latex-clean coq-nf2 coq-nfo
.DEFAULT_GOAL := all

# SHELL=/bin/bash

all: coq CCP21/main.pdf

clean: coq-clean latex-clean

remake: clean all

# Coq

coq: coq-nf2 coq-nfo

coq-nf2: src/Model.vos src/Ext.vos src/Sets.vos src/ZF.vos src/Classp.vos
coq-nfo : src/NFO/Xor.vos src/NFO/Aux.vos src/NFO/FunExt.vos src/NFO/Bool.vos src/NFO/Model.vos src/NFO/Wff.vos src/NFO/Eeq.vos src/NFO/Iin.vos src/NFO/Sets.vos src/NFO/Ext.vos

src/NFO/%.vos: src/NFO/%.v
	coqc -R src/NFO "" $<

src/%.vos: src/%.v
	coqc -R src "" $<

coq-clean:
	rm -f src/**/*.glob src/**/*.vo src/**/*.vok src/**/*.vos src/**/.*.aux src/**/*.html src/**/*.css

coq-doc: # NFO-only!
	cd src/NFO/ && coqdoc --parse-comments -l *.v

# LaTeX

CCP21/main.pdf:
	cd CCP21 && latexmk main.tex -pdf

latex-clean:
	cd CCP21 && rm -f *.cut *.aux *.fdb-latexmk *.fls *.out *.pdf *.synctex.gz
