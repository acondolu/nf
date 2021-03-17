SHELL := /bin/bash
.PHONY: coq coq-clean coq-nf2 coq-nfo coq-common coq-doc
.DEFAULT_GOAL := all

coq: coq-common coq-nf2 coq-nfo

coq-common: src/Internal/Misc.vos src/Internal/List.vos src/Internal/WfMult.vos src/Internal/WfDecr.vos src/Internal/WfTuples.vos src/Internal/FunExt.vos src/Internal/Common.vos
coq-nf2: src/NF2/Model.vos src/NF2/Ext.vos src/NF2/Sets.vos
coq-nfo : src/NFO/Xor.vos src/NFO/BoolExpr.vos src/NFO/Model.vos src/NFO/Wf.vos src/NFO/Eq.vos src/NFO/In.vos src/NFO/Morphism.vos src/NFO/Sets.vos src/NFO/Ext.vos src/NFO/Union.vos src/Main.vos

src/Internal/%.vos: src/Internal/%.v
	coqc -R src "" $<

src/NFO/%.vos: src/NFO/%.v
	coqc -R src "" $<

src/NF2/%.vos: src/NF2/%.v
	coqc -R src "" $<

src/%.vos: src/%.v
	coqc -R src "" $<

coq-clean:
	rm -f src/{,**/}*.glob src/{,**/}*.vo src/{,**/}*.vok src/{,**/}*.vos src/{,**/}.*.aux
	rm -rf doc

coq-doc: coq
	rm -rf doc
	mkdir doc
	coqdoc --lib-subtitles -d doc -R "src" "" --verbose --utf8 src/{,**/}*.v


latex-clean:
	cd CCP21 && rm -f *.cut *.aux *.fdb-latexmk *.fls *.out *.pdf *.synctex.gz
