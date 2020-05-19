.PHONY: all clean ci remake
.DEFAULT_GOAL := all

# Workaround for acondolu's custom coqc path
COQC=`[[ $(hash coqc 2>/dev/null ; echo $?) -eq 0 ]] && echo 'coqc' || echo '/Applications/CoqIDE_8.11.0.app/Contents/Resources/bin/coqc'`

src/%.vos: src/%.v
	$(COQC) -R src "" $<

all: src/Model.vos src/Ext.vos src/Sets.vos src/ZF.vos

ci: all

clean:
	rm -f src/*.glob src/*.vo src/*.vok src/*.vos src/.*.aux

remake: clean all
