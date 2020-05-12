.PHONY: all clean ci remake
.DEFAULT_GOAL := all

ifndef COQC
COQC=/Applications/CoqIDE_8.11.0.app/Contents/Resources/bin/coqc
endif

src/%.vos: src/%.v
	$(COQC) -R src "" $<

all: src/Base.vos src/Lifting.vos src/Top.vos

ci: src/Base.vos src/Lifting.vos src/Top.vos

clean:
	rm -f src/*.glob src/*.vo src/*.vok src/*.vos src/.*.aux

remake: clean all

remake2: clean src/Base2.vos