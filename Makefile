.PHONY: all clean ci remake
.DEFAULT_GOAL := all

# My local coqc patch
ifndef COQC
COQC=/Applications/CoqIDE_8.11.0.app/Contents/Resources/bin/coqc
endif

src/%.vos: src/%.v
	$(COQC) -R src "" $<

all: src/Tower.vos

ci: src/Tower.vos

clean:
	rm -f src/*.glob src/*.vo src/*.vok src/*.vos src/.*.aux

remake: clean all
