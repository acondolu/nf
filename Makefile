.PHONY: all clean
.DEFAULT_GOAL := all

COQC=/Applications/CoqIDE_8.11.0.app/Contents/Resources/bin/coqc

src/%.vos: src/%.v
	$(COQC) -R src "" $<

all: src/Untitled2.vos src/Quot.vos

clean:
	rm -f src/*.glob src/*.vo src/*.vok src/*.vos src/.*.aux
	