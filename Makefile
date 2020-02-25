.PHONY: all clean
.DEFAULT_GOAL := all

COQC=/Applications/CoqIDE_8.11.0.app/Contents/Resources/bin/coqc

all:
	$(COQC) -R src "" src/Untitled2.v

clean:
	rm -f src/*.glob src/*.vo src/*.vok src/*.vos src/.*.aux
	