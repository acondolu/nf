# nf [![Build Status](https://travis-ci.com/acondolu/nf.svg?branch=master)](https://travis-ci.com/acondolu/nf)

This repository contains the formalisation in Coq of a basic set theory with universal set. It started as an investigation into the (alleged) consistency of Quine's [New Foundations](https://plato.stanford.edu/entries/quine-nf/), but of course, settled on a much weaker theory 😉

The set theory that we consider here is known as _NF<sub>2</sub>_, and the model that we provide is basically a Church-Oswald model, encoded similarly as one usually does for ZF (see https://github.com/coq-contribs/zfc).

The basic operations of NF<sub>2</sub> are the empty set, singletons, unions, intersections, and complement. The usual operations of ZF, like comprehension and powerset, are allowed only for so-called _low_ sets, which correspond to the usual understanding of sets as collections of given sets.

### Structure
- `Model.v` defines the model, set equality, and set membership. It proves that equality is an equivalence relation, and that it is sound w.r.t. set membership.
- `Sets.v` defines singleton, set complement, union, and intersection.
- `Ext.v` proves extensionality of sets.
- `ZF.v` proves some axioms of Zermelo-Fraenkel set theory.
  Some are falsified altogether (like regularity), some hold (like pairing, union, infinity), some hold only for low_ sets (comprehension, replacement, powerset).

### Compiling
Just type `make`. The `coqc` executable is required.

### References
- Thomas Forster, Church's Set Theory with a Universal Set. https://www.dpmms.cam.ac.uk/~tf/church2001.pdf

---

© acondolu 2020