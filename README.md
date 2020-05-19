# nf [![Build Status](https://travis-ci.com/acondolu/nf.svg?branch=master)](https://travis-ci.com/acondolu/nf)

This repository contains the formalisation in Coq of a basic set theory with universal set. It started as an investigation into the (possible) consistency of Quine's [New Foundations](https://plato.stanford.edu/entries/quine-nf/), but of course, settled on a much weaker theory 😉

- `Model.v` defines the model, set equality, and set membership. It proves that equality is an equivalence relation, and that it is sound w.r.t. set membership.
- `Sets.v` defines singleton, set complement, union, and intersection.
- `Ext.v` proves extensionality of sets.
- `ZF.v` proves some axioms of Zermelo-Fraenkel set theory.
  Some are falsified altogether (like regularity), some hold (like pairing, union, infinity), some hold only for so-called _positive_ sets (comprehension, replacement, powerset).

### Compiling
Just type `make`. The `coqc` executable is required.

---

© acondolu 2020