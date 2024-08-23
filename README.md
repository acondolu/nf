# nf <img src="https://github.com/acondolu/nf/actions/workflows/workflow.yml/badge.svg?branch=CPP22">

This repository contains the formalisation in Coq of a basic set theory with universal set. It started as an investigation into the consistency of Quine's [New Foundations](https://plato.stanford.edu/entries/quine-nf/), but in the end settled on a much weaker theory 😉 (Note 2024: the consistency of full NF has been finally settled by [Randall Holmes and Sky Wilshaw](https://randall-holmes.github.io/Nfproof/maybedetangled2.pdf))

The set theory that we consider here is known as _NF<sub>2</sub>_, and the model that we provide is basically a Church-Oswald model, using an encoding inspired by the historic encoding of ZF in Coq by Aczel (see https://github.com/coq-contribs/zfc).

The basic operations of NF<sub>2</sub> are the empty set, singletons, unions, intersections, and complement. The usual operations of ZF, like comprehension and powerset, are allowed only for so-called _low_ sets, which correspond to the usual understanding of sets as collections of given sets.

### Structure
- `Model.v` defines the model, set equality, and set membership. It proves that equality is an equivalence relation, and that it is sound w.r.t. set membership.
- `Sets.v` defines singleton, set complement, union, and intersection.
- `Ext.v` proves extensionality of sets.
- `ZF.v` proves some axioms of Zermelo-Fraenkel set theory.
  Some are falsified altogether (like regularity), some hold (like pairing, union, infinity), some hold only for low  sets (comprehension, replacement, powerset).

### Building
Tested with Coq version 8.13.1.

- `make coq` to build
- `make coq-doc` to build the documentation
- `make coq-clean` to clean up

### References
- Thomas Forster, Church's Set Theory with a Universal Set. https://www.dpmms.cam.ac.uk/~tf/church2001.pdf
