# AlgGeom
Formalisation of Algebraic Geometry based on the HoTT library.

# Prequesites

Using `opam` you need `coq` and `coq-hott` at dev level.

The following will add the dev versions of `coq` and `coq-hott`:
```shell
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
Then to install run:
```shell
opam update
opam install coq-hott
```

# Building the library

To compile, run
```shell
dune build
```
