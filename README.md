Coq Formalization for Mininix
=============================

[![License](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.12208115.svg)](https://doi.org/10.5281/zenodo.12208115)

Mininix is a smaller version of the Nix expression language. This codebase
provides the mechanization of the semantics and reference interpreter for this
language in the [Coq](https://coq.inria.fr/) proof assistant. For more details,
I refer to my bachelor's thesis. It should be linked to from the related work
section of the [Zenodo record](https://zenodo.org/records/12208115) after it
has been made available on the [thesis
archive](https://www.cs.ru.nl/bachelors-theses/) page of
[iCIS](https://www.ru.nl/en/institute-for-computing-and-information-sciences).

## Development

During my thesis, I used Nix to manage my Coq installation. If you use Nix, it
should be easy to build/check the codebase. If not, this might be a bit more
tricky.

There are two things that you need to have installed. The current `flake.lock`
ensures that we have the following software:

- Coq, version 8.19.2.
- [Coq-std++](https://gitlab.mpi-sws.org/iris/stdpp), version 1.10.0.

### Using Nix

I have attached a `flake.nix` and `flake.lock` file, which should make my setup
reproducible. Assuming a working Nix installation with flake support and the
Nix command enabled, simply running `nix develop` should give you a shell where
the right Coq and Coq-std++ versions available.

If you have a working [direnv](https://direnv.net/) installation, simply
running `direnv allow` (after inspecting the `.envrc` file) should make the
right version of Coq and Coq-std++ available.

### Without Nix

If you are on some Unix-based system, there is a good chance that your package
manager provides a Coq package. [The Repology
page](https://repology.org/project/coq/versions) should give you the
information that you need.

You may be able to install Coq-std++ via opam, as described in the README of
Coq-std++. However, your operating system's package repositories may also
provide a package. Consider taking a look at the Repology pages:
[coq-stdpp](https://repology.org/project/coq-stdpp/versions),
[coq:stdpp](https://repology.org/project/coq:stdpp/versions).

## Building/checking

Running `make` should run `coqc` on all files; assuming that you are using a
compatible Coq version, this should successfully check all proofs.
