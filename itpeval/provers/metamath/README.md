# Metamath adapter

This directory contains the ITPEval adapter for the original Metamath C verifier.

Files:
- `install.sh`: downloads the official source tarball, builds `metamath`, and installs it under `ITPEVAL_PREFIX/metamath`.
- `check.sh`: reads and verifies the bundled hello database.
- `hello/hello.mm`: tiny database with one axiom and one proved theorem.

Defaults:
- Source tarball: `https://us.metamath.org/downloads/metamath.tar.gz`
- Install prefix: `ITPEVAL_PREFIX/metamath`

You can override the tarball URL with `ITPEVAL_METAMATH_URL`.
