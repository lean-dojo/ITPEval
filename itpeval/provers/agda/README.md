# Agda adapter

Files:
- `install.sh`: installs (or wires) `agda` under `ITPEVAL_PREFIX/agda` and links it into `ITPEVAL_PREFIX/bin/agda`.
- `check.sh`: typechecks `hello/Hello.agda`.
- `hello/Hello.agda`: minimal module used for the smoke test.

Notes:
- On this machine we generally install Agda via `ghcup` + `cabal` (this can take a while).
