# Provers

This release has ten native adapters:

- [lean4](lean4/)
- [rocq](rocq/)
- [isabelle](isabelle/)
- [hol-light](hol-light/)
- [acl2](acl2/)
- [agda](agda/)
- [hol4](hol4/)
- [metamath](metamath/)
- [mizar](mizar/)
- [pvs](pvs/)

Each directory provides `adapter.json`, `install.sh`, `check.sh`, `version.sh`,
and source files under `hello/`. See [the harness guide](../README.md) for
installation, platform limitations, and one-file evaluation. Native statement
acceptance is separate from BEq; the public BEq implementation remains Lean-only.
