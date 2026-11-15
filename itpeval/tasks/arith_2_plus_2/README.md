# arith_2_plus_2

Shared `2 + 2 = 4` smoke artifacts for all ten release adapters.

- `lean4/Hello.lean`
- `rocq/hello.v`
- `isabelle/ROOT`
- `hol-light/hello.ml`
- `acl2/hello.lsp`
- `agda/Hello.agda`
- `hol4/helloScript.sml`
- `metamath/hello.mm`
- `mizar/text/hello.miz`
- `pvs/hello.pvs`

Run `./itpeval/bin/itpeval check --task arith_2_plus_2 <provers>` from the
repository root. `--task hello` selects each adapter's built-in example instead.
