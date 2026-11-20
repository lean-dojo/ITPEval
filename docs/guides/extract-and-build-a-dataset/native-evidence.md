# Native evidence by prover

Extraction bundles share declaration, context and dependency files. Use the run's `report.json` to find evidence produced by the native adapter.

## Lean 4

For Lean theorems with a parser-resolved `:=` body, the structure keyed by declaration ID contains the exact half-open UTF-8 proof interval. The stored source hash lets a client recover the original proof expression. Generated theorems and declarations whose original command cannot be reparsed may have no proof-region entry. The executable completion task still uses its reviewed edit policy.

## Isabelle/HOL

For Isabelle, native `Term_XML.Encode.term_raw` records each proposition and kernel hypothesis in YXML, including binders, constants, variable indexes and types. Constant signatures use the matching native type encoding. Statement references to constants and theorem dependencies carry distinct relations.

## HOL Light

For HOL Light, the inspector queries typed OCaml theorem bindings at entry to and exit from nested project loads. A declaration preceding a mid-file import receives only the earlier bindings. The supported definition-registration entry points are `new_definition` and `new_basic_definition`. A named defining theorem links to its introduced constant and carries the kernel conclusion and hypotheses. Definitions created without an exported theorem binding have no declaration row in this binding view.

## HOL4

For HOL4, the extractor builds the theory with Holmake and reads the exported names, conclusions, hypotheses and typed terms from the native theorem database. Its reconstructed context includes public declarations from imported theories and earlier source lines. Private declarations get records of their own without entering later public contexts. [HOL4 libraries and project layout](../../provers/hol4.md#libraries)

## PVS

For PVS, each declaration structure identifies the parameters of the enclosing theory and the declaration's own arguments. Native declaration-reference edges retain the originating module and source position to disambiguate overloaded identifiers. Instantiating a parameterized theory makes its exported declarations available while leaving its formal parameters inside the original theory.

## Rocq

The Rocq fixture compiles the upstream Stdlib `StrictProp.v` and records the compiler's byte ranges for each vernacular command. Under `<file>#goals`, the native RocqIDE trace retains focused goals, the background focus stack, shelved goals and given-up goals. A declaration from an aborted proof has a trace and a skip reason when it is absent from the final library.

## Agda

For Agda, the `<file>#interaction` structure contains visible and invisible metas, diagnostic errors and constraints from the interaction protocol. The default extractor rejects unresolved goals. To inspect a module that permits unsolved metas, prepare it with `checking_profile="inspect_incomplete"`. Its declaration status reports `incomplete_module` whenever that module still contains goals or constraints.

## ACL2

For ACL2, events replayed from the entrypoint carry native `used_runes` and a content hash for the theory enabled immediately before the event. The supplied project also includes a byte-identical copy of the certified system book `std/lists/append`. The extractor matches its public events to entries in the ACL2 world. Rule-use labels for those imported events remain unavailable.

## Mizar

For Mizar, the upstream REAL_1 fixture supplies three checked registrations and six constructor redefinitions. The native XML, article index and accommodated theorem dictionary are available by source path in `report.json`. For an explicit justification, the edge names the referenced local label or MML theorem or definition, such as `XREAL_0:def 1`. The declaration context limits imported objects to the roles named in the article's environment.

## Metamath

For the Metamath project, `report.json` maps the declaration ID for `a1i` to a proof trace. Each transition records the proof label or compressed save/recall operation, stack height before and after the step, and the expression at the top of the stack. The parser checks substitution and disjointness against the active hypotheses. Metamath also verifies the assembled database. The project contains the dependency closure of the original set.mm proof and a separate disjoint-variable example. [Metamath proof of a1i](https://us.metamath.org/mpeuni/a1i.html)

See [backend capabilities](../../reference/capabilities.md) for the fields supported by each adapter.
