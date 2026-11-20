# Reuse check and dependency results

<span id="reuse-work-across-checks"></span>

Keep a `PreparedProject` for checks against the same source and imports. Each `verify` call stages locked inputs in a fresh workspace. Set `retain_dir` to keep it for debugging.

Use `verify_cached` for identical submissions and read `cache_hit`. Every lookup validates the lock. Validation reuses hashes for stable files and rereads recently modified files. A changed proof gets its own native check and can reuse compiled or verified dependencies where supported. [Python example](../../reference/python.md#reuse-an-identical-check) · [Cache timings](../measurements/startup-and-caching.md#loading-a-project-and-reusing-a-verification-result)

## Reuse compiled HOL4 dependencies

`itpeval.backends.hol4.theories.prepare_theories(prepared, source_files)` builds selected HOL4 dependency theories and keys the build by environment ID and scripts. HOL4 embeds absolute paths, so the build stays in a stable directory. Call `build.stage(prepared, attempt_workspace)` to validate and copy the compiled objects into a private dependency directory and obtain Holmake flags. Keep the editable target separate from those dependencies. [HOL4 timings](../measurements/startup-and-caching.md#reusing-dependencies-for-a-changed-candidate) · [Native trial data](../../../benchmarks/runtime/hol4-theories.json)

```sh
# Build and reuse the compiled HOL4 theory for this workload.
PYTHONPATH=. python benchmarks/runtime/hol4_theories.py --prefix "$ITPEVAL_PREFIX" \
    --cache /tmp/itpeval-hol-dependencies --output hol4-theories.json
```

## Fixed Metamath databases and ACL2 events

`itpeval.backends.metamath.base.prepare_base(prepared, "base.mm")` verifies a database and its transitive includes. The `VerifiedBase` return value identifies the cached receipt and records whether verification ran. Its key includes source hashes, the environment ID, the adapter and the tokenizer.

Pass `metamath_base="base.mm"` to `verify` when the client begins by including that exact base and adds one `$p` target. Local hypotheses and disjoint-variable conditions are supported. Extra includes, theorems or axioms use full verification. ITPEval compares the base with the locked bytes, checks the new proof natively and queries its transitive axioms. See `evidence_references` for a base receipt. The two paths were compared on two valid candidates and one invalid compressed proof. [Metamath trials](../../../benchmarks/runtime/evidence/metamath/native-interaction.json)

`itpeval.backends.acl2.interaction.replay_events(prepared, "events.lisp", names)` reconstructs an ACL2 book prefix in a fresh image. It records source ranges, world event numbers, stored events, symbol classes and rules for named top-level definitions and theorems in the ACL2 package with pinned system books. The trial follows a function, a guard-verified function, and a theorem that uses the definition. [ACL2 event trace](../../../benchmarks/runtime/evidence/acl2/native-interaction.json)
