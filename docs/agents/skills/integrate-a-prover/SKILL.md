---
name: integrate-a-prover
description: Connect a new theorem prover to ITPEval and establish which native operations work, starting with a command-line checker and an independently verifiable fixture.
---

# Integrate a prover

Run from an ITPEval checkout. For an installed copy of this skill, resolve the guide links from `docs/agents/skills/integrate-a-prover/SKILL.md` in that checkout.

## Start with a native checker

1. Identify the checker command, its input files, and its success verdict. Run it directly on one valid and one invalid input. For a detached certificate, hold the original problem fixed and pass it alongside each certificate.
2. Use `examples/prover-adapters/sprig` as a template. Give the adapter its own ID, place a valid example under `hello/`, and set `ITPEVAL_ADAPTER_DIR` to the absolute path of its parent directory. In `check.sh`, read `ITPEVAL_TASK_DIR` and `ITPEVAL_TASK_FILE`, then preserve the native exit status and diagnostics. [Connect a native checker](../../../reference/extending-a-backend.md#connect-a-native-checker-to-the-cli)
3. Run `./itpeval/bin/itpeval check --task hello PROVER` on the valid fixture. Check the invalid input with `run_itp(prover=..., task_dir=..., task_file=...)`. Report the checked inputs, diagnostics, and verdicts. [Sprig checker example](../../sprig.md#run-it-through-itpeval)

## Add task verification or extraction when needed

For a separate JSON, text, or binary certificate, add `typed-adapter.json` and a reviewed manifest. Use `itpeval prepare` and `itpeval verify-task` on the locked target. Test an invalid certificate, a changed fixed source, and a missing checker receipt. Record each result. [Detached certificate integration](../../../reference/extending-a-backend.md#add-verification-for-a-detached-certificate)

If the adapter also has an extractor, run `itpeval dataset` on the known target and compare the extracted proof references with the checker receipt. For operations beyond the external adapter protocol, implement and verify the supported operations in a bundled backend. [Add extraction and backend operations](../../../reference/extending-a-backend.md#add-declaration-extraction)
