# Add a prover backend

Start by teaching ITPEval how to check a native file. Add proof completion when you can identify a named theorem and verify the edited proof against it. Add library extraction when the prover can tell you about its declarations and their context. A native goal or tactic API can come later.

## Connect a native checker to the CLI

For an example you can run, start with Sprig. It has a small propositional checker with a proof certificate and scripts for installing, versioning and checking. Each custom adapter gets a subdirectory named after its prover ID. Set `ITPEVAL_ADAPTER_DIR` to the absolute path of the parent directory. Both the CLI and `run_itp` look there. Bundled IDs take precedence when names coincide. The checker runs as your user, so choose a directory whose code you trust. [Run the Sprig adapter](../agents/sprig.md)

Give your adapter a `check.sh` that invokes the native checker and passes its exit status back to ITPEval. Put a small valid input under `hello/`. With the custom adapter path set and the checker installed, run the following from the checkout, replacing `my-prover` with the directory name.

```bash
# Check the adapter's own hello fixture with its native checker.
./itpeval/bin/itpeval check --task hello my-prover
```

Look for one successful check in the summary. Then try a file the native checker should reject. The default arithmetic task can report a skip until you add a fixture for it.

## Add verification for a detached certificate

A prover with a separate certificate can use typed tasks from its own adapter directory. Add `typed-adapter.json` with schema version `1`, your prover `id`, a `version`, the relative path to its `checker`, and any `inputs` the checker loads. Add `extractor` when the prover can emit declarations. The environment lock fingerprints the descriptor, scripts, declared inputs, and Python interpreter. The adapter command uses the interpreter in isolated mode with the standard library. Prepare the project and reload its lock with `ITPEVAL_ADAPTER_DIR` pointing at the trusted adapter directory. [Sprig's descriptor](../../examples/prover-adapters/sprig/typed-adapter.json) · [Run the complete workflow](../agents/sprig.md#verify-a-locked-task-and-extract-it)

In the project, write a `completion.json` using `DetachedCompletionManifest`. Include the `source_path`, `proof_file`, and both in `files`. Give the named `target`, its `statement`, and a unique source `anchor`. List the assumption names the checker may use in `allowed_assumptions`. Supply any additional fixed project artifacts in `files`. During an attempt, ITPEval stages the fixed inputs and inserts the candidate in the certificate file. [Sprig's completion manifest](../../examples/prover-adapters/sprig/hello/completion.json)

Set `certificate_format` to `json`, `text`, or `binary`. The default is `json`. `verify-task --candidate-file` reads the file directly. In Python, pass bytes to `verify_document`, or call `candidate_from_bytes(task, data)` to get the string used by `verify`, checkpoints, and proof episodes. Binary candidates use canonical Base64 in those records. The checker receives the original bytes. [Native DRAT example](#check-native-drat-certificates)

Your checker gets `--request FILE` and runs inside the staged project. It should establish the target in the fixed source, then run your kernel on that target and the submitted certificate. Write a `DetachedProofReceipt` as one JSON object on stdout. Include the request’s task, environment, and artifact IDs. Supply the observed target and the SHA-256 of every staged input. Return `accepted`, `rejected`, or `incomplete` and include the assumptions actually used. Write diagnostics to stderr. ITPEval checks the receipt, assumption policy, and execution outcome before it gives proof credit. [Request and receipt implementation](../../itpeval/verification/external.py) · [Sprig's checker wrapper](../../examples/prover-adapters/sprig/verify.py)

## Add declaration extraction

An external extractor runs with `--entrypoint FILE --output FILE` from a staged copy of the locked project. The first JSONL record is `{"schema_version":1}`. Emit a `source` event with the logical path and SHA-256, then `declaration` events with a name, kind, statement, UTF-8 byte range, and visible declarations. Identify prior declarations with `[source_path, name]` pairs. ITPEval assigns stable records and builds the retrieval index.

When a declaration has a reviewed proof in the project, supply `proof_manifest`, `proof_sha256`, and `proof_used` together. ITPEval checks the exact certificate through the typed checker and compares the reported dependencies with the checker’s receipt. Sprig emits an unverified goal when its certificate file is blank, so it can still become a proof task or retrieval reference. [Sprig's extraction driver](../../examples/prover-adapters/sprig/extract.py) · [Event validation](../../itpeval/extraction/external.py)

## Check native DRAT certificates

DRAT-trim checks unsatisfiability certificates against a DIMACS formula. This example uses the upstream checker with both of its native certificate formats. The typed adapter locks the DIMACS formula and the checker executable. It reports the whole formula as its checked input. [DRAT format and checker](https://github.com/marijnheule/drat-trim/tree/2e3b2dc0ecf938addbd779d42877b6ed69d9a985) · [Adapter descriptor](../../examples/prover-adapters/drat/typed-adapter.json) · [Verified text and binary trials](../../benchmarks/runtime/detached-drat.json)

```bash
# From the checkout, build the revision used for the recorded checks.
scratch=$(mktemp -d)
git clone https://github.com/marijnheule/drat-trim.git "$scratch/drat-trim"
git -C "$scratch/drat-trim" checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
make -C "$scratch/drat-trim" drat-trim

# Copy the adapter and keep its text proof alongside the binary example.
export ITPEVAL_ADAPTER_DIR="$scratch/adapters"
mkdir -p "$ITPEVAL_ADAPTER_DIR"
cp -R examples/prover-adapters/drat "$ITPEVAL_ADAPTER_DIR/drat"
adapter="$ITPEVAL_ADAPTER_DIR/drat"
mkdir -p "$adapter/bin"
cp "$scratch/drat-trim/drat-trim" "$adapter/bin/"
cp "$adapter/hello/proof.drat" "$scratch/text.drat"

# Encode an addition of literal 64 followed by an addition of the empty clause.
python -c 'from pathlib import Path; import sys; Path(sys.argv[1]).write_bytes(b"a\x80\x01\x00a\x00")' \
  "$adapter/hello/proof.drat"
lock=$(itpeval prepare drat --project "$adapter/hello" --cache "$scratch/cache" \
  | python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])')

# Check the text and binary proofs, then export the checked target and its input.
itpeval verify-task --lock "$lock" --manifest text-completion.json \
  --candidate-file "$scratch/text.drat" --summary
itpeval verify-task --lock "$lock" --candidate-file "$adapter/hello/proof.drat" --summary
itpeval dataset --lock "$lock" --entrypoint problem.cnf --output "$scratch/export"
```

## Add a bundled integration

Use a bundled backend for native task operations outside the detached certificate profile. A benchmark integration also needs a target format, prompts, and aligned examples. [Translation tasks and data](../benchmarks/translation.md)

1. Add the native installer, checker, version probe, hello fixture and `adapter.json` under `itpeval/provers/<id>/`. Register toolchain sources and the executable or other inputs that identify the build. Run the checker against a staged artifact with an explicit operation. Preserve diagnostics and make rejection distinguishable from a missing executable, a crash or a timeout. [Toolchain registration](../../itpeval/environments/toolchains.py) · [Supervised checker](../../itpeval/runtime/checker.py)
2. Define the target, unchanged source bytes, allowed proof edits and required native evidence. Exercise an alternative valid proof, an incorrect proof and attempts to change the target, assumptions and obligations. Project authors can supply their own uniquely anchored completion in a prepared environment. [Task manifest format](task-manifests.md) · [Reviewed registry fixtures](../../itpeval/backends/tasks.json)
3. Expose the Python backend and declare each supported operation in the registry. A document revision keeps candidate text and a session generation. An implementation that can retain, branch or restore prover states should describe its state lifetime and report native observations for each operation. [Backend protocol](../../itpeval/core/protocols.py) · [Native registry](../../itpeval/backends/registry.py)
4. Register the extraction module in `itpeval.extraction.ADAPTERS` and implement `extract(ctx, entrypoint)`. Obtain declaration names, kinds and statements from the prover. Bind each declaration to exact source bytes and its preceding visible context. The collector records native evidence and any unavailable or reconstructed fields. Test an imported multi-declaration library and compare independent and cached outputs. [Extraction collector](../../itpeval/extraction/protocol.py) · [Known-answer tests](../../itpeval/tests/conformance/extraction.py)
5. Package the fixtures and native drivers. From a new installation, extract a target, resolve its completion task, check and repair an incorrect candidate, export the trainer rows and replay the episode. The release harness compares the artifacts with SDK, synchronous, batch and post-hoc results. Regenerate per-prover coverage from the resulting reports. [Installed-distribution test](../../scripts/check_distribution.py) · [Release gate](../../scripts/check_release.py) · [Capability matrix](capabilities.md)
