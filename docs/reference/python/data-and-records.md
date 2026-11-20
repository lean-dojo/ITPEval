# Extraction and record APIs

## Export a library dataset

`itpeval.corpus.datasets.export_dataset(prepared, entrypoint, output, *, timeout_s=180)` writes the extracted declarations and a premise-selection JSONL file. Pass the entrypoint path relative to the project and choose an output directory outside the source project. Unpack the result as `bundle, premise_path`. Read `bundle.path / "declarations.jsonl"` for declarations and use their IDs to join them to the records in `premise_path`. [Run the library walkthrough](../../guides/work-with-a-library.md)

## Extract declarations and context

`extract_project(prepared, entrypoint, destination)` takes a project-relative entrypoint and a writable output directory. The result contains the bundle path, a report with field-level provenance and a cache-hit flag. Look up a declaration by its occurrence ID and select its context when retrieving premises. [Extraction and dataset examples](../../guides/extract-and-build-a-dataset.md)

## Records and backend discovery

Record classes expose `to_dict()`, `from_dict()` and `json_schema()`. For example, print the task schema with `python -c 'import json; from itpeval.core.types import TaskSpec; print(json.dumps(TaskSpec.json_schema(), indent=2))'`.

The Python backend names are importable. For example, `from itpeval.backends.hol_light import backend` selects the backend exposed by the CLI as `hol-light`. Its `check` method accepts the same task, candidate and prepared environment as the shared verifier.

To see which operations have run on this exact environment and native build, call `backend.capabilities(prepared=project, qualification_report=report)`. Use the release report for the historical package and native checks. Use the interaction report for the stable-toolchain document forks, checkpoints and native proof feedback examples. The project’s environment ID and native build must both match the evidence. [Release report](../../../benchmarks/runtime/qualification.jsonl) · [Stable interaction report](../../../benchmarks/runtime/interaction-capabilities.jsonl)

A search can require tested operations by calling `require_capabilities(project.spec.prover, ["checkpoint_document"], prepared=project, qualification_report=report, allow_experimental=False)` from `itpeval.backends.registry`. Optional native instruments must also be present in the lock when the operation uses them.

Install `.[isabelle]` for the Isa-REPL client’s MessagePack support.

The Lean equivalence API compares two extracted propositions in one environment. It checks both implications using a bounded search over hypothesis application, equality symmetry, and conjunction exchange. A failed search reports “equivalence not established.” [Equivalence for translation results](../../guides/formalization-and-translation.md#semantic-equivalence-in-lean)

[CLI commands](../cli.md) · [Backend protocol](../../../itpeval/core/protocols.py)
