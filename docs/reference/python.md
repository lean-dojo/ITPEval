# Python API

| To | Start with |
|---|---|
| Check a complete source file | `itpeval.itp.run_itp(prover=..., code_path=...)` |
| Verify a candidate for a fixed theorem | `itpeval.verification.verify(task, candidate, prepared=...)` |
| Extract declarations | `itpeval.extraction.extract_project(prepared, entrypoint, destination)` |
| Record an agent’s attempts | `itpeval.learning.rollouts.rollout(task, prepared, manifest, generate)` |

## Chapters

- <span id="check-a-source-file"></span><span id="prepare-and-reopen-an-environment"></span><span id="check-a-candidate"></span><span id="reuse-an-identical-check"></span>[Project and checker APIs](python/checking.md)
  Prepare a project, check a source file or proof, manage revisions, and reuse an identical check.
- <span id="ask-an-automated-prover-for-help"></span><span id="record-and-replay-agent-actions"></span>[Proof search and agent APIs](python/proof-agents.md)
  Search a native goal, record proof attempts, and replay a saved run.
- <span id="export-a-library-dataset"></span><span id="extract-declarations-and-context"></span><span id="records-and-backend-discovery"></span>[Extraction and record APIs](python/data-and-records.md)
  Export declarations and contexts, decode records, and discover tested backend operations.
- <span id="function-reference"></span>[Function reference](python/functions.md)
  Look up current Python signatures, defaults, and return types.
