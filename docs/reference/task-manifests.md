# Proof task manifests

A completion manifest makes a theorem available as a proof task. It says which theorem must be proved, what part of the source a candidate can replace and what the verifier must observe to accept it. Save the manifest as `completion.json` in your project before preparing the lock. You can use `itpeval eval` to check a whole file directly. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

You can submit a proof fragment, a revised file or the full set of project files. ITPEval finds the target in the locked source and checks that the edit stays inside the chosen proof region.

The environment also fixes imported libraries. If the proof needs a lemma from Mathlib or the Rocq Stdlib, prepare that dependency before writing the task. [Lean libraries](../provers/lean4.md#libraries) · [Rocq libraries](../provers/rocq.md#libraries)

## Define the theorem and the editable region

Suppose `Hello.lean` contains `theorem exampleTarget : True := True.intro`. This manifest lets a candidate replace `True.intro`. Lean still checks the candidate against `exampleTarget` with the original statement `True`. For other syntax, open the proof-completion exercise for your prover. [Exercises for all ten provers](../start/proof-completion.md#choose-your-prover)

```json
{
  "schema_version": 1,
  "entrypoint": "Hello.lean",
  "files": ["Hello.lean"],
  "anchor": "theorem exampleTarget : True := True.intro",
  "target": "exampleTarget",
  "statement": "True",
  "proof_slot": "True.intro",
  "allowed_edits": ["True.intro", "False.elim"]
}
```

| Field | What to put in it |
| --- | --- |
| `entrypoint` | The source path relative to the project root |
| `files` | The entrypoint and any other source or build files the checker needs. Include `ROOT` for an Isabelle session or the theory driver and `Holmakefile` for HOL4. |
| `anchor` | Text that identifies the target declaration and occurs exactly once in the source. Include the reference proof or proof fragment in this span. |
| `target`, `statement` | The theorem’s native name and the proposition it must prove |
| `proof_slot` | The exact text to replace. It must occur once within `anchor`. |
| `observer_anchor` | Optional text marking a separate native observation point, such as the end of a Rocq section |

Binders, imports, local variables and namespaces all remain fixed. For Lean or Rocq modules that use local dependencies, include each source in `files` and list the paths in compilation order in `dependency_sources`. The native checker compiles them in the attempt directory before checking the entrypoint. Use `budgets` to set a versioned resource budget.

## Choose the edits and require evidence

`allowed_edits` lists complete fragments the project owner has reviewed for this task. You can include edits that are permitted but fail to prove the statement, such as `False.elim` against the example above. A training loop can learn from the native diagnostic.

Where the backend supports it, `proof_atoms` allows bounded sequences of reviewed commands or labels. Lean supports `<;>`, Rocq accepts semicolon-separated tactics followed by a period, and HOL tactics use `THEN`. Metamath accepts premise labels, Mizar accepts reviewed statements one per line and PVS accepts `then` with reviewed commands. Native checkers execute with the permissions of the invoking account, so the manifest, allowed edits, source and libraries are trusted inputs.

`allowed_assumptions` records the task's reviewed logical context. Lean and Rocq also inspect the compiler's target assumption report. The HOL constructors require an empty theorem-hypothesis list. ACL2 checks the theorem event in the resulting world. Metamath verifies the proof and disjoint-variable conditions, queries the transitive native axiom list with `show trace_back /axioms`, and rejects every unlisted axiom. PVS requires complete status for the named target and every declared `obligations` entry, as well as matching attempted, succeeded and total counts in its native summary. Use generated TCC names in that list when they must be present. The other profiles check a single named target and reject secondary obligations during task construction. Agda checks the resulting definition and its type. Mizar checks the generated theorem in its accommodated article. Isabelle checks the lemma as part of the selected session.

```python
# Load the fixed target and evaluate only the proposed edit.
from pathlib import Path
from itpeval.backends.projects import build_task
from itpeval.environments import load_project
from itpeval.verification.service import verify

def check_fragment(lock_path: Path, candidate: str):
    prepared = load_project(lock_path)
    task = build_task(prepared)
    return verify(task, candidate, prepared=prepared).to_dict()
```

`curated_task(prover, environment_id)` provides a small packaged benchmark with reviewed target witnesses. `build_task(prepared, manifest_path)` builds the project's own target. The returned records share the same verification, session, scheduling and reward interfaces. Artifact and statement checks report checker acceptance separately from proof completion.

Prepare a resolved toolchain and library configuration with `itpeval --prefix PREFIX prepare --manifest ENVIRONMENT.json --cache CACHE`. The manifest supplies the prover, project, libraries, imports and options. Alternatively, `itpeval --prefix PREFIX prepare PROVER --project DIR --cache CACHE` freezes a local project directly. Both commands print the path to the resulting lock. `verify-task --lock LOCK --candidate FRAGMENT` checks the project's default completion manifest.

For Metamath, PVS, Isabelle's single-proposition lemma profile, Agda, ACL2 and Mizar, copy the complete statement from its declaration. The builder checks the full source-delimited statement, including internal whitespace. Isabelle accepts the content of a quoted proposition. Lean, Rocq, HOL4 and HOL Light instead use native type or term comparison for their target observers.


## Submitting a document revision

`verify_document(task, document, prepared=prepared)` accepts a UTF-8 string or bytes containing the complete entrypoint. The service supplies its locked siblings. To submit the entire file set, pass `Artifact.from_files(entrypoint, files)`, where `files` maps project-relative names to bytes. Each sibling, the entrypoint path, and the bytes before and after the proof slot must match the reviewed task. Both the original project source and the instrumented source produced by `assemble` are supported.

The service extracts the submitted proof from its slot and checks it with the same native target witness used by `verify`. Evidence includes `submitted_artifact:<id>` in `evidence_references`. For a native check, `artifact_id` identifies the assembled checker input. A changed target, missing declaration, added assumption, or changed sibling gets `not_run`, `policy_rejected`, and `target_preservation="violated"`, with the submitted artifact's ID. An authorized empty slot gets `incomplete`.

`DocumentSession.submit_document(handle, document)` records each whole-document submission as a revision, including policy rejections. Calling `finalize(handle)` verifies that exact revision again. `replay_documents(documents)` resets the session and returns each revision’s observation in submission order. A subsequent `submit(handle, candidate)` switches back to fragment input. The CLI exposes both document forms through `verify-task --document-file FILE` and `verify-task --artifact-json BUNDLE.json`.
