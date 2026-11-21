# Project and checker APIs

## Check a source file

Pass `run_itp` one input. Use `code_path` for a file, `code` for text, or `task_dir` for a native directory. Set `task_file` where the adapter supports selecting an entrypoint. `ok` reports the file verdict, `execution_outcome` describes the run, and `stdout` and `stderr` carry diagnostics. [Check a file or project](../../guides/work-with-a-library.md#check-a-file-you-already-have)

For repeated checks with shared libraries, prepare the project and use an `Artifact` with `check_artifact`. Preserve the files’ relative paths. [Check a multi-file project](../../guides/work-with-a-library.md#check-the-proofs-in-the-database)

## Prepare and reopen an environment

`prepare_project(prover, project, *, prefix, cache, ...)` records the project files, dependencies and native toolchain. Call it once before a series of checks.

| Parameter | What to pass |
| --- | --- |
| `prover` | A backend ID such as `"rocq"` or `"hol-light"` |
| `project` | The path to the native project root |
| `prefix` | The directory that contains the installed toolchains |
| `cache` | A writable directory for snapshots, hashes and locks |
| `libraries` | An optional mapping from dependency names to local paths |

The returned `PreparedProject` contains an environment ID and a `lock_path`. Use `load_project(lock_path)` to reopen the environment on the same installation. Loading checks that its inputs still match the lock. [Environment manifest guide](../../guides/environment-manifest.md)

## Check a file with external imports

Suppose `client/Client.v` imports `From MyLib Require Import Base.` and `compiled/MyLib/Base.vo` was compiled as `MyLib.Base`. Bind its directory once and use the resulting lock for checks. For Agda, use `agda` and a `.agda` entrypoint, and point each library binding at its source include root, such as `agda-stdlib/src`. [Rocq library setup](../../provers/rocq.md#build-and-check-a-library) · [Agda library setup](../../provers/agda.md#build-and-check-a-library)

```python
from pathlib import Path

from itpeval.cli.lib import default_prefix
from itpeval.core.types import Artifact, TaskSpec
from itpeval.environments import prepare_project
from itpeval.verification import verify

# Lock the client and the compiled Rocq modules under their logical name.
project = prepare_project("rocq", Path("client"), prefix=default_prefix(),
                          cache=Path("build/itpeval-cache"),
                          libraries={"MyLib": Path("compiled/MyLib")})
entrypoint = "Client.v"
artifact = Artifact.from_files(entrypoint, {entrypoint: (project.project / entrypoint).read_bytes()})
task = TaskSpec("rocq", project.environment_id, "check_artifact", artifact)
result = verify(task, prepared=project)
print(result.checker_outcome)
```

## Check a candidate

`get_backend(prover).build_task(project)` reads the completion manifest. Use `verify(task, candidate, prepared=project)` for a fragment or `verify_document(task, document, prepared=project)` for a full file or multi-file `Artifact`. The verifier checks that source outside the editable region matches the lock.

`evidence.task_success` is `True` for a proof that satisfies its task, `False` for a definite failure, and `None` for an unknown result. Read `execution_outcome`, `checker_outcome`, `target_preservation`, and `obligations` for the details. [Runnable proof example](../../start/quickstart.md#verify-a-candidate)

Use `open_document` for saved revisions. Use `open_native_session` and `session.inspect(session.handle)` for native feedback, or `NativeProofDriver` for a common action API. [Document revisions](../../runtime/execution/document-revisions.md) · [Native proof sessions](../../runtime/execution/native-interaction.md)

## Reuse an identical check

`verify_cached` returns evidence and a `cache_hit` flag. Time the call to measure lookup latency. The timing in the evidence describes the original check. [Cache measurements](../../runtime/measurements/startup-and-caching.md#loading-a-project-and-reusing-a-verification-result)

```python
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.registry import curated_project, get_backend
from itpeval.cli.lib import default_prefix
from itpeval.environments import prepare_project
from itpeval.verification.cache import verify_cached

with TemporaryDirectory() as directory:
    cache = Path(directory)
    project = prepare_project("metamath", curated_project("metamath"),
                              prefix=default_prefix(), cache=cache)
    task = get_backend("metamath").build_task(project)
    # An identical second request can reuse the first native verdict.
    for _ in range(2):
        result = verify_cached(task, task.allowed_edits[0], prepared=project, cache=cache)
        print(result.cache_hit, result.evidence.task_success)
```

The output is `False True` followed by `True True`. To reuse evidence across runs, supply a persistent cache directory. Changed candidates and task budgets have different keys. Episode replay requests fresh verification.
