# Core concepts

Here’s a thought experiment. Give two agents the same theorem. One submits the whole proof in one go. The other asks the prover what’s left after every step. What would you need to save to replay both attempts? Start with the theorem, the libraries it imports, and the prover that checked it.

| Record | What it identifies |
|---|---|
| Environment | The native toolchain, project snapshot, libraries and options. Its lock points to the inputs for a later run. |
| Artifact | The paths and exact bytes of the submitted files and the entrypoint the prover reads. |
| Task | The operation to run and the artifact it uses. For proof completion it also identifies the fixed theorem, allowed edit, assumptions and obligations. |
| Evidence | What happened on one attempt, including the checker’s answer, diagnostics, and whether the proof met the task’s conditions. |
| Declaration occurrence | A theorem, definition or other declaration at a particular place in a versioned project. Its context records what was visible there. |
| Episode | The ordered attempts on one task, their checker replies and the final artifact when available. |

## Read a checker result

In the Metamath exercise, the environment contains the source database and its native checker. The task asks for a proof of `|- pair x y`. When your agent changes `vx vx distinct` to `vx vy distinct`, the task and environment IDs stay the same. The candidate and submitted artifact change.

Read the execution outcome first. A timeout leaves the verdict unknown. After a native run, read the checker outcome and `task_success`, which also accounts for the fixed statement and required obligations. The episode ties each candidate to its evidence. [Try the Metamath exercise](../provers/metamath.md#proof-completion)

## Join a theorem to its context

Use IDs when combining extraction and training records. A theorem called `identity` can occur in several files or libraries. An extraction binds each occurrence to its project revision and source location. Its context ID gives you the premises in scope at that point. To see the premises the proof used, read the proof-use edges and the field-availability report. [Extract a library and look up premises](../guides/extract-and-build-a-dataset.md)
