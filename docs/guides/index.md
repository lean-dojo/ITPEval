# User guide

## Check a proof

<span id="check-a-file-or-complete-a-proof"></span>

- [Work with your own files](work-with-a-library.md#check-a-file-you-already-have) if you already have a source file or project.
- [Complete a proof in VS Code](../start/proof-completion.md) if you want to write the proof yourself.
- [Define a proof task](../reference/task-manifests.md) if you want to compare attempts on the same theorem.

## Formalize, translate, or search

<span id="formalize-explain-or-translate-a-theorem"></span>
<span id="train-or-evaluate-an-agent"></span>

- [Formalization and translation](formalization-and-translation.md) for English statements, formal theorems, or proofs in another prover's language.
- [Automated proof search](automated-proving.md) for standalone solvers and exploring native proof branches.
- [Proof repair and agent training](verification-and-learning.md) for policies that use checker feedback and episodes you can replay.

## Extract a library or build a dataset

<span id="extract-a-library"></span>
<span id="build-a-dataset"></span>

- [Library extraction and datasets](extract-and-build-a-dataset.md) for extracting declarations and combining libraries across provers.
- [Training datasets](training-data.md) for fine-tuning, reinforcement learning, and premise retrieval.
- [Translation benchmark](../benchmarks/translation.md) describes the released tasks and how to load them.

## Run larger jobs or add a prover

<span id="inspect-proof-states-and-run-checks-in-batches"></span>
<span id="add-a-prover"></span>

- [Project configuration](environment-manifest.md) covers locking sources, dependencies, and toolchains.
- [Execution and caching](../runtime/execution.md) covers batching, reusing work, and sharing proof checkpoints. See [runtime measurements](../runtime/measurements.md) for results by workload.
- [Backend capabilities](../reference/capabilities.md) lists available operations and their evidence.
- [Add a backend](../reference/extending-a-backend.md) or follow the [Sprig example](../agents/sprig.md) to integrate a checker.
