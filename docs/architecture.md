# Architecture

Adapters run the native provers and return evidence in a common format. Agents can submit whole proof edits or use native goal and action APIs where the backend exposes them. [Backend capabilities](reference/capabilities.md)

## What happens when you submit an edit

1. Prepare the project. Its lock identifies the sources, libraries, and native build. Rocq maps module names to compiled files, and Agda uses module search roots. [Project configuration](guides/environment-manifest.md)
2. Build the task. Proof completion fixes a theorem and an editable region. An artifact check specifies the files and entrypoint. [Task manifests](reference/task-manifests.md)
3. Run the native verifier. It checks the submitted fragment against the named target, permitted assumptions, and obligations. PVS, for example, can generate type-correctness obligations. [Execution and caching](runtime/execution.md)
4. Record the evidence. Use the diagnostics to revise a candidate, or save the run for replay or training. [Common records](concepts/records.md)

## Python modules

**`itpeval.core`**
:   Versioned records for environments, artifacts, tasks, declaration occurrences, observations and evidence.

**`itpeval.environments`**
:   Freeze project inputs, identify installed native builds and validate environment locks.

**`itpeval.backends`**
:   Enumerate provers, capabilities, reviewed task templates and editable proof regions.

**`itpeval.runtime`**
:   Supervise native checks, manage workspaces, and reuse initialized prover state where supported.

**`itpeval.verification`**
:   Assemble candidates and check the fixed task. Exact repeats can reuse evidence from the result cache.

**`itpeval.atp`**
:   Run E or Vampire on TPTP input or through a bridge for a supported native goal. [Search and replay](guides/automated-proving.md)

**`itpeval.extraction`, `corpus`, `retrieval`**
:   Store declaration and context records, exact source bytes, dependency edges and local search indexes.

**`itpeval.learning`**
:   Bind generation settings to an environment and task, retain each action and observation, export attempts and replay.

**`itpeval.semantics`**
:   Optional bidirectional checks on extracted Lean propositions.

The translation benchmark in `eval/` uses the verification infrastructure and adds datasets, prompts, provider clients and historical protocols such as the original Logipedia convention. Changes to the file and snippet staging code contribute to the benchmark’s checkpoint identity.

## Add a prover

Start with a file checker. Add a reviewed proof target for training or an extraction driver for library declarations. [Backend integration guide](reference/extending-a-backend.md)
