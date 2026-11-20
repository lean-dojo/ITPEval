# Function reference

<span id="function-reference"></span>

Look up call signatures and defaults here. For runnable examples, start with the [Python API guide](../python.md).

## Prepare a project and check a proof

### `prepare_project`

<!-- api-signature: itpeval.environments:prepare_project -->
<pre class="api-signature"><code>itpeval.environments.prepare_project(
    prover: str,
    project: Path,
    *,
    prefix: Path,
    cache: Path,
    libraries: Mapping[str, Path] | None = None,
    options: Mapping[str, str] | None = None,
    imports: Iterable[str] = (),
    import_bindings: Mapping[str, tuple[str, str]] | None = None,
    checking_profile: str = 'strict',
    toolchain_inputs: Mapping[str, Path] | None = None,
    project_name: str | None = None,
    project_commit: str | None = None,
    library_commits: Mapping[str, str] | None = None,
) -&gt; PreparedProject</code></pre>

Lock sources, libraries, and the native toolchain. The returned project has an environment ID and a lock path.

### `prepare_manifest`

<!-- api-signature: itpeval.environments:prepare_manifest -->
<pre class="api-signature"><code>itpeval.environments.prepare_manifest(
    manifest: Path,
    *,
    prefix: Path,
    cache: Path,
) -&gt; PreparedProject</code></pre>

Prepare a project from its JSON environment manifest. [Project configuration](../../guides/environment-manifest.md)

### `load_project`

<!-- api-signature: itpeval.environments:load_project -->
<pre class="api-signature"><code>itpeval.environments.load_project(lock_path: Path) -&gt; PreparedProject</code></pre>

Reopen an existing lock and validate its inputs.

### `get_backend`

<!-- api-signature: itpeval.backends.registry:get_backend -->
<pre class="api-signature"><code>itpeval.backends.registry.get_backend(prover: str) -&gt; NativeBackend</code></pre>

Select a backend by its prover ID. Call the `NativeBackend` methods below on the returned object.

### `NativeBackend.build_task`

<!-- api-signature: itpeval.backends.registry:NativeBackend.build_task -->
<pre class="api-signature"><code>NativeBackend.build_task(prepared, manifest_path: str = 'completion.json') -&gt; TaskSpec</code></pre>

Read the completion manifest and select the theorem and editable proof region.

### `NativeBackend.open_document`

<!-- api-signature: itpeval.backends.registry:NativeBackend.open_document -->
<pre class="api-signature"><code>NativeBackend.open_document(task: TaskSpec, *, prepared)</code></pre>

Open a session for candidate revisions, reset, and replay. [Document revisions](../../runtime/execution/document-revisions.md)

### `NativeBackend.check_document`

<!-- api-signature: itpeval.backends.registry:NativeBackend.check_document -->
<pre class="api-signature"><code>NativeBackend.check_document(
    task: TaskSpec,
    document: Artifact | str | bytes,
    *,
    prepared,
    **options,
)</code></pre>

Check an entrypoint or multi-file artifact against the locked theorem.

### `curated_task`

<!-- api-signature: itpeval.backends.registry:curated_task -->
<pre class="api-signature"><code>itpeval.backends.registry.curated_task(prover: str, environment_id: str) -&gt; TaskSpec</code></pre>

Select the packaged proof-completion task for a prover and environment.

### `verify`

<!-- api-signature: itpeval.verification:verify -->
<pre class="api-signature"><code>itpeval.verification.verify(
    task: TaskSpec,
    candidate: str | None = None,
    *,
    prepared: PreparedProject,
    cancel: Event | None = None,
    retain_dir: Path | None = None,
    metamath_base: str | None = None,
) -&gt; VerificationEvidence</code></pre>

Check a proof fragment against the task and return verifier evidence.

### `verify_document`

<!-- api-signature: itpeval.verification:verify_document -->
<pre class="api-signature"><code>itpeval.verification.verify_document(
    task: TaskSpec,
    document: Artifact | str | bytes,
    *,
    prepared: PreparedProject,
    cancel: Event | None = None,
    retain_dir: Path | None = None,
    metamath_base: str | None = None,
) -&gt; VerificationEvidence</code></pre>

Verify a revised file or a multi-file artifact. The bytes outside the allowed proof region must match the task.

### `verify_cached`

<!-- api-signature: itpeval.verification.cache:verify_cached -->
<pre class="api-signature"><code>itpeval.verification.cache.verify_cached(
    task: TaskSpec,
    candidate: str | None = None,
    *,
    prepared: PreparedProject,
    cache: Path,
    cancel=None,
) -&gt; VerificationLookup</code></pre>

Check a candidate or reuse evidence for an identical request. [Cache example](checking.md#reuse-an-identical-check)

### `run_itp`

<!-- api-signature: itpeval.itp:run_itp -->
<pre class="api-signature"><code>itpeval.itp.run_itp(
    *,
    prover: str | None = None,
    code: str | None = None,
    code_path: Path | None = None,
    task_dir: Path | None = None,
    task_file: Path | None = None,
    mode: str = 'raw',
    prefix: Path | None = None,
    timeout_s: int | None = None,
    ensure_installed: bool = False,
    install_timeout_s: int | None = None,
    budgets: Budgets | None = None,
    install_budgets: Budgets | None = None,
    cancel=None,
    task: TaskSpec | None = None,
    candidate: str | None = None,
    prepared: PreparedProject | None = None,
    retain_dir: Path | None = None,
) -&gt; RunResult | VerificationEvidence</code></pre>

Check a source file, snippet, or native task directory and return a `RunResult`. The task-bound form returns `VerificationEvidence`. [Check a source file](checking.md#check-a-source-file)

### `compare`

<!-- api-signature: itpeval.semantics.lean:compare -->
<pre class="api-signature"><code>itpeval.semantics.lean.compare(
    prepared,
    entrypoint: str,
    left_id: str,
    right_id: str,
    *,
    cache: Path,
    timeout_s: int = 60,
) -&gt; EquivalenceResult</code></pre>

Try both implications between two declarations from the same Lean environment within a fixed budget.

## Run a proof session or agent

### `prepare_solver`

<!-- api-signature: itpeval.atp:prepare_solver -->
<pre class="api-signature"><code>itpeval.atp.prepare_solver(
    solver: str = 'e',
    *,
    executable: Path | None = None,
    prefix: Path | None = None,
) -&gt; PreparedSolver</code></pre>

Resolve the local E or Vampire executable and record its build for reuse.

### `solve_tptp`

<!-- api-signature: itpeval.atp:solve_tptp -->
<pre class="api-signature"><code>itpeval.atp.solve_tptp(
    problem: Path,
    *,
    solver: str = 'e',
    executable: Path | None = None,
    prefix: Path | None = None,
    tptp_root: Path | None = None,
    budgets: Budgets | None = None,
    cancel: Event | None = None,
) -&gt; SearchEvidence</code></pre>

Run a standalone TPTP problem and keep the solver's verdict and output. [Run a solver on TPTP](../../guides/automated-proving/run-a-solver.md)

### `NativeBackend.open_native_session`

<!-- api-signature: itpeval.backends.registry:NativeBackend.open_native_session -->
<pre class="api-signature"><code>NativeBackend.open_native_session(task: TaskSpec, *, prepared, **options)</code></pre>

Open a prover-specific session on a reviewed proof task. Use `open_document` for detached certificate adapters.

### `NativeProofDriver`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver -->
<pre class="api-signature"><code>itpeval.runtime.proof_driver.NativeProofDriver(task, prepared, **session_options)</code></pre>

Use a common interface for native observations, actions, checkpoints, and proof search.

### `NativeProofAction`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofAction -->
<pre class="api-signature"><code>itpeval.runtime.proof_driver.NativeProofAction(
    kind: ActionKind,
    text: str,
    goal_path: tuple[int, ...] | None = None,
    step_index: int | None = None,
)</code></pre>

Describe a prover-specific step. Use `goal_path` for a HOL branch or `step_index` for a Metamath assignment.

### `NativeProofDriver.observe`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.observe -->
<pre class="api-signature"><code>NativeProofDriver.observe(*, cancel=None) -&gt; NativeProofObservation</code></pre>

Read the current native goal, hole, sequent, or thesis.

### `NativeProofDriver.advance`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.advance -->
<pre class="api-signature"><code>NativeProofDriver.advance(
    action: NativeProofAction,
    *,
    cancel=None,
) -&gt; NativeProofTransition</code></pre>

Try an action and see whether the prover committed it.

### `NativeProofDriver.checkpoint`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.checkpoint -->
<pre class="api-signature"><code>NativeProofDriver.checkpoint(*, cancel=None) -&gt; NativeProofCheckpoint</code></pre>

Save the committed actions and observed state identities.

### `NativeProofDriver.from_checkpoint`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.from_checkpoint -->
<pre class="api-signature"><code>NativeProofDriver.from_checkpoint(
    task,
    prepared,
    checkpoint: NativeProofCheckpoint,
    *,
    cancel=None,
    **session_options,
)</code></pre>

Restore a saved revision under the same task and environment and check the replayed states.

### `NativeProofDriver.fork`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.fork -->
<pre class="api-signature"><code>NativeProofDriver.fork(*, cancel=None)</code></pre>

Create an independent continuation from the committed state.

### `NativeProofDriver.suggest_atp`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.suggest_atp -->
<pre class="api-signature"><code>NativeProofDriver.suggest_atp(
    *,
    solver=None,
    executable=None,
    timeout_s=None,
    cancel=None,
    goal_path=None,
    max_trials=32,
    proof_fragment=None,
    hints=(),
)</code></pre>

Search the current goal with a native strategy or an external solver where supported. [Search from a proof state](../../guides/automated-proving/search-a-proof-state.md)

### `NativeProofDriver.apply_atp`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.apply_atp -->
<pre class="api-signature"><code>NativeProofDriver.apply_atp(suggestion, *, cancel=None) -&gt; NativeProofTransition</code></pre>

Apply a checked suggestion to the revision that produced it.

### `SearchWithATP`

<!-- api-signature: itpeval.learning.native_proofs:SearchWithATP -->
<pre class="api-signature"><code>itpeval.learning.native_proofs.SearchWithATP(
    solver: str | PreparedSolver | None = None,
    executable: Path | None = None,
    timeout_s: float | None = None,
    goal_path: tuple[int, ...] | None = None,
    max_trials: int = 32,
    hints: tuple[str, ...] = (),
)</code></pre>

Return this decision from a native policy to request search at an open goal.

### `NativeProofDriver.finalize`

<!-- api-signature: itpeval.runtime.proof_driver:NativeProofDriver.finalize -->
<pre class="api-signature"><code>NativeProofDriver.finalize(*, proof_fragment=None, **options) -&gt; NativeProofFinalization</code></pre>

Check the completed proof and read the result’s verifier evidence. Some PVS sessions require a reviewed ProofLite fragment.

### `rollout`

<!-- api-signature: itpeval.learning.rollouts:rollout -->
<pre class="api-signature"><code>itpeval.learning.rollouts.rollout(
    task: TaskSpec,
    prepared: PreparedProject,
    manifest: RunManifest,
    generate: Callable[[TaskSpec, tuple[Transition, ...]], Action],
) -&gt; Episode</code></pre>

Record a proof-edit episode using a callback that receives the task and previous attempts.

### `replay`

<!-- api-signature: itpeval.learning.episodes:replay -->
<pre class="api-signature"><code>itpeval.learning.episodes.replay(
    episode: Episode,
    *,
    task: TaskSpec,
    prepared: PreparedProject,
    receipt: Path | None = None,
) -&gt; VerificationEvidence</code></pre>

Recheck the saved edits under the original task and environment.

### `rollout_native`

<!-- api-signature: itpeval.learning.native_proofs:rollout_native -->
<pre class="api-signature"><code>itpeval.learning.native_proofs.rollout_native(
    task,
    prepared,
    manifest,
    generate,
    *,
    proof_fragment=None,
    cancel=None,
    **session_options,
) -&gt; NativeProofEpisode</code></pre>

Record a native proof episode. The callback receives the current state and earlier actions.

### `replay_native_episode`

<!-- api-signature: itpeval.learning.native_proofs:replay_native_episode -->
<pre class="api-signature"><code>itpeval.learning.native_proofs.replay_native_episode(
    episode: NativeProofEpisode,
    *,
    task,
    prepared,
    cancel=None,
    **session_options,
) -&gt; VerificationEvidence | None</code></pre>

Repeat the recorded actions and run a fresh final check if the episode reached one.

### `search_portfolio`

<!-- api-signature: itpeval.learning.portfolio:search_portfolio -->
<pre class="api-signature"><code>itpeval.learning.portfolio.search_portfolio(
    driver: NativeProofDriver,
    propose,
    *,
    policy_id: str,
    max_trials=32,
    max_depth=8,
    timeout_s=None,
    proof_fragment=None,
    cancel=None,
) -&gt; ProofPortfolio</code></pre>

Try native actions or ATP suggestions on independent branches. The result includes each trial’s parent and the winning branch when one is verified.

### `replay_portfolio`

<!-- api-signature: itpeval.learning.portfolio:replay_portfolio -->
<pre class="api-signature"><code>itpeval.learning.portfolio.replay_portfolio(
    portfolio: ProofPortfolio,
    *,
    task,
    prepared,
    cancel=None,
    **session_options,
) -&gt; NativeProofEpisode</code></pre>

Recheck the winning route and return a native episode. [Branch and replay example](../../guides/automated-proving/branch-and-replay.md)

## Extract source and export training views

### `NativeBackend.inspect_declarations`

<!-- api-signature: itpeval.backends.registry:NativeBackend.inspect_declarations -->
<pre class="api-signature"><code>NativeBackend.inspect_declarations(
    prepared,
    entrypoint: str,
    destination: Path,
    *,
    timeout_s: float = 180,
    context_storage='expanded',
)</code></pre>

Export declarations and their context from a prepared project.

### `extract_project`

<!-- api-signature: itpeval.extraction:extract_project -->
<pre class="api-signature"><code>itpeval.extraction.extract_project(
    prepared,
    entrypoint: str,
    destination,
    *,
    timeout_s=180,
    context_storage='expanded',
)</code></pre>

Return the bundle path, coverage report, and cache-hit flag.

### `export_dataset`

<!-- api-signature: itpeval.corpus.datasets:export_dataset -->
<pre class="api-signature"><code>itpeval.corpus.datasets.export_dataset(
    prepared,
    entrypoint,
    output,
    *,
    timeout_s=180,
    context_storage='expanded',
    premise_visibility=None,
)</code></pre>

Return the extraction bundle and the premise-selection JSONL path.

### `export_collection`

<!-- api-signature: itpeval.corpus.library_collection:export_collection -->
<pre class="api-signature"><code>itpeval.corpus.library_collection.export_collection(
    catalog: Path,
    output: Path,
    *,
    format: str = 'jsonl',
    premise_visibility='expanded',
) -&gt; dict</code></pre>

Join extraction bundles from a catalog while retaining library and source provenance. [Combine libraries](../../guides/extract-and-build-a-dataset/combine-libraries.md)

### `export_training_data`

<!-- api-signature: itpeval.learning.training_data:export_training_data -->
<pre class="api-signature"><code>itpeval.learning.training_data.export_training_data(
    output: Path,
    *,
    bundles=(),
    catalog: Path | None = None,
    episodes=(),
    native_episodes=(),
    locks=(),
    task_manifest='completion.json',
    format='jsonl',
    style='standard',
    split=None,
    exclude_source_hashes=(),
)</code></pre>

Write training views from extraction bundles, proof episodes, or locks. [Choose a training view](../../guides/training-data/choose-a-view.md)

### `export_jsonl`

<!-- api-signature: itpeval.learning.episodes:export_jsonl -->
<pre class="api-signature"><code>itpeval.learning.episodes.export_jsonl(
    episodes: Iterable[Episode],
    path: Path,
    *,
    view: str = 'attempts',
) -&gt; int</code></pre>

Write episode records, individual attempts, or supervised pairs and return the row count.

### `sample_tasks`

<!-- api-signature: itpeval.learning.views:sample_tasks -->
<pre class="api-signature"><code>itpeval.learning.views.sample_tasks(
    tasks: collections.abc.Iterable[itpeval.core.types.TaskSpec],
    *,
    count: int,
    seed: int,
) -&gt; tuple[itpeval.core.types.TaskSpec, ...]</code></pre>

Sample distinct tasks by seed, independent of input order.

### `repair_rows`

<!-- api-signature: itpeval.learning.views:repair_rows -->
<pre class="api-signature"><code>itpeval.learning.views.repair_rows(
    episodes: collections.abc.Iterable[itpeval.core.episodes.Episode],
) -&gt; collections.abc.Iterator[dict]</code></pre>

Yield failed candidates with native feedback and the next accepted edit.

### `trajectory_rows`

<!-- api-signature: itpeval.learning.views:trajectory_rows -->
<pre class="api-signature"><code>itpeval.learning.views.trajectory_rows(
    episodes: collections.abc.Iterable[itpeval.core.episodes.Episode],
) -&gt; collections.abc.Iterator[dict]</code></pre>

Yield action, observation, evidence, and reward for each step.
