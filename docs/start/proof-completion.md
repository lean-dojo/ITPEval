# Complete a proof in VS Code

Suppose you have a theorem and want to try several ways to prove it. A proof-completion task tells ITPEval which theorem to check and which part of the file a candidate may edit. That part can be a tactic in Lean, a sequence of labels in Metamath, or a hint that tells ACL2 where to look.

You can edit the file yourself in VS Code, replay the example’s two attempts, or connect a model to propose a fragment. The native prover checks each candidate against the same theorem. For a normal file check, including changes to a theorem statement, pass the file directly to the prover through ITPEval. [Check a file you already have](../guides/work-with-a-library.md#check-a-file-you-already-have)

## Choose your prover

Choose an exercise in your prover’s own language. Each guide shows where to edit the proof and how to check it from your editor.

<!-- completion-examples -->

| Prover | File to edit | Starting fragment | One accepted completion |
|---|---|---|---|
| [Lean 4](../provers/lean4.md#proof-completion) | `Hello.lean` | `exact False.elim` | `rfl` |
| [Rocq](../provers/rocq.md#proof-completion) | `hello.v` | `exact I.` | `exact (fun p => p).` |
| [Isabelle/HOL](../provers/isabelle.md#proof-completion) | `Hello.thy` | `by (rule FalseE)` | `by (rule premise)` |
| [HOL Light](../provers/hol-light.md#proof-completion) | `hello.ml` | `NO_TAC` | `ITAUT_TAC` |
| [HOL4](../provers/hol4.md#proof-completion) | `helloScript.sml` | `NO_TAC` | `PROVE_TAC []` |
| [ACL2](../provers/acl2.md#proof-completion) | `hello.lsp` | `:hints (("Goal" :use itpeval-unknown))` | `:hints nil` |
| [Agda](../provers/agda.md#proof-completion) | `Hello.agda` | `= false` | `= refl` |
| [Metamath](../provers/metamath.md#proof-completion) | `hello.mm` | `vx vx distinct` | `vx vy distinct` |
| [Mizar](../provers/mizar.md#proof-completion) | `hello.miz` | `thus contradiction;` | `thus thesis;` |
| [PVS](../provers/pvs.md#proof-completion) | `hello.pvs` | `(skip)` | `(grind)` |

<!-- end-completion-examples -->

## Edit and check a saved file

Install the package from this checkout with `python -m pip install -e .` and install the native prover you want to use. Open VS Code on the same machine where its checker runs. On Windows with WSL, open the folder from your WSL terminal. [Platform and prover setup](../runtime/toolchains.md)

For example, to work on the Rocq theorem that $P$ implies itself, run these commands from the repository:

```bash
# Create the Rocq exercise once, including its checker task.
itpeval practice rocq
# Open the folder so VS Code can find .vscode/tasks.json.
code build/practice/rocq
```

1. Open `hello.v`. The theorem declares `P -> P`. Between `Proof.` and `Qed.` the starter says `exact I.`. Run **Terminal → Run Task → ITPEval: Check saved proof**. Rocq rejects the term because `I` proves `True`.
2. Replace `exact I.` with `exact (fun p => p).` and save. A proof of an implication is a function. Given a proof `p` of `P`, this function returns `p` itself.
3. Run the same task again. The terminal prints `rocq · itpeval_target · accepted`. The proof stays in the file you edited.

Use **File → Open Folder** if you prefer to open the folder from VS Code. To continue later, reopen that folder. The generated task checks the saved entrypoint against a local lock containing the original theorem, imports and toolchain identity. Keep the lock's cache on the machine that runs the task. Each prover guide also links to its editor tools for inspecting goals or diagnostics while you work. [VS Code tasks](https://code.visualstudio.com/docs/debugtest/tasks)

## Watch a prerecorded completion

Run the command with `--show-attempts` on a prover guide to replay its two supplied candidates. For Rocq, `exact I.` comes back rejected, and `exact (fun p => p).` comes back accepted. You can follow the same exchange in the browser using the recorded results.

The demo writes the final proof fragment to `final_candidate` in `episodes.jsonl`. Its `transitions` contain the submitted edits and native diagnostics. `repair.jsonl` pairs the unsuccessful edit and feedback with the successful correction for training. [Episode and training formats](../guides/verification-and-learning.md)

## Let a model or agent supply the proof

**For one model attempt**, configure a provider in the repository checkout. The command below sends the selected task to that provider and checks its reply with your local installation of Agda. Change `prover` to any of the ten IDs used in the individual guides. The prompt includes the surrounding source and the permitted edits for this exercise. [Configure a model provider](../benchmarks/translation.md#quick-start)

```bash
# Lock the example project and keep the exact environment used for the check.
prover=agda
mkdir -p build/model-completion
itpeval prepare "$prover" --cache ./cache > "build/model-completion/$prover-lock.json"
lock=$(python -c 'import json, sys; print(json.load(sys.stdin)["lock_path"])' < "build/model-completion/$prover-lock.json")
# Ask the configured provider for one proof fragment and check its response.
python -m eval.pipeline.completion "$lock" "build/model-completion/$prover.jsonl" --model claude-sonnet-4-6
```

The result stores the model’s proposed text in `generated`, the completion verdict in `task_success`, and the checker diagnostics in `evidence`. To try this with a theorem from your own project, prepare its sources and define the statement and editable region in a completion manifest. [Define a proof task](../reference/task-manifests.md)

**For an agent that revises a proof**, pass a `generate(task, history)` function to `itpeval.learning.rollouts.rollout`. On the first call, history is empty. On the next call, your agent can read the previous candidate and its checker output, then return an `Action("edit_document", raw_response, candidate)` containing a new fragment. ITPEval stops on success, an infrastructure failure, or the configured attempt limit. A runnable local example uses a short Python search function and saves every attempt. [Run the local search agent](../guides/verification-and-learning/search-with-an-agent.md#run-a-local-search-agent)
