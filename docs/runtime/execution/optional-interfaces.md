# Optional native interfaces

## Optional Lean tools

LeanDojo-v2’s `ExtractData.lean` produced a command AST, premises and a tactic trace on Lean 4.35.0. Register it as `toolchain_inputs={"leandojo_tracer": path}`, then call `itpeval.backends.lean4.tools.leandojo_trace(prepared, entrypoint)` on one module with prebuilt imports. [LeanDojo-v2 revision](https://github.com/lean-dojo/LeanDojo-v2/tree/f3b01b180e7429ed5389c2409ed14ce9ede93987)

The pinned PyPantograph uses Pantograph 0.3.19. Its source declares Lean 4.33.1, and the recorded build passed all 44 targets on Lean 4.35.0. Register the executable as `toolchain_inputs={"pantograph": path}`. `pantograph_trace(prepared, expression, actions)` takes a prior state index and tactic for each action. The trial solves the same parent goal two ways. IDs expire when the process closes. [Pantograph source](https://github.com/leanprover/Pantograph/tree/0ee70917fb93a5421157119362ecde806a4d881b) · [Build and trace record](../../../benchmarks/runtime/evidence/lean4/optional-tools.json)

## Reproduce the optional native interfaces

### Lean

The commands below build the optional Lean tools against the installed Lean 4.35.0 distribution. Set `ITPEVAL_PREFIX` to the absolute path of that installation, set `ITPEVAL_CHECKOUT` to the source checkout and run the commands in an empty working directory.

```sh
# Use the instrument revision that matches this Lean integration.
git clone https://github.com/stanford-centaur/PyPantograph.git
git -C PyPantograph checkout a098035e29f7910a627b8440145b51246ec38484
git -C PyPantograph submodule update --init src
test "$(git -C PyPantograph/src rev-parse HEAD)" = 0ee70917fb93a5421157119362ecde806a4d881b
git clone https://github.com/lean-dojo/LeanDojo-v2.git
python "$ITPEVAL_CHECKOUT/scripts/install_optional_runtime.py" lean4 --prefix "$ITPEVAL_PREFIX" \
    --pantograph PyPantograph/src --leandojo LeanDojo-v2
```

### Rocq

This Pétanque build uses coq-lsp 0.2.5+9.1, Rocq 9.1.1 and an OCaml 4.14.2 switch. The installer exports the shell and matching core libraries, findlib metadata and plugins. Register them with the `petanque` and `petanque_runtime` input roles.

```sh
# Install the Rocq interaction tools in an isolated opam switch.
opam switch create itpeval-petanque ocaml-base-compiler.4.14.2
opam install --switch itpeval-petanque rocq-runtime.9.1.1 coq-lsp.0.2.5+9.1
python scripts/install_optional_runtime.py rocq --prefix "$ITPEVAL_PREFIX" \
    --opam-switch "$(opam var --switch itpeval-petanque prefix)"
PYTHONPATH=. python benchmarks/runtime/interaction.py --prover rocq --prefix "$ITPEVAL_PREFIX" \
    --cache build/petanque/cache --output build/petanque/evidence \
    --report build/petanque/qualification.jsonl
```

`itpeval.backends.rocq.interaction.command_trace(task, commands, prepared=env)` accepts a tactic or a pair of prior state index and tactic. It returns native goals, context, focus, shelved and given-up goals, and errors. IDs expire when the shell closes. The trial solves one goal in two branches and records an incorrect attempt. Final verification runs a fresh Rocq compilation. [Pétanque trace](../../../benchmarks/runtime/evidence/rocq/native-interaction.json)

For subgoal editing, see the built-in HOL tactic and PVS command interfaces. [HOL subgoal walkthrough](../hol-and-pvs-interaction.md#edit-one-hol-subgoal-at-a-time) · [PVS walkthrough](../hol-and-pvs-interaction.md#branch-and-restore-a-pvs-proof)
