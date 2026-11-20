# Native prover harness

Use the [installation guide](../docs/runtime/toolchains.md) for platform setup, supported releases, and toolchain selection. The checkout entrypoint `./itpeval/bin/itpeval` calls the Python CLI in `itpeval/cli/`.

## Quickstart (macOS)

Run `./itpeval/bin/bootstrap-macos.sh` for Homebrew build dependencies, then install the provers you need. ACL2 can use an existing installation through `ACL2_HOME`. See the setup guide for Mizar’s native platform requirements.

## Quickstart (Amazon Linux 2023)

Run `./itpeval/bin/bootstrap-system.sh` on Amazon Linux 2023. Install or check any subset of the built-in provers.

```bash
# Install and smoke-check two adapters from the repository root.
./itpeval/bin/itpeval install rocq metamath
./itpeval/bin/itpeval check --task hello rocq metamath
```

## What “check” means

`--task hello` runs each adapter’s own smoke fixture. Without `--task`, `check` uses the shared `arith_2_plus_2` task. Use `itpeval report` to read the run summary. Run directories retain `results.jsonl`, `summary.json`, and native logs. See the [CLI reference](../docs/reference/cli.md) for checking your own project and verifying a fixed target.

## Supported provers

Run `./itpeval/bin/itpeval list-provers` or browse the [adapter directory](provers/) for `adapter.json`, `install.sh`, `check.sh`, `version.sh`, and `hello/` fixtures.

## One-file “run any ITP” runner

```bash
# Let the adapter wrap the lemma as an Isabelle theory.
./itpeval/bin/itpeval eval --prover isabelle --mode snippet \
  --code 'lemma t: "(2::nat) + 3 = 5" by simp'
```

Use `--file` for a complete source file or `--task-dir` for an existing native layout. Agda derives the file path from the module name, PVS uses the theory name, and HOL4 wraps the supplied SML in a theory. [Check a file with the Python API or CLI](../docs/start/quickstart.md#check-a-file)

## Shared cache

`manifest.json` records shared downloads. The helper in `bin/common.sh` verifies a cached file against its expected hash when supplied. Set `ITPEVAL_DOWNLOAD_CACHE` to reuse downloads outside the checkout.

## Per-prover notes

The [adapter scripts](provers/) define version and mirror overrides. For existing installations, the HOL Light, HOL4, ACL2, PVS, and Mizar adapters support native home-directory overrides. Rocq can use a separate `ITPEVAL_ROCQ_OPAMROOT`. Mizar checks a disposable copy so that verifier annotations stay out of the supplied source.
