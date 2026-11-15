# Mizar adapter

This directory contains the Mizar adapter for `ITPEval`.

Files:
- `install.sh`: installs an official Linux bundle or wires an existing Mizar tree into `ITPEVAL_PREFIX/mizar`
- `check.sh`: checks one `.miz` article with `mizf` or `verifier`
- `hello/`: minimal article layout using `text/` and `dict/`

Supported inputs:
- `MIZAR_HOME` / `ITPEVAL_MIZAR_HOME`
- `ITPEVAL_MIZAR_SRC`
- `MIZFILES` / `ITPEVAL_MIZFILES`
- `MIZAR_TARBALL` / `ITPEVAL_MIZAR_TARBALL`
- `ITPEVAL_MIZAR_TARBALL_URL`
- `ITPEVAL_TMPDIR` for disposable verification files

Task layout:
- put exactly one `.miz` file in the task root or `text/`; or
- set `ITPEVAL_TASK_FILE` to a relative path inside `ITPEVAL_TASK_DIR`.

`check.sh` verifies a disposable task copy because Mizar's `errflag` tool
annotates erroneous source files in place. A nonempty `.err` file is treated as
failure even if the `mizf` shell driver exits successfully.

For statement-only evaluation, use Mizar's proof parser pragma and omit an
article-level closing `end;`:

```mizar
environ
  vocabularies ...;

begin

::$P-
theorem
  <statement>
proof
end;
::$P+
```

Notes:
- Official binaries are available for Linux/x86.
- The adapter accepts both legacy and current database layouts. The Mizar
  database root must contain `abstr/` and at least one of `prel/`, `mml/`, or
  `dict/`.
- If the installer cannot infer `MIZFILES`, set it explicitly.
