"""Read native .glob occurrences and query exported types after section discharge."""

import json
import re
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.corpus.storage import encode

_DECL = re.compile(r"^(\w+) (\d+):(\d+) (\S+) (\S+)$")
_REF = re.compile(r"^R(\d+):(\d+) (\S+) (\S+) (\S+) (\w+)$")
_EXPORTED = {"def", "prf", "ax", "ind", "constr", "class", "proj", "inst", "rec", "meth", "coind", "fix", "cofix"}


def extract(ctx, entrypoint):
    rocq = ctx.prepared.prefix / "rocq/bin/rocq"
    # -Q gives nested projects a predictable absolute logical module path.
    load_path = ["-Q", ".", "ITPProject"]
    if ctx.prepared.spec.options:
        raise ValueError("Rocq command options are unsupported by this extractor")
    for name, lib in ctx.prepared.library_paths:
        if not all(part.isidentifier() for part in name.split(".")):
            raise ValueError(f"invalid logical library path {name}")
        load_path.extend(["-Q", str(lib), name])
    files = sorted(p.relative_to(ctx.root).as_posix() for p in ctx.root.rglob("*.v"))
    if any(not re.fullmatch(r"[\w/]+\.v", p) for p in files):
        raise ValueError("unsupported Rocq project file name")
    deps, _ = ctx.run([rocq, "dep", *load_path, *files])
    graph = {}
    for line in deps.splitlines():
        if ": " in line and ".vo " in line:
            targets, dependencies = line.split(": ", 1)
            unit = str(Path(targets.split()[0]).with_suffix(".v"))
            graph[unit] = [str(Path(w).with_suffix(".v")) for w in dependencies.split()
                           if w.endswith(".vo") and str(Path(w).with_suffix(".v")) in files]

    visible = {}

    def visit(path):
        if path in visible:
            return
        imported = graph[path]
        for dep in imported:
            visit(dep)
        ctx.source(path)
        glob = Path(path).with_suffix(".glob")
        timing = ctx.root.parent / "rocq-timings"
        ctx.run([rocq, "compile", *load_path, "-time-file", timing, "-dump-glob", glob, path])
        spans = [(int(lo), int(hi)) for lo, hi in re.findall(
            r"^Chars (\d+) - (\d+) ", timing.read_text(), re.MULTILINE)]
        ide = rocq.resolve().with_name("coqidetop")
        if not spans or not ide.is_file():
            raise ValueError("RocqIDE or compiler sentence locations unavailable")
        timing.write_text(json.dumps(spans))
        output = ctx.root.parent / "rocq-goals"
        inspector = Path(__file__).with_name("native") / "rocq.py"
        ctx.run([sys.executable, inspector, ide.resolve(), path, timing, output, *load_path])
        ctx.structures[path + "#goals"] = ctx.evidence(encode(json.loads(output.read_bytes())))
        native = (ctx.root / glob).read_text()
        module = next(line[1:] for line in native.splitlines() if line.startswith("F"))
        if not re.fullmatch(r"[\w.]+", module):
            raise ValueError(f"invalid logical module {module!r}")
        imports, rows, scope_vars = [], [], []
        for line in native.splitlines():
            ref = _REF.fullmatch(line)
            if ref:
                start, end, owner, context, name, kind = ref.groups()
                if kind == "lib":
                    imports.append(owner)
                if kind == "sec":
                    scope = (context + ".") if context != "<>" else ""
                    scope_vars = [v for v in scope_vars if not v.startswith(scope)]
                continue
            m = _DECL.fullmatch(line)
            if not m:
                continue
            kind, start, end, scope, name = m.groups()
            if kind == "var":
                scope_vars.append((scope + "." if scope != "<>" else "") + name)
            if kind in _EXPORTED:
                full = ".".join(p for p in (module, scope, name) if p != "<>")
                if not all(part.isidentifier() or re.fullmatch(r"[\w']+", part)
                           for part in full.split(".")):
                    raise ValueError(f"unsupported Rocq identifier {full}")
                rows.append((kind, int(start), int(end) + 1, full, tuple(scope_vars), tuple(imports)))
            elif kind not in {"mod", "sec", "binder", "var"}:
                ctx.notes["skipped"].append(f"{path}:{start} ({kind} {name})")
        # The queries typecheck in a separate library so that the printed types
        # contain the generalized section variables seen by downstream clients.
        # .glob also records declarations in proofs that are later aborted.
        # Locate each candidate in the finished library before querying its type.
        with TemporaryDirectory(dir=ctx.root.parent) as tmp:
            query = Path(tmp) / "Locate.v"
            commands = [f"Require {module}."]
            for idx, (_, _, _, name, _, _) in enumerate(rows):
                commands.extend([f'Goal True. idtac "ITPEVAL_LOCATE_{idx}". Abort.', f"Locate {name}."])
            query.write_text("\n".join(commands) + "\n")
            located, _ = ctx.run([rocq, "compile", *load_path, query])
        checked_rows = []
        for idx, row in enumerate(rows):
            block = located.split(f"ITPEVAL_LOCATE_{idx}\n", 1)[1].split("ITPEVAL_LOCATE_", 1)[0]
            if block.startswith("No object of "):
                ctx.notes["skipped"].append(f"{path}:{row[1]} ({row[3]} absent from final library)")
            else:
                checked_rows.append(row)
        rows = checked_rows
        output = []
        driver = [f"Require {module}.", "Set Printing Width 100000."]
        for idx, (_, _, _, name, _, _) in enumerate(rows):
            driver.extend([f'Goal True. idtac "ITPEVAL_BEGIN_{idx}". Abort.',
                           f"Check @{name}.", 'Goal True. idtac "ITPEVAL_ASSUMPTIONS". Abort.',
                           f"Print Assumptions {name}.",
                           'Goal True. idtac "ITPEVAL_END". Abort.'])
        with TemporaryDirectory(dir=ctx.root.parent) as tmp:
            query = Path(tmp) / "Inspect.v"
            query.write_text("\n".join(driver) + "\n")
            stdout, _ = ctx.run([rocq, "compile", *load_path, query])
            for idx in range(len(rows)):
                head = f"ITPEVAL_BEGIN_{idx}\n"
                if head not in stdout:
                    raise ValueError(f"missing Rocq response for {rows[idx][3]}")
                chunk = stdout.split(head, 1)[1].split("\nITPEVAL_END", 1)[0]
                check, assumptions = chunk.split("\nITPEVAL_ASSUMPTIONS\n", 1)
                _, sep, statement = check.partition("\n     : ")
                if not sep:
                    raise ValueError(f"missing native Rocq type: {check}")
                output.append((statement.strip(), assumptions.strip()))
        own = []
        local = {Path(dep).with_suffix("").as_posix().replace("/", "."): dep for dep in imported}
        for name in dict.fromkeys(imports):
            dep = local.get(name.removeprefix("ITPProject."))
            ctx.edge(path, "import", name, ctx.sources.get(dep))
        for (kind, start, end, name, hypotheses, active_imports), (statement, axioms) in zip(rows, output):
            # A .glob "prf" may come from Admitted. Print Assumptions retains
            # that fact even if an opaque proof or another declaration uses it.
            status = ("kernel_checked" if axioms == "Closed under the global context"
                      else "compiled_with_assumptions")
            active = [local[a.removeprefix("ITPProject.")] for a in active_imports
                      if a.removeprefix("ITPProject.") in local]
            prior = list(dict.fromkeys(key for dep in active for key in visible[dep]))
            context = ctx.context(path, imports=active_imports, hypotheses=hypotheses, visible=prior + own)
            native_kind = kind
            symbols = [line.split(" :", 1)[0] for line in axioms.splitlines() if " :" in line]
            if kind == "ax" or any(name == symbol or name.endswith("." + symbol) for symbol in symbols):
                native_kind = "axiom"
                status = "assumption"
            evidence = ctx.evidence(encode({"type": statement, "assumptions": axioms, "glob_kind": kind}))
            key = ctx.declare(path, name, native_kind, statement, start, end, context, status, evidence=[evidence])
            own.append(key)
        ctx.structures[path] = ctx.evidence(native.encode())
        visible[path] = list(dict.fromkeys(key for dep in imported for key in visible[dep])) + own
        ctx.notes["succeeded"].append(path)

    visit(entrypoint)
    ctx.availability.update({k: "observed" for k in ("names", "kinds", "source_mapping", "statements", "imports")})
    ctx.availability["context"] = "reconstructed"
    ctx.availability.update(action_traces="observed", pending_goals="observed")
