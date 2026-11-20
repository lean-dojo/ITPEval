"""Read global facts and constant signatures from a freshly loaded HOL theory."""
from itertools import groupby
from pathlib import Path
import re
import shutil
from tempfile import TemporaryDirectory

from itpeval.corpus.storage import encode

from .native_io import NATIVE, evidence, line_span, observations, probe_environment


def _quote(value):
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def extract(ctx, entrypoint):
    entry = Path(entrypoint)
    if entry.suffix != ".thy":
        raise ValueError("Isabelle extraction requires a .thy entrypoint")
    out = ctx.root.parent / "isabelle-observations"
    env = probe_environment(ctx, USER_HOME=ctx.root.parent / "isabelle-home",
                            ITPEVAL_OUTPUT=out, ITPEVAL_ENTRY=entry.with_suffix(""))
    binary = ctx.prepared.prefix / "isabelle/bin/isabelle"
    release = re.search(r"Isabelle(\d{4})", ctx.prepared.build["version"])
    if release and int(release[1]) >= 2026:
        # A child theory sees the entrypoint and its imports after PIDE has
        # checked them. Keep all inspector files outside the user's sources.
        with TemporaryDirectory(dir=ctx.root, prefix="itpeval_") as tmp:
            probe = Path(tmp)
            theory = probe.name
            imported = "../" + entry.with_suffix("").as_posix()
            (probe / (theory + ".thy")).write_text(
                f'theory {theory} imports {_quote(imported)} begin\n'
                'ML_file "adapter.ML"\nML_file "inspector.ML"\nend\n', encoding="utf-8")
            shutil.copyfile(NATIVE / "isabelle.2026.ML", probe / "adapter.ML")
            shutil.copyfile(NATIVE / "isabelle.ML", probe / "inspector.ML")
            # Isabelle requires every local theory directory to be declared.
            directories = sorted({source.parent for source in ctx.root.rglob("*.thy")
                                  if source.parent != probe})
            dirs = " ".join(_quote(str(directory)) for directory in directories)
            (probe / "ROOT").write_text(
                f"session ITPEval_Extract = HOL +\n  directories {dirs}\n  theories {theory}\n",
                encoding="utf-8")
            env["ITPEVAL_PROJECT"] = str(ctx.root)
            ctx.run([binary, "build", "-D", probe, "-o", "quick_and_dirty=false",
                     "ITPEval_Extract"], env=env)
    else:
        ctx.run([binary, "process", "-l", "HOL", "-o", "quick_and_dirty=false",
                 "-f", NATIVE / "isabelle.legacy.ML", "-f", NATIVE / "isabelle.ML"], env=env)
    groups = {}
    for row in observations(out):
        if row[0] == "theory":
            _, name, filename, *parents = row
            path = Path(filename).relative_to(ctx.root).as_posix()
            groups[name] = (path, parents, [])
        else:
            groups[row[1]][2].append(row)

    constants, facts, exported, references = {}, {}, {}, []
    def visit(name):
        if name in exported:
            return exported[name]
        path, parents, declarations = groups[name]
        source = ctx.source(path)
        prior = []
        for parent in parents:
            if parent in groups:
                prior.extend(visit(parent))
            ctx.edge(path, "import", parent, ctx.sources.get(groups[parent][0]) if parent in groups else None)
        # Declarations at the same command position share its incoming context.
        ordered = sorted(declarations, key=lambda r: (int(r[5]), r[2]))
        for line, items in groupby(ordered, key=lambda r: int(r[5])):
            introduced = []
            for row in items:
                _, _, decl, kind, statement, _, status, hyps, deps, tree, native_hyps, consts = row
                start, end = line_span(source, line, line) if line else (0, len(source))
                context = ctx.context(path, imports=parents, visible=tuple(dict.fromkeys(prior)),
                                      hypotheses=hyps.split("\x00") if hyps else ())
                key = ctx.declare(path, decl, kind, statement, start, end, context, status,
                                  evidence=[evidence(ctx, row[:9])])
                (constants if kind == "constant" else facts)[decl] = key
                ctx.structures[key] = ctx.evidence(encode({
                    "format": "isabelle.term_xml.v1", "encoding": "yxml",
                    "type" if kind == "constant" else "proposition": tree,
                    "hypotheses": native_hyps.split("\x00") if native_hyps else []}))
                introduced.append(key)
                if deps:
                    references.extend((key, "proof_used_premise", premise) for premise in deps.split("\x00"))
                if consts:
                    references.extend((key, "statement_reference", ref) for ref in consts.split("\x00"))
            prior.extend(introduced)
        ctx.notes["succeeded"].append(path)
        exported[name] = prior
        return prior
    for name in groups:
        visit(name)
    for origin, kind, ref in references:
        ctx.edge(origin, kind, ref, (facts if kind == "proof_used_premise" else constants).get(ref))
    ctx.availability.update(dict.fromkeys(("names", "kinds", "statements", "proof_used_premises",
                                           "imports", "term_trees", "statement_references"), "observed"))
    ctx.availability.update(context="reconstructed", source_mapping="reconstructed")
