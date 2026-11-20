"""Inspect top-level OCaml theorem bindings after HOL Light loads a project."""
from collections import defaultdict
from pathlib import Path

from .native_io import NATIVE, evidence, observations, probe_environment


def extract(ctx, entrypoint):
    if Path(entrypoint).suffix != ".ml":
        raise ValueError("HOL Light extraction requires an OCaml .ml entrypoint")
    out = ctx.root.parent / "hol-light-observations"
    env = probe_environment(ctx, ITPEVAL_PROJECT=ctx.root, ITPEVAL_ENTRY=entrypoint,
                            ITPEVAL_OUTPUT=out)
    ctx.run([ctx.prepared.prefix / "hol-light/bin/hollight-run", NATIVE / "hol_light.ml"], env=env)
    imports, visible = defaultdict(list), {}
    # File-loader entry and exit snapshots preserve the actual sequence of
    # loaded bindings, including imports in the middle of an OCaml file.
    for row in observations(out):
        if row[0] == "source":
            path = row[1]
            ctx.source(path)
            if path not in ctx.notes["succeeded"]:
                ctx.notes["succeeded"].append(path)
        elif row[0] == "import":
            imports[row[1]].append(row[2])
            ctx.edge(row[1], "import", row[2], ctx.sources[row[2]])
        else:
            _, path, name, kind, conclusion, begin, end, constant, *hypotheses = row
            prior = [d for n, d in visible.items() if n != name]
            context = ctx.context(path, imports=imports[path], visible=prior, hypotheses=hypotheses)
            if kind == "axiom":
                status = "axiom"
            elif hypotheses:
                status = "theorem_with_hypotheses"
            else:
                status = "kernel_theorem_value"
            key = ctx.declare(path, name, kind, conclusion, int(begin), int(end), context, status,
                              evidence=[evidence(ctx, row)])
            if constant:
                ctx.edge(key, "defines_constant", constant)
            visible[name] = key
    ctx.availability.update(dict.fromkeys(("names", "kinds", "statements", "source_mapping",
                                           "imports", "definition_registrations"), "observed"))
    ctx.availability["context"] = "reconstructed"
