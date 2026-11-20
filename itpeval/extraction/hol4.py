"""Read the native DB after Holmake builds the project's exported theories."""
from collections import defaultdict
from itertools import groupby
from pathlib import Path

from itpeval.corpus.storage import encode

from .native_io import NATIVE, evidence, line_span, observations, probe_environment


def extract(ctx, entrypoint):
    script = Path(entrypoint)
    if script.parent != Path(".") or not script.name.endswith("Script.sml"):
        raise ValueError("HOL4 extraction expects a top-level NAME-Script file (NAME followed by Script.sml)")
    if (ctx.root / ".hol").exists():
        raise ValueError("prepare HOL4 sources without candidate build outputs")
    theory = script.name.removesuffix("Script.sml")
    out = ctx.root.parent / "hol4-observations"
    env = probe_environment(ctx, ITPEVAL_THEORY=theory, ITPEVAL_OUTPUT=out)
    tools = ctx.prepared.prefix / "hol4/bin"
    ctx.run([tools / "Holmake", f"{theory}Theory.uo"], env=env)
    ctx.run([tools / "hol", "run", NATIVE / "hol4.sml"], env=env)
    groups, exported = {}, {}
    trees = defaultdict(lambda: defaultdict(list))
    for row in observations(out):
        if row[0] == "theory":
            _, name, *parents = row
            groups[name] = (parents, [])
        elif row[0] == "term":
            _, theory_name, name, component, path, typ, kind, *ident = row
            trees[theory_name, name][component].append(
                {"path": path, "type": typ, "kind": kind, "identifier": ident})
        else:
            groups[row[1]][1].append(row)
    def visit(name):
        if name in exported:
            return exported[name]
        parents, rows = groups[name]
        path = f"{name}Script.sml"
        source = ctx.source(path)
        prior = []
        for parent in parents:
            if parent in groups:
                prior.extend(visit(parent))
            ctx.edge(path, "import", parent, ctx.sources.get(f"{parent}Script.sml"))
        public = []
        # Earlier commands on known lines contribute premises. Same-line and
        # unlocated exports cannot be ordered by their occurrence in the DB.
        located = sorted((row for row in rows if int(row[5])), key=lambda r: (int(r[5]), r[2]))
        unlocated = sorted((row for row in rows if not int(row[5])), key=lambda r: r[2])
        for line, entries in groupby([*located, *unlocated], key=lambda r: int(r[5])):
            incoming = tuple(dict.fromkeys(prior + public)) if line else prior
            introduced = []
            for row in entries:
                _, _, decl, kind, statement, _, _, _, _, private, *hyps = row
                start, end = line_span(source, line, line) if line else (0, len(source))
                context = ctx.context(path, imports=parents, visible=incoming, hypotheses=hyps)
                status = "axiom" if kind == "axiom" else "exported_theorem_value"
                key = ctx.declare(path, f"{name}.{decl}", kind, statement, start, end, context,
                                  status, evidence=[evidence(ctx, row)])
                ctx.structures[key] = ctx.evidence(encode({"format": "hol4.kernel-term.v1",
                                                          "terms": trees[name, decl]}))
                if private == "false":
                    introduced.append(key)
            public.extend(introduced)
        exported[name] = list(dict.fromkeys(prior + public))
        ctx.notes["succeeded"].append(path)
        return exported[name]
    visit(theory)
    ctx.availability.update(dict.fromkeys(("names", "kinds", "statements", "imports", "term_trees"), "observed"))
    ctx.availability.update(context="reconstructed", source_mapping="reconstructed")
