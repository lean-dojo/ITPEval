"""Inspect typechecked PVS theory objects, including generated TCC origins."""
from collections import defaultdict
from pathlib import Path

from itpeval.corpus.storage import encode

from .native_io import NATIVE, evidence, line_span, observations, probe_environment


def extract(ctx, entrypoint):
    entry = Path(entrypoint)
    if entry.suffix != ".pvs":
        raise ValueError("PVS extraction requires a .pvs entrypoint")
    # A context or binary from another proof attempt can carry stale proof status.
    if any(p.name in {".pvscontext", "pvsbin"} for p in ctx.root.rglob("*")):
        raise ValueError("prepare the PVS sources without a saved PVS context")
    out = ctx.root.parent / "pvs-observations"
    env = probe_environment(ctx, ITPEVAL_ENTRY=entry.with_suffix(""), ITPEVAL_OUTPUT=out,
                            PVS_LOG_DIR=ctx.root.parent / "pvs-log", PVSMINUSQ="t")
    ctx.run([ctx.prepared.prefix / "pvs/bin/pvs", "-raw", "-L", NATIVE / "pvs.lisp",
             "-E", "(progn (itpeval-extract) (bye))"], env=env)
    paths, ids, references = {}, {}, []
    parameters = defaultdict(list)
    for row in observations(out):
        if row[0] == "theory":
            _, theory, filename, *bindings = row
            imports = list(zip(bindings[::3], bindings[1::3], bindings[2::3]))
            path = str(entry.parent / (filename + ".pvs"))
            source = ctx.source(path)
            paths[theory] = path
            own = []
            import_ids = defaultdict(list)
            if path not in ctx.notes["succeeded"]:
                ctx.notes["succeeded"].append(path)
            for spelling, target, _ in imports:
                ctx.edge(path, "import", spelling, ctx.sources.get(paths.get(target)))
            continue
        if row[0] == "visible-import":
            _, _, spelling, module, identifier, position = row
            imported = ids.get((module, identifier, position))
            if imported is not None:
                import_ids[spelling].append(imported)
            continue
        if row[0] == "parameter":
            _, theory, name, kind, statement, place = row
            parameters[theory].append({"name": name, "kind": kind.lower(), "statement": statement, "place": place})
            continue
        if row[0] == "reference":
            _, theory, name, place, target_theory, target, location = row
            references.append(((theory, name, place), "declaration_reference", (target_theory, target, location)))
            continue
        _, theory, name, kind, statement, spelling, position, owner, owner_position, *arguments = row
        if not position:
            ctx.notes["skipped"].append(f"{theory}.{name} has no source location")
            continue
        first, col, last, end_col = map(int, position.split())
        start, end = line_span(source, first, last, col, end_col)
        def before(place, limit=(first, col)):
            return not place or tuple(map(int, place.split()[:2])) < limit

        active = [(text, parent) for text, parent, place in imports if before(place)]
        prior = [key for spelling, _ in active for key in import_ids[spelling]]
        formals = [p["statement"] for p in parameters[theory] if before(p["place"])]
        context = ctx.context(path, imports=[text for text, _ in active], hypotheses=formals + arguments,
                              visible=list(dict.fromkeys(prior + own)))
        status = "generated_obligation" if owner else "typechecked"
        key = ctx.declare(path, f"{theory}.{name}", kind.lower(), statement, start, end,
                          context, status, evidence=[evidence(ctx, row)])
        ids[theory, name, position] = key
        if owner:
            references.append(((theory, owner, owner_position), "generated_obligation", (theory, name, position)))
        else:
            own.append(key)
        ctx.structures[key] = ctx.evidence(encode({"format": "pvs.declaration.v1", "theory_parameters": formals,
                                                  "declaration_parameters": arguments, "formula_kind": spelling}))
    for source_key, relation, target_key in references:
        origin = ids.get(source_key)
        if origin:
            ctx.edge(origin, relation, ".".join(target_key[:2]), ids.get(target_key))
        else:
            ctx.notes["skipped"].append(f"{source_key[0]}.{source_key[1]}: reference source unavailable")
    ctx.availability.update(dict.fromkeys(("names", "kinds", "source_mapping", "statements", "parameters",
                           "imports", "generated_obligations", "declaration_references"), "observed"))
    ctx.availability["context"] = "reconstructed"
