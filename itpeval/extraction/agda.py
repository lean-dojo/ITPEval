"""Read Agda's definition anchors, inferred types and interaction goal diagnostics."""

import json
from html.parser import HTMLParser
from pathlib import Path
from tempfile import TemporaryDirectory
from urllib.parse import unquote

from itpeval.corpus.storage import encode


class _Anchors(HTMLParser):
    def __init__(self):
        super().__init__()
        self.data = []
        self.anchor = None
        self.definition = None

    def handle_starttag(self, tag, attrs):
        if tag == "a":
            self.anchor = dict(attrs)
            if "href" not in self.anchor and self.anchor.get("id", "").isnumeric() is False:
                self.definition = unquote(self.anchor.get("id", ""))
            elif self.definition:
                self.anchor["qualified_name"] = self.definition
                self.definition = None

    def handle_endtag(self, tag):
        if tag == "a":
            self.anchor = None

    def handle_data(self, data):
        if self.anchor:
            self.data.append((self.anchor, data))


def extract(ctx, entrypoint):
    agda = ctx.prepared.prefix / "agda/bin/agda"
    flags = ["--no-libraries", "--no-write-interfaces", "-i", str(ctx.root)]
    for _, library in ctx.prepared.library_paths:
        flags += ["-i", str(library)]
    if ctx.prepared.spec.options:
        raise ValueError("Agda command options are unsupported by this extractor")
    inspect_incomplete = ctx.prepared.spec.checking_profile == "inspect_incomplete"
    # HTML anchors identify the original declaration and carry Agda's classification.
    # ModuleContents reports quantified types, including hidden arguments.
    with TemporaryDirectory(dir=ctx.root.parent) as tmp:
        html = Path(tmp)
        ctx.run([agda, *flags, "--ignore-interfaces", "--html", "--html-dir=" + str(html), entrypoint])
        visible = {}

        def visit(path):
            if path in visible:
                return
            src = ctx.source(path).decode()
            module = ".".join(Path(path).with_suffix("").parts)
            document = module + ".html"
            parser = _Anchors()
            parser.feed((html / document).read_text())
            imports, rows = {}, []
            last = ""
            for anchor, spelling in parser.data:
                kind, ident = anchor.get("class", ""), anchor.get("id", "")
                link = unquote(anchor.get("href", ""))
                if kind == "Module" and last == "import" and link.endswith(".html"):
                    if not ident.isdigit():
                        raise ValueError(f"missing native import location in {path}")
                    imports.setdefault(link[:-5], len(src[:int(ident)-1].encode()))
                if (ident.isdigit() and link == document + "#" + ident
                        and kind in {"Function", "Datatype", "Record", "Field", "Primitive", "Postulate",
                                     "InductiveConstructor", "CoinductiveConstructor", "Generalizable"}):
                    pos = int(ident) - 1
                    if src[pos:pos + len(spelling)] != spelling:
                        raise ValueError(f"Agda source/anchor mismatch for {spelling}")
                    rows.append((anchor.get("qualified_name", spelling), kind, len(src[:pos].encode()), len(src[:pos+len(spelling)].encode())))
                last = spelling
            imported = {}
            for mod in imports:
                file = mod.replace(".", "/") + ".agda"
                if (ctx.root / file).is_file():
                    visit(file)
                    imported[mod] = file
                ctx.edge(path, "import", mod, ctx.sources.get(file))

            filename = json.dumps(str(ctx.root / path))
            commands = [f"Cmd_load {filename} []", "Cmd_metas AsIs", "Cmd_constraints AsIs"]
            scopes = list(dict.fromkeys(n.rpartition(".")[0] for n, *_ in rows))
            commands += ["Cmd_show_module_contents_toplevel AsIs " + json.dumps(scope, ensure_ascii=False)
                         for scope in scopes]
            driver = html / "queries"
            driver.write_text("".join(f"IOTCM {filename} None Direct ({command})\n" for command in commands))
            stdout, _ = ctx.run([agda, *flags, "--interaction-json"], stdin_path=driver)
            contents, goals, constraints = [], [], None
            for line in stdout.splitlines():
                message = line.removeprefix("JSON> ").strip()
                if not message:
                    continue
                event = json.loads(message)
                info = event.get("info", {})
                if not isinstance(info, dict):
                    continue
                if info.get("kind") == "Error":
                    raise ValueError(info["error"]["message"])
                if info.get("kind") == "ModuleContents":
                    contents.append({v["name"]: v["term"] for v in info["contents"]})
                if info.get("kind") == "Constraints":
                    constraints = info["constraints"]
                if info.get("kind") == "AllGoalsWarnings":
                    goals.append({key: info[key] for key in ("visibleGoals", "invisibleGoals", "errors")})
            if not goals or constraints is None:
                raise ValueError(f"missing Agda diagnostic response for {path}")
            incomplete = bool(any(goals[-1].values()) or constraints)
            diagnostics = {"goals": goals[-1], "constraints": constraints}
            diagnostic_id = ctx.evidence(encode(diagnostics))
            ctx.structures[path + "#interaction"] = diagnostic_id
            if incomplete and not inspect_incomplete:
                raise ValueError(f"Agda reported unresolved goals or unavailable goal information for {path}")
            if len(contents) != len(scopes):
                raise ValueError(f"missing Agda scope information for {path}")
            scope_types = dict(zip(scopes, contents))
            local = []
            for name, kind, start, end in rows:
                scope, _, short = name.rpartition(".")
                typ = scope_types[scope].get(short)
                if typ is None:
                    ctx.notes["skipped"].append(f"{path}: {name} has no exported type")
                    continue
                active = [mod for mod, position in imports.items() if position < start]
                earlier = [d for mod in active if mod in imported for d in visible[imported[mod]]]
                key = ctx.declare(path, module + "." + name, kind, typ, start, end,
                                  ctx.context(path, imports=active, visible=earlier + local),
                                  "incomplete_module" if incomplete else "postulate" if kind == "Postulate" else "typechecked",
                                  evidence=[ctx.evidence(encode({"type": typ, "goals": goals[-1]})), diagnostic_id])
                local.append(key)
            visible[path] = local
            ctx.notes["succeeded"].append(path)

        visit(entrypoint)
    ctx.availability.update({k: "observed" for k in ("names", "kinds", "source_mapping", "statements", "imports")})
    ctx.availability.update(context="reconstructed", pending_goals="observed", constraints="observed")
