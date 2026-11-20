"""Read accommodated MML articles, registrations and checked trees from native verifier XML."""

import re
import xml.etree.ElementTree as ET
from collections import defaultdict
from pathlib import Path


def extract(ctx, entrypoint):
    if ctx.prepared.spec.options:
        raise ValueError("Mizar command options are unsupported by this extractor")
    tool = ctx.prepared.prefix / "mizar/bin"
    mizfiles = ctx.prepared.prefix / "mizar/vendor/mizfiles"
    env = {}
    if ctx.prepared.library_paths:
        libraries = dict(ctx.prepared.library_paths)
        if set(libraries) != {"mizfiles"}:
            raise ValueError("Mizar accepts a single library role named mizfiles")
        tool = ctx.prepared.prefix / "mizar/vendor/bin"
        mizfiles = libraries["mizfiles"]
        env = {"MIZFILES": str(mizfiles), "PATH": str(tool) + ":/usr/bin:/bin"}
    visited, theorem_ids = {}, {}

    def visit(path):
        if path in visited:
            return visited[path]
        stem = Path(path).with_suffix("")
        base = ctx.root / stem
        suffixes = (".xml", ".evl", ".idx", ".err", ".wsx", ".atr", ".eth", ".ecl")
        for suffix in suffixes:
            base.with_suffix(suffix).unlink(missing_ok=True)
        raw = ctx.source(path)
        ctx.run([tool / "makeenv", stem], env=env)
        ctx.run([tool / "verifier", "-x", stem], env=env)
        errors = base.with_suffix(".err").read_bytes()
        if errors.strip():
            raise ValueError(f"Mizar reported article errors: {errors[:600]!r}")
        article = ET.parse(base.with_suffix(".xml")).getroot()
        aid = article.attrib["aid"]
        syntax = ET.parse(base.with_suffix(".wsx")).getroot()
        names = {sym.get("nr"): sym.get("name") for sym in ET.parse(base.with_suffix(".idx")).getroot()
                 if sym.get("kind") == "I"}
        # Store the native dictionaries that interpret formula and reference numbers.
        for suffix in suffixes:
            file = base.with_suffix(suffix)
            if file.is_file() and suffix != ".err":
                ctx.structures[path + suffix] = ctx.evidence(file.read_bytes())
        external = {}
        if base.with_suffix(".eth").exists():
            for thm in ET.parse(base.with_suffix(".eth")).getroot().findall("Theorem"):
                index = thm.get("articlenr"), thm.get("kind"), thm.get("nr")
                article_id, kind, nr = thm.get("aid"), thm.get("kind"), thm.get("nr")
                external[index] = article_id + (":def " if kind == "D" else ":") + nr
        imports = defaultdict(set)
        for directive in ET.parse(base.with_suffix(".evl")).getroot().findall("Directive"):
            for ident in directive.findall("Ident"):
                imports[ident.attrib["name"]].add(directive.attrib["name"])
        visible = []
        for mod, roles in imports.items():
            sibling = str(Path(path).with_name(mod.lower() + ".miz"))
            installed = mizfiles / "mml" / (mod.lower() + ".miz")
            if sibling != path and (ctx.root / sibling).is_file():
                if not installed.is_file() or (ctx.root / sibling).read_bytes() != installed.read_bytes():
                    raise ValueError(f"{sibling} differs from MML article used in accommodation")
                visible.extend(key for category, key in visit(sibling) if category in roles)
            ctx.edge(path, "import", mod, ctx.sources.get(sibling))
        local, by_nr = [], {}
        by_pos = {(n.get("line"), n.get("col")): n for n in syntax.findall("Item")}
        lines = raw.splitlines(keepends=True)
        starts = [0]
        for line in lines:
            starts.append(starts[-1] + len(line))
        ordinal = 0
        for node in article:
            item = by_pos.get((node.get("line"), node.get("col")))
            records = []
            if node.tag == "JustifiedTheorem":
                ordinal += 1
                prop = node.find("Proposition")
                records.append(("theorems", names.get(prop.get("vid")) or "Th" + str(ordinal),
                                node.tag, next(iter(prop)), node, item, b"theorem"))
            elif node.tag == "RegistrationBlock" and item is not None:
                clusters = item.findall("./Block/Item[@kind='Cluster']")
                registered = [(r, cl) for r in node.findall("Registration")
                              for cl in r if cl.tag in {"CCluster", "RCluster", "FCluster"}]
                if len(clusters) == len(registered):
                    for (reg, cl), locus in zip(registered, clusters):
                        records.append(("registrations", cl.tag + cl.attrib["nr"], cl.tag,
                                        cl, reg, locus, b"cluster"))
            elif node.tag == "DefinitionBlock" and item is not None:
                constructors = [(d, c) for d in node.findall("Definition") for c in d.findall("Constructor")]
                loci = [s for s in item.findall("./Block/Item") if s.get("kind", "").endswith("-Definition")]
                if len(loci) == len(constructors):
                    for (definition, c), locus in zip(constructors, loci):
                        kind = "constructor_redefinition" if c.get("redefnr") else "constructor"
                        records.append(("constructors", c.attrib["kind"] + c.attrib["nr"], kind,
                                        c, definition, locus, None))
            if not records and node.tag != "Section":
                ctx.notes["skipped"].append(f"{path}: {node.tag}")
            for role, name, kind, term, evidence, locus, keyword in records:
                line = int(locus.attrib["line"]) - 1
                anchor = starts[line] + int(locus.attrib["col"])
                if keyword:
                    start = anchor - len(keyword)
                    if raw[start:anchor].lower() != keyword:
                        raise ValueError(f"could not align source for {aid}.{name}")
                else:
                    # The native .wsx column marks the last byte of the introducer.
                    token = re.search(rb"[A-Za-z]+$", raw[starts[line]:anchor])
                    if token is None:
                        raise ValueError(f"invalid constructor locus for {aid}.{name}")
                    start = starts[line] + token.start()
                end = starts[int(locus.attrib["posline"]) - 1] + int(locus.attrib["poscol"])
                markers = re.findall(rb"(?im)^\s*::\$P([+-])\s*$", raw[:end])
                incomplete = evidence.find(".//SkippedProof") is not None or (markers and markers[-1] == b"-")
                key = ctx.declare(path, aid + "." + name, kind, ET.tostring(term, encoding="unicode").strip(),
                                  start, end, ctx.context(path, imports=imports, visible=visible),
                                  "statement_only" if incomplete else "article_checked",
                                  evidence=[ctx.evidence(ET.tostring(evidence))])
                for ref in evidence.iter("Ref"):
                    number = ref.get("nr"), ref.get("vid")
                    if ref.get("articlenr") is None:
                        ctx.edge(key, "justification_reference", names.get(ref.get("vid"), "local:" + ref.attrib["nr"]),
                                 by_nr.get(number))
                    else:
                        index = ref.get("articlenr"), ref.get("kind"), ref.get("nr")
                        target = external.get(index)
                        ctx.edge(key, "justification_reference", target or ET.tostring(ref, encoding="unicode").strip(),
                                 theorem_ids.get(target))
                if role == "theorems":
                    prop = node.find("Proposition")
                    if prop.get("nr") and prop.get("vid"):
                        by_nr[(prop.get("nr"), prop.get("vid"))] = key
                    theorem_ids[f"{aid}:{ordinal}"] = key
                visible.append(key)
                local.append((role, key))
        visited[path] = local
        ctx.notes["succeeded"].append(path)
        return local

    visit(entrypoint)
    ctx.availability.update({k: "observed" for k in ("names", "kinds", "statements", "imports",
                            "source_mapping", "term_trees", "registrations", "justification_references")})
    ctx.availability["context"] = "reconstructed"
