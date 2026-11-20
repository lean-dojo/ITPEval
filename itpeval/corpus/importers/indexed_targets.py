"""Locate source declarations whose identifiers are supplied by the released indexes.

These are source-occurrence records. Native extraction supplies elaborated names,
types and proof evidence when the enclosing project is prepared and checked.
"""

import re
from collections import defaultdict
from pathlib import PurePosixPath

# Anchors only describe the surface declaration. In particular a value binding
# in an ML statement file can contain a quoted term instead of a kernel theorem.
_NAME = r"(?P<name>[^\s()[\]{}:;=$`]+)"
_PREFIX = r"^[ \t]*"
_HEADS = {
    "lean4": _PREFIX + r"(?:private\s+|protected\s+)?(?P<kind>theorem|lemma|axiom|def|abbrev|opaque)\s+" + _NAME,
    "rocq": _PREFIX + r"(?P<kind>Theorem|Lemma|Proposition|Corollary|Definition|Axiom|Parameter|Fact)\s+" + _NAME,
    "isabelle": _PREFIX + r"(?P<kind>lemma|theorem|corollary|definition|abbreviation)\s+" + _NAME,
    "metamath": _PREFIX + _NAME + r"\s+(?P<kind>\$a|\$p)\s+",
    "acl2": _PREFIX + r"\(\s*(?P<kind>defun-sk|defun|defthm|defthmd|defaxiom|defun-nx)\s+" + _NAME,
    "hol-light": r"^let\s+" + _NAME + r"\s*=",
    "hol4": r"^val\s+" + _NAME + r"\s*=",
    "agda": _PREFIX + _NAME + r"[ \t]*:[ \t]*(?P<kind>Set[₀-₉]*)(?=\s|$)",
    "pvs": _PREFIX + _NAME + r"[ \t]*(?:\[[^\]\n]*\][ \t]*)?:[ \t]*(?P<kind>bool(?:ean)?\s*=|conjecture|lemma|theorem|axiom|formula)(?=\s|$)",
    "mizar": _PREFIX + r"(?P<kind>theorem)\b(?:\s+(?P<name>[A-Za-z][\w']*)\s*:)?",
}
_FLAGS = {p: re.MULTILINE | (re.IGNORECASE if p in {"acl2", "pvs", "mizar"} else 0) for p in _HEADS}
HEADS = {p: re.compile(pattern, _FLAGS[p]) for p, pattern in _HEADS.items()}
# Mask non-code text while keeping every character offset and every newline.
_COMMENT = {"lean4": ("/-", "-/", "--"), "rocq": ("(*", "*)", None),
            "isabelle": ("(*", "*)", None), "hol-light": ("(*", "*)", None),
            "hol4": ("(*", "*)", None), "acl2": ("#|", "|#", ";"),
            "agda": ("{-", "-}", "--"), "mizar": (None, None, "::"),
            "pvs": (None, None, "%"), "metamath": ("$(", "$)", None)}
_QUOTE = {"isabelle": ('"', '‹', '›'), "hol-light": ('"', '`'), "hol4": ('"', '‘', '’', '“', '”'),
          "lean4": ('"',), "agda": ('"',), "acl2": ('"',), "pvs": ('"',), "rocq": ('"',)}
_CLOSE = {"‹": "›", "‘": "’", "“": "”", '\\<open>': '\\<close>'}
_TOKENS = {
    p: re.compile("|".join(re.escape(t) for t in (*comments, *_QUOTE.get(p, ()),
                  *(('\\<open>', '\\<close>') if p == "isabelle" else ())) if t))
    for p, comments in _COMMENT.items()
}


def _masked(src, prover):
    opening, closing, single = _COMMENT[prover]
    pattern = _TOKENS[prover]
    parts, at = [], 0
    while token := pattern.search(src, at):
        start, end = token.span()
        spelling = token[0]
        if spelling == opening:
            depth = 1
            while depth and (part := pattern.search(src, end)):
                end = part.end()
                if part[0] == closing:
                    depth -= 1
                elif part[0] == opening and prover != "metamath":
                    depth += 1
            if depth:
                end = len(src)
        elif spelling == single:
            end = src.find("\n", end)
            if end == -1:
                end = len(src)
        elif spelling in {'"', '`', '‹', '“', '‘', '\\<open>'}:
            stop = _CLOSE.get(spelling, spelling)
            while True:
                found = src.find(stop, end)
                if found == -1:
                    end = len(src)
                    break
                end = found + len(stop)
                if spelling == '"' and prover not in {"rocq", "pvs"} and found and src[found - 1] == "\\":
                    continue
                if spelling == '"' and prover == "rocq" and src[found + 1:found + 2] == '"':
                    end += 1
                    continue
                break
        parts.extend((src[at:start], re.sub(r"[^\n]", " ", src[start:end])))
        at = end
    return "".join([*parts, src[at:]])


def comment_only_metamath(raw):
    return not _masked(raw.decode(), "metamath").strip()


def identities(member, prover, indexes):
    dataset, item = member["source"], member["item_id"]
    index = indexes[dataset]
    path = f"data/{dataset}/data/index.json"
    if dataset == "babel-formal":
        for row in index["topics"][item]["items"]:
            yield row["name"], path, f"topics/{item}/items/{row['name']}"
    elif dataset == "hundred-theorems":
        entry = index["theorems"][item]["provers"].get(prover)
        if entry and entry.get("name"):
            yield entry["name"], path, f"theorems/{item}/provers/{prover}"
    elif dataset == "thousand-theorems":
        system = {"lean4": "lean", "hol-light": "hol_light"}.get(prover, prover)
        for entry in index["theorems"][item]["provers"].get(system, []):
            for name in entry.get("identifiers", ()):
                yield name, path, f"theorems/{item}/provers/{system}"
    elif dataset == "logipedia":
        name = item.replace("/", ".")
        if name in index["entries"]:
            yield name, path, f"entries/{name}"
    elif dataset == "verina":
        row = index["by_id"][item]
        yield row["signature"]["name"] + "_spec_satisfied", path, f"tasks/{item}/signature"
    else:
        name = PurePosixPath(item).name
        if dataset == "ntp4vc":
            goal = re.search(r"(?:^|_)(goal\d+)$", name)
            if goal:
                name = goal[1]
        yield name, None, str(member["theorem_id"])


def _aliases(name, prover, dataset):
    result = {name, name.rsplit(".", 1)[-1], name.replace(".", "_")}
    if prover in {"agda", "metamath", "acl2"}:
        result.update(n.replace("_", "-").replace(".", "-") for n in tuple(result))
    if prover in {"acl2", "metamath"}:
        result.update(dataset + "-" + n for n in tuple(result))
    if prover in {"pvs", "rocq", "lean4", "isabelle", "hol4"}:
        result.update(dataset.replace("-", "_") + "_" + n for n in tuple(result))
        result.update(n + "_statement" for n in tuple(result))
    if prover == "acl2":
        result.update(n + "-statement" for n in tuple(result))
    lower = prover in {"acl2", "pvs", "mizar"}
    return {s.casefold() if lower else s for s in result}


def locate(raw, digest, member, prover, indexes, membership, metadata):
    src = raw.decode()
    masked = _masked(src, prover)
    heads = list(HEADS[prover].finditer(masked))
    lower = prover in {"acl2", "pvs", "mizar"}
    spans = defaultdict(list)
    for m in heads:
        name = m["name"]
        if name:
            spans[name.casefold() if lower else name].append(m)
    result = {}

    def record(m, authority, key, basis, identifier):
        name = m["name"]
        left, right = m.span("name") if name else m.span("kind")
        start = len(src[:left].encode())
        end = start + len(src[left:right].encode())
        kind = {"hol-light": "OCaml value binding", "hol4": "SML value binding"}.get(prover)
        if not kind:
            kind = m["kind"]
        if prover == "agda":
            if not re.search(r"^[ \t]*" + re.escape(name) + r"[ \t]*=", masked, re.MULTILINE):
                return
            kind = "type-valued definition"
        if prover == "pvs" and "=" in kind:
            kind = "Boolean constant definition"
        result[left] = {"name": name, "actual_kind": kind, "benchmark_role": "target_specification",
                        "checking_status": "statement_only", "evidence_sha256": digest,
                        "start_byte": start, "end_byte": end, "basis": basis,
                        "authority_path": authority, "authority_key": key, "authority_sha256": metadata[authority],
                        "authority_identifier": identifier}

    for name, authority, key in identities(member, prover, indexes):
        matches = [m for candidate in _aliases(name, prover, member["source"]) for m in spans[candidate]]
        if len(matches) == 1:
            matched = matches[0]["name"]
            exact = matched.casefold() == name.casefold() if lower else matched == name
            if not exact:
                basis = "released_name_alias"
            elif member["source"] in {"ntp4vc", "verina"}:
                basis = "indexed_task_naming"
            elif authority is None:
                basis = "membership_identifier"
            else:
                basis = "released_identifier"
            record(matches[0], authority or membership, key, basis, name)
    if not result:
        # Keep weaker evidence distinguishable from a named index match. The
        # membership is a statement artifact. A unique proposition or explicitly
        # named statement binding can locate it even if the translation renamed it.
        item_key = str(member["theorem_id"])
        named_statement = [m for m in heads if m["name"] and
                           (m["name"].casefold() == "statement" or
                            m["name"].casefold().endswith(("-statement", "_statement")))]
        if len(named_statement) == 1:
            record(named_statement[0], membership, item_key, "explicit_statement_binding", None)
        elif prover == "metamath":
            logical = [m for m in heads if masked[m.end():].lstrip().startswith("|- ")]
            if len(logical) == 1:
                record(logical[0], membership, item_key, "sole_logical_assertion", None)
        elif prover in {"lean4", "rocq", "isabelle", "mizar", "pvs"}:
            theorem_kinds = {"theorem", "lemma", "proposition", "corollary", "fact", "conjecture", "formula"}
            proved = [m for m in heads if m["kind"].casefold() in theorem_kinds]
            if len(proved) == 1:
                record(proved[0], membership, item_key, "sole_proposition_declaration", None)
    return [result[i] for i in sorted(result)]
