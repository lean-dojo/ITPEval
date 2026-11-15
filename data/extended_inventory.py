"""Deterministic identities and exports for the audited ten-prover corpus."""
from __future__ import annotations

import hashlib
import json
import os
import re
from collections import defaultdict
from pathlib import Path, PurePosixPath

EXTENSIONS = {
    "lean4": ".lean", "rocq": ".v", "isabelle": ".thy", "hol-light": ".ml",
    "acl2": ".lsp", "agda": ".agda", "hol4": ".sml", "metamath": ".mm",
    "mizar": ".miz", "pvs": ".pvs",
}
EXPECTED = {
    "babel-formal": 15, "hundred-theorems": 100, "minif2f": 455,
    "putnambench": 657, "ntp4vc": 597, "logipedia": 394,
    "thousand-theorems": 227, "verina": 189,
}
MINIF2F_ALIASES = {
    "test/imo_2007_p6": "test/imosl_2007_algebra_p6",
    "test/imo_2007_a6": "test/imosl_2007_algebra_p6",
    "test/induction_sumkexp3eqsumksqsq": "test/induction_sumkexp3eqsumksq",
    "test/numbertheory_notequiv2i2jasqbsqdiv8": "test/numbertheory_notEquiv2i2jasqbsqdiv8",
    "valid/aimeI_2001_p3": "valid/aimeII_2001_p3",
    "valid/aime_1997_p12": "valid/aime_1997_p11",
    "valid/amc12a_2020_p22": "valid/amc12a_2020_p21",
    "valid/imo_2006_p6": "valid/imo_2006_p3",
    "valid/imo_2006_a6": "valid/imo_2006_p3",
}


def canonical_key(dataset: str, key: str) -> str | None:
    if dataset in {"hundred-theorems", "thousand-theorems"}:
        pattern = r"(\d{3})_.+" if dataset == "hundred-theorems" else r"(Q\d+[A-Z]*)_.+"
        match = re.fullmatch(pattern, key)
        if match is None:
            return None  # support modules are not benchmark items
        return str(int(match[1])) if dataset == "hundred-theorems" else match[1]
    if dataset == "minif2f":
        return MINIF2F_ALIASES.get(key, key)
    if dataset == "ntp4vc":
        return re.sub(r"/X_", "/_", key)
    return key


def scan(root: Path, dataset: str, prover: str) -> dict[str, list[Path]]:
    base = root / "data" / dataset / "data/stmts" / prover
    result = defaultdict(list)
    for directory, dirs, files in os.walk(base, followlinks=True):
        dirs.sort()
        for filename in sorted(files):
            path = Path(directory) / filename
            if path.suffix != EXTENSIONS[prover]:
                continue
            key = canonical_key(dataset, path.relative_to(base).with_suffix("").as_posix())
            if key is not None:
                result[key].append(path)
    return dict(result)


def ntp_key(line: str) -> str:
    path = PurePosixPath(line.strip())
    if (path.parts[:2] != ("data", "why3") or len(path.parts) < 6
            or path.parts[-2] != "lean" or not path.parts[-3].endswith("_vcg")):
        raise ValueError(f"invalid nTP4VC selection entry: {line!r}")
    return PurePosixPath(path.parts[2], *path.parts[3:-3], path.stem).as_posix()


def inventory(root: Path) -> tuple[dict, dict]:
    maps, pools = {}, {}
    for dataset, count in EXPECTED.items():
        maps[dataset] = {pr: scan(root, dataset, pr) for pr in EXTENSIONS}
        pool = set(maps[dataset]["lean4"])
        if dataset == "ntp4vc":
            pool = {ntp_key(line) for line in
                    (root / "data/ntp4vc/data/test_set.lean.txt.lst").read_text().splitlines()
                    if line.strip()}
        included = pool.intersection(*(set(m) for m in maps[dataset].values()))
        if len(included) != count:
            raise ValueError(f"{dataset}: expected {count} aligned items, found {len(included)}")
        pools[dataset] = {"pool": sorted(pool), "included": sorted(included)}
    return maps, pools


def membership(root: Path, maps: dict, pools: dict) -> list[dict]:
    frozen = json.loads((root / "eval/subsets/full_stmts_390.json").read_text())
    legacy = {}
    for row in frozen:
        key = row["title"]
        if row["source"] == "minif2f":
            key = row["split"] + "/" + key
        identity = (row["source"], canonical_key(row["source"], key))
        if identity in legacy:
            raise ValueError(f"duplicate historical identity: {identity}")
        legacy[identity] = row
    next_id = max(row["theorem_id"] for row in frozen) + 1
    rows = []
    for dataset in EXPECTED:
        for key in pools[dataset]["included"]:
            old = legacy.get((dataset, key))
            if old:
                theorem_id, title = old["theorem_id"], old["title"]
            else:
                theorem_id = next_id
                next_id += 1
                title = maps[dataset]["lean4"][key][0].stem
            artifacts = {}
            for prover in EXTENSIONS:
                candidates = maps[dataset][prover][key]
                if len(candidates) == 1:
                    path = candidates[0]
                else:
                    # The audited miniF2F aliases sometimes coexist with the
                    # canonical spelling. Select that spelling, never an
                    # arbitrary traversal-order winner.
                    base = root / "data" / dataset / "data/stmts" / prover
                    exact = [p for p in candidates if p.relative_to(base).with_suffix("").as_posix() == key]
                    if len(exact) != 1:
                        raise ValueError(f"ambiguous artifact for {dataset}/{key}/{prover}")
                    path = exact[0]
                artifacts[prover] = path.relative_to(root).as_posix()
            row = {"theorem_id": theorem_id, "source": dataset, "item_id": key,
                   "title": title, "tier": "a" if dataset == "babel-formal" else "b",
                   "artifacts": artifacts}
            if dataset == "minif2f":
                row["split"] = key.split("/", 1)[0]
            rows.append(row)
    return rows


def render_json(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def build_extended(root: Path, *, check: bool = False) -> None:
    maps, pools = inventory(root)
    members = membership(root, maps, pools)
    member_path = root / "eval/subsets/extended_stmts_2634.json"
    if member_path.exists() and json.loads(member_path.read_text()) != members:
        raise ValueError("extended membership changed; review identities before updating the frozen manifest")
    outputs = {member_path: render_json(members)}
    out = root / "eval/data/extended"
    manifest = {
        "schema_version": "itpeval-extended-statements-v1",
        "source_commit": "04326bcc04c9f182ea0cc03565ee6cc976012889",
        "provers": list(EXTENSIONS), "items": len(members),
        "records": len(members) * len(EXTENSIONS),
        "directed_pairs": len(members) * len(EXTENSIONS) * (len(EXTENSIONS) - 1),
        "membership": "eval/subsets/extended_stmts_2634.json",
        "membership_sha256": hashlib.sha256(outputs[member_path]).hexdigest(),
        "coverage_basis": "file presence; not semantic equivalence or proof completion",
        "datasets": {},
    }
    for dataset in EXPECTED:
        records = []
        for member in members:
            if member["source"] != dataset:
                continue
            for prover, artifact in member["artifacts"].items():
                raw = (root / artifact).read_bytes()
                content = raw.decode("utf-8")
                if not content.strip():
                    raise ValueError(f"empty statement: {artifact}")
                records.append({**{k: v for k, v in member.items() if k != "artifacts"},
                                "prover": prover, "content": content, "artifact": artifact,
                                "sha256": hashlib.sha256(raw).hexdigest()})
        payload = render_json(records)
        filename = dataset + ".json"
        outputs[out / filename] = payload
        manifest["datasets"][dataset] = {
            "file": filename, "items": EXPECTED[dataset], "records": len(records),
            "sha256": hashlib.sha256(payload).hexdigest(),
            "candidate_items": len(pools[dataset]["pool"]),
            "excluded_items": sorted(set(pools[dataset]["pool"]) - set(pools[dataset]["included"])),
        }
    outputs[out / "manifest.json"] = render_json(manifest)
    if check:
        stale = [str(p.relative_to(root)) for p, content in outputs.items()
                 if not p.is_file() or p.read_bytes() != content]
        if stale:
            raise ValueError("missing or stale exports: " + ", ".join(stale))
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
    print(f"{'Checked' if check else 'Built'} {manifest['items']} items / "
          f"{manifest['records']} records / {manifest['directed_pairs']} directed pairs")
