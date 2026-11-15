#!/usr/bin/env python3
"""Recount the inventory described in new_data_description.md, without prover runs.

Run from any directory. Writes JSON to stdout; uses only the Python standard
library and local corpus files. Counts describe item identities and file presence,
not semantic equivalence or completed proofs.
"""

import json
import os
import re
import statistics
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parents[1]
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
# Seven problem identities with differing upstream filenames. These mappings
# resolve catalogue identity only; they do not certify statement equivalence.
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


def read_json(relative):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def scan(dataset, prover, extension):
    base = ROOT / "data" / dataset / "data/stmts" / prover
    result = defaultdict(list)
    for directory, _, files in os.walk(base, followlinks=True):
        for filename in sorted(files):
            path = Path(directory) / filename
            if path.suffix != extension:
                continue
            key = path.relative_to(base).with_suffix("").as_posix()
            if dataset in {"hundred-theorems", "thousand-theorems"}:
                pattern = r"(\d{3})_.+" if dataset == "hundred-theorems" else r"(Q\d+[A-Z]*)_.+"
                match = re.fullmatch(pattern, key)
                if match is None:
                    continue
                key = str(int(match[1])) if dataset == "hundred-theorems" else match[1]
            elif dataset == "minif2f":
                key = MINIF2F_ALIASES.get(key, key)
            elif dataset == "ntp4vc":
                key = re.sub(r"/X_", "/_", key)
            result[key].append(path)
    return result


def ntp_key(line):
    path = PurePosixPath(line.strip())
    assert path.parts[:2] == ("data", "why3")
    assert path.parts[-2] == "lean" and path.parts[-3].endswith("_vcg")
    return PurePosixPath(path.parts[2], *path.parts[3:-3], path.stem).as_posix()


def mini_type(key):
    name = key.split("/")[1]
    prefixes = {
        "mathd_algebra_": "MATH algebra", "mathd_numbertheory_": "MATH number theory",
        "aime": "AIME", "amc": "AMC", "imo": "IMO / shortlist",
        "algebra_": "Custom algebra", "numbertheory_": "Custom number theory",
        "induction_": "Custom induction",
    }
    return next(label for prefix, label in prefixes.items() if name.startswith(prefix))


def main():
    report = {}
    included_sets = {}
    indices = {ds: read_json(f"data/{ds}/data/index.json") for ds in EXPECTED}
    for dataset, expected in EXPECTED.items():
        maps = {pr: scan(dataset, pr, ext) for pr, ext in EXTENSIONS.items()}
        pool = set(maps["lean4"])
        if dataset == "ntp4vc":
            selection = ROOT / "data/ntp4vc/data/test_set.lean.txt.lst"
            pool = {ntp_key(line) for line in selection.read_text().splitlines() if line.strip()}
            assert len(pool) == 600
        included = pool.intersection(*(set(m) for m in maps.values()))
        assert len(included) == expected, (dataset, len(included), expected)
        included_sets[dataset] = included
        lengths = [len(maps["lean4"][key][0].read_text(encoding="utf-8").splitlines())
                   for key in included]
        row = {
            "pool": len(pool), "included": len(included), "records": 10 * len(included),
            "excluded": sorted(pool - included), "ids": sorted(included),
            "missing_by_prover": {pr: sorted(pool - set(m)) for pr, m in maps.items() if pool - set(m)},
            "lean_file_lines": {"min": min(lengths), "median": statistics.median(lengths), "max": max(lengths)},
        }
        if dataset == "minif2f":
            row["by_source_and_split"] = {
                kind: {scope: dict(Counter(k.split("/")[0] for k in keys if mini_type(k) == kind))
                       for scope, keys in [("pool", pool), ("included", included)]}
                for kind in sorted({mini_type(k) for k in pool})
            }
        elif dataset == "ntp4vc":
            row["by_source_project"] = {
                scope: dict(sorted(Counter("/".join(k.split("/")[:2]) if k.startswith("frama_c/")
                                           else "pearl" for k in keys).items()))
                for scope, keys in [("pool", pool), ("included", included)]
            }
        elif dataset == "putnambench":
            metadata = {x["problem_name"]: x for x in read_json("data/putnambench/data/upstream_problem_metadata.json")}
            row["unlabelled_ids"] = sorted(included - metadata.keys())
            row["tags"] = dict(sorted(Counter(t for k in included if k in metadata
                                              for t in metadata[k]["tags"]).items()))
            row["tag_cardinality"] = dict(sorted(Counter(len(metadata[k]["tags"])
                                                         for k in included if k in metadata).items()))
            row["positions"] = dict(sorted(Counter(k[-2:] for k in included).items()))
            row["decades"] = dict(sorted(Counter(str(int(k[7:11]) // 10 * 10) for k in included).items()))
        elif dataset == "babel-formal":
            row["indexed_lemma_counts"] = {k: indices[dataset]["topics"][k]["n_items"] for k in sorted(included)}
        elif dataset == "logipedia":
            modules = defaultdict(Counter)
            for entry in indices[dataset]["entries"].values():
                modules[entry["module"]][entry["kind"]] += 1
            row["indexed_module_kinds"] = dict(modules)
        elif dataset == "thousand-theorems":
            theorems = indices[dataset]["theorems"]
            row["msc"] = dict(sorted(Counter(theorems[k]["msc_classification"] for k in included).items()))
            row["catalogue_entries"] = len(theorems)
        elif dataset == "verina":
            tasks = indices[dataset]["tasks"]
            row["categories"] = dict(Counter(t["category"] for t in tasks))
            row["origins"] = dict(Counter(t["upstream"]["name"] for t in tasks))
            row["normalizations"] = {t["id"]: t["statement_compatibility_normalizations"]
                                     for t in tasks if t["statement_compatibility_normalizations"]}
        report[dataset] = row

    proofs = read_json("eval/data/proofs.json")
    assert {row["theorem_id"] for row in proofs} == set(range(1, 75))
    proof_items = defaultdict(set)
    for row in proofs:
        key = row["title"] if row["source"] == "babel-formal" else str(int(row["title"].split("_")[0]))
        proof_items[(row["source"], key)].add(row["prover"])
    assert len(proofs) == 296 and len(proof_items) == 74
    assert all(provers == {"lean4", "rocq", "isabelle", "hol-light"} for provers in proof_items.values())
    overlap = sum(key in included_sets[ds] for ds, key in proof_items)
    assert overlap == 73
    report["proofs"] = {
        "items": len(proof_items), "records": len(proofs), "statement_overlap": overlap,
        "by_dataset": dict(Counter(ds for ds, _ in proof_items)),
        "hundred_ids": sorted(int(key) for ds, key in proof_items if ds == "hundred-theorems"),
    }
    report["totals"] = {
        "statement_items": sum(len(s) for s in included_sets.values()),
        "statement_records": 10 * sum(len(s) for s in included_sets.values()),
        "union_items": sum(len(s) for s in included_sets.values()) + len(proof_items) - overlap,
        "modality_records": 10 * sum(len(s) for s in included_sets.values()) + len(proofs),
    }
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
