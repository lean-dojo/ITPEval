"""Run native extraction, deterministic replay and learning export for release qualification."""

import argparse
import hashlib
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.registry import prover_ids
from itpeval.corpus.example import ENTRY, LIBRARY, export
from itpeval.corpus.storage import read_jsonl
from itpeval.environments import prepare_project
from itpeval.extraction import extract_project
from itpeval.learning.qualification import _record
from itpeval.retrieval import CorpusIndex


def _evidence(bundle, decl):
    key = decl["evidence"][0]
    return json.loads((bundle / "blobs" / key[:2] / key[2:]).read_bytes())


def _structure(bundle, report, name):
    key = report["structures"][name]
    return json.loads((bundle / "blobs" / key[:2] / key[2:]).read_bytes())


def check_fixture(prover, bundle):
    """Known answers grounded in each fixture's source and native proof model."""
    decls = {row["name"]: row for row in read_jsonl(bundle / "declarations.jsonl")}
    report = json.loads((bundle / "report.json").read_bytes())
    contexts = {r["context_id"]: r for r in read_jsonl(bundle / "contexts.jsonl")}
    edges = list(read_jsonl(bundle / "dependencies.jsonl"))
    if len(decls) < 2:
        raise ValueError("fixture did not produce multiple declarations")
    for d in decls.values():
        if d["declaration_id"] in contexts[d["context_id"]]["visible"]:
            raise ValueError("a target was visible in its own premise context")

    if prover == "lean4":
        theorem = decls["first_successor"]
        proof = _structure(bundle, report, theorem["declaration_id"])
        key = theorem["source_hash"]
        src = (bundle / "blobs" / key[:2] / key[2:]).read_bytes()
        checks = {"parser proof region": src[proof["start_byte"]:proof["end_byte"]].strip() == b"Counts.next_index_zero",
                  "Mathlib declaration": "findImports" in decls,
                  "kernel type": "Counts.nextIndex 0 = 1" == theorem["statement"],
                  "explicit proof reference": any(e["origin"] == theorem["declaration_id"] and
                      e["target_id"] == decls["Counts.next_index_zero"]["declaration_id"] and
                      e["relation"] == "proof_used_premise" for e in edges)}
    elif prover == "rocq":
        theorem = decls["ITPProject.Library.M.identity_eq"]
        goals = _structure(bundle, report, "Library.v#goals")
        checks = {"Stdlib declaration": "ITPProject.StrictProp.Spr1_inj" in decls,
                  "native focus and shelf": all(any(t["goals"] and "<goal>" in t["goals"][category] for t in goals)
                                                for category in ("focused", "background", "shelved")),
                  "discharged section": "forall (A : Type) (x : A)" in theorem["statement"],
                  "source section context": "M.Local.A" in contexts[theorem["context_id"]]["hypotheses"],
                  "Stdlib import": any(e["target_name"] == "Stdlib.Init.Nat" for e in edges)}
    elif prover == "metamath":
        dv = decls["pair-rule"]
        proof_key = json.loads((bundle / "report.json").read_bytes())["structures"][dv["declaration_id"]]
        trace = json.loads((bundle / "blobs" / proof_key[:2] / proof_key[2:]).read_bytes())["transitions"]
        checks = {"verified proof stack": trace[-1]["top"] == dv["statement"].split() and trace[-1]["height_after"] == 1,
                  "set.mm theorem": decls["a1i"]["checking_status"] == "proof_verified",
                  "fixed disjoint pair": ["x", "y"] in contexts[dv["context_id"]]["disjoint"],
                  "compressed reference": any(e["origin"] == dv["declaration_id"] and
                      e["target_id"] == decls["pair-dv"]["declaration_id"] and
                      e["relation"] == "proof_used_premise" for e in edges)}
    elif prover == "agda":
        field = decls["Level.Lift.lower"]
        early = contexts[decls["Client.prior"]["context_id"]]
        checks = {"later import hidden": "Level" not in early["imports"] and field["declaration_id"] not in early["visible"],
                  "record projection": field["kind"] == "Field" and "Lift ℓ A → A" in field["statement"],
                  "constructor parameters": "{a ℓ : Level}" in decls["Level.lift"]["statement"],
                  "no open goals": not any(_evidence(bundle, field)["goals"].values()),
                  "native constraints": _structure(bundle, report, "Level.agda#interaction")["constraints"] == []}
    elif prover == "acl2":
        cls = [_evidence(bundle, decls[k])["symbol_class"] for k in ("MY-ID", "GUARDED-ID")]
        detail = _evidence(bundle, decls["MY-ID-ID"])
        h = detail["enabled_theory_blob"]
        theory = (bundle / "blobs" / h[:2] / h[2:]).read_text()
        checks = {"certified book declaration": decls["LEN-OF-APPEND"]["source_path"] == "books/std/lists/append.lisp",
                  "enabled and used runes": "(:DEFINITION GUARDED-ID)" in theory and
                  detail["used_runes"] == "((:DEFINITION MY-ID))",
                  "guard verification differs from admission": cls == [":IDEAL", ":COMMON-LISP-COMPLIANT"],
                  "theorem in world": decls["MY-ID-ID"]["statement"] == "(EQUAL (MY-ID X) X)",
                  "certified book": any(e["target_name"] == "std/lists/append" for e in edges)}
    elif prover == "mizar":
        checks = {"MML registration": decls["REAL_1.CCluster1"]["kind"] == "CCluster",
                  "MML constructor": decls["REAL_1.K6"]["kind"] == "constructor_redefinition",
                  "resolved reference name": any(e["target_name"] == "XREAL_0:def 1" for e in edges),
                  "accommodated MML": "TARSKI" in contexts[decls["SAMPLE.Th1"]["context_id"]]["imports"],
                  "verified formula tree": "<For " in decls["SAMPLE.Th1"]["statement"],
                  "justification reference": any(e["origin"] == decls["SAMPLE.Th2"]["declaration_id"] and
                      e["target_id"] == decls["SAMPLE.Th1"]["declaration_id"] for e in edges)}
    elif prover == "pvs":
        lower = {k.lower(): d for k, d in decls.items()}
        params = _structure(bundle, report, lower["prelude_aux.rest_emptyset"]["declaration_id"])
        arguments = _structure(bundle, report, lower["sample.twice"]["declaration_id"])
        checks = {"theory and declaration parameters": params["theory_parameters"] == ["T: TYPE"] and
                  arguments["declaration_parameters"] == ["x: int"],
                  "formal is local to declaring theory": lower["prelude_aux.t"]["declaration_id"] not in
                  contexts[lower["sample.step"]["context_id"]]["visible"],
                  "transitive exports respect EXPORTING": lower["base.bump"]["declaration_id"] in
                  contexts[lower["sample.step"]["context_id"]]["visible"] and
                  lower["base.internal_offset"]["declaration_id"] not in contexts[lower["sample.step"]["context_id"]]["visible"],
                  "native declaration reference": any(e["origin"] == lower["sample.step"]["declaration_id"] and
                      e["target_id"] == lower["base.bump"]["declaration_id"] and
                      e["relation"] == "declaration_reference" for e in edges),
                  "imported definition": "base.bump" in lower, "lemma is typechecked":
                  lower["sample.step"]["checking_status"] == "typechecked",
                  "required TCC": any(e["relation"] == "generated_obligation" and
                      e["origin"] == lower["sample.twice"]["declaration_id"] and
                      e["target_id"] == lower["sample.twice_tcc1"]["declaration_id"] for e in edges)}
    elif prover == "isabelle":
        theorem = next(v for k, v in decls.items() if k.endswith("bounded.twice_positive"))
        tree = _structure(bundle, report, theorem["declaration_id"])
        checks = {"native typed term": tree["format"] == "isabelle.term_xml.v1" and
                  "Base.twice" in tree["proposition"] and "HOL.Trueprop" in tree["proposition"],
                  "resolved statement reference": any(e["origin"] == theorem["declaration_id"] and
                      e["target_id"] == decls["Base.twice"]["declaration_id"] and
                      e["relation"] == "statement_reference" for e in edges),
                  "locale assumption retained": "bounded" in theorem["statement"] or
                  bool(contexts[theorem["context_id"]]["hypotheses"]),
                  "theory definition": any(k.endswith("twice_def") for k in decls)}
    else:
        opened = next(v for k, v in decls.items() if k.endswith("under_assumption"))
        closed_name = "twice_zero" if prover == "hol4" else "discharge_assumption"
        closed = next(v for k, v in decls.items() if k.endswith(closed_name))
        checks = {"open theorem assumptions": bool(contexts[opened["context_id"]]["hypotheses"]),
                  "closed theorem": not contexts[closed["context_id"]]["hypotheses"]}

    if prover == "hol-light":
        early = contexts[decls["before_arithmetic"]["context_id"]]
        registered = decls["itpeval_neg_def"]
        checks.update({"definition registration": registered["kind"] == "definition" and
                       any(e["origin"] == registered["declaration_id"] and e["target_name"] == "itpeval_neg" and
                           e["relation"] == "defines_constant" for e in edges),
                       "imports ordered at load": decls["base_refl"]["declaration_id"] in early["visible"] and
                       decls["ARITHMETIC_PROGRESSION"]["declaration_id"] not in early["visible"] and
                       "arithmetic.ml" in contexts[registered["context_id"]]["imports"]})
    if prover == "hol4":
        tree = _structure(bundle, report, opened["declaration_id"])
        checks["typed native term trees"] = tree["format"] == "hol4.kernel-term.v1" and all(
            node["type"] for component in tree["terms"].values() for node in component) and bool(tree["terms"])
    available = next((d for d in decls.values() if contexts[d["context_id"]]["visible"]), None)
    if available:
        hits = CorpusIndex(bundle / "index.sqlite").search(
            "", environment_id=available["environment_id"], context_id=available["context_id"], limit=len(decls))
        actual = {r["declaration_id"] for r in hits}
        checks["retrieval respects context"] = actual == set(contexts[available["context_id"]]["visible"])
    if not all(checks.values()):
        raise ValueError(f"known answer mismatch in {prover}: {checks}")
    return checks


def qualify(prover, prefix, cache, directory, matrix):
    directory = directory / prover
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "extraction.json"
    build = env_id = None
    try:
        prepared = prepare_project(prover, LIBRARY / prover / "library", prefix=prefix, cache=cache)
        build, env_id = prepared.spec.prover_build, prepared.environment_id
        with TemporaryDirectory() as scratch:
            root = Path(scratch)
            fresh, dataset = export(prepared, ENTRY[prover], root / "first")
            replay = extract_project(prepared, ENTRY[prover], root / "second")
            cached = extract_project(prepared, ENTRY[prover], root / "second")
            normalized = {}
            for name in ["report.json", "declarations.jsonl", "contexts.jsonl", "dependencies.jsonl"]:
                data = (fresh.path / name).read_bytes()
                if data != (replay.path / name).read_bytes():
                    raise ValueError(f"fresh native runs differed in {name}")
                normalized[name] = hashlib.sha256(data).hexdigest()
            if fresh.cache_hit or replay.cache_hit or not cached.cache_hit:
                raise ValueError("incorrect extraction cache lifecycle")
            checks = check_fixture(prover, fresh.path)
            rows = sum(1 for _ in read_jsonl(dataset))
            if rows != fresh.report["declarations"]:
                raise ValueError("incomplete premise dataset")
            report = {**fresh.report, "known_answers": checks, "dataset_rows": rows,
                      "fresh_runs": 2, "cache_replay": True, "normalized_sha256": normalized}
        status = "implemented/tested"
    except (KeyError, OSError, RuntimeError, StopIteration, ValueError) as exc:
        status = "failed"
        report = {"prover": prover, "error": str(exc)}
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    _record(matrix, [{"prover": prover, "prover_build": build, "environment_id": env_id,
                      "operation": "inspect_declarations", "status": status,
                      "evidence_path": os.path.relpath(path, matrix.parent)}])
    print(f"{prover}: {status}", flush=True)
    if status == "failed":
        print(report["error"], flush=True)
    return status == "implemented/tested"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prover", action="append", choices=prover_ids())
    for field in ("prefix", "cache", "output", "report"):
        parser.add_argument("--" + field, type=Path, required=True)
    args = parser.parse_args()
    results = [qualify(prover, args.prefix, args.cache, args.output, args.report)
               for prover in args.prover or prover_ids()]
    raise SystemExit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
