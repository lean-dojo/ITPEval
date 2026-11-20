"""Import a released ITPEval checkout as an independently reconstructible corpus."""

import argparse
import json
import subprocess
import tempfile
from collections import defaultdict
from pathlib import Path

from itpeval.alignment import Correspondence, SourceRef
from itpeval.corpus import datasets
from itpeval.corpus.datasets import partition_items
from itpeval.corpus.storage import (
    digest,
    encode,
    jsonl,
    object_id,
    project_file,
    store_blob,
)

from . import indexed_targets, locators


def _revision(checkout, *args):
    try:
        result = subprocess.run(["git", "-C", str(checkout), *(args or ("rev-parse", "HEAD"))],
                                capture_output=True, text=True, check=False)
    except FileNotFoundError:
        return None
    return result.stdout.strip() or None if result.returncode == 0 else None


def import_release(checkout, destination, *, duplicate_groups=(), build_revision=None):
    """Validate the frozen membership and source bytes before publishing the new directory."""
    root = Path(checkout).resolve()
    out = Path(destination).absolute()
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        raise FileExistsError(out)
    with tempfile.TemporaryDirectory(dir=out.parent) as tmp:
        stage = Path(tmp) / "release"
        stage.mkdir()
        metadata = {}

        def keep(name, expected=None):
            raw = project_file(root, name).read_bytes()
            key = store_blob(stage / "blobs", raw)
            if expected is not None and expected != key:
                raise ValueError(f"checksum mismatch for {name}")
            metadata[name] = key
            return raw

        def archived(name):
            key = metadata[name]
            return (stage / "blobs" / key[:2] / key[2:]).read_bytes()

        manifest_name = "eval/data/extended/manifest.json"
        manifest = json.loads(keep(manifest_name))
        if manifest["schema_version"] != "itpeval-extended-statements-v1":
            raise ValueError("unsupported released corpus schema")
        members = json.loads(keep(manifest["membership"], manifest["membership_sha256"]))
        by_id = {row["theorem_id"]: row for row in members}
        if len(by_id) != len(members) or len(members) != manifest["items"]:
            raise ValueError("inconsistent release membership count")
        keep("LICENSE")
        for pattern in ("data/third_party_licenses/*", "corpus-extension/*resolutions.json",
                        "data/*/data/index.json", "eval/subsets/*.json",
                        "eval/data/*.json", "eval/data/*.jsonl", "data/ntp4vc/data/test_set.lean.txt.lst"):
            for path in sorted(root.glob(pattern)):
                keep(path.relative_to(root).as_posix())

        # One Why3 program may generate multiple modules and many obligations.
        # Match the longest released source stem (e.g. bitcount vs bitcount_aux).
        why3 = root / "data/ntp4vc/data/why3_sources"
        program_paths = {p.relative_to(why3).with_suffix("").as_posix(): p for p in why3.rglob("*.mlw")}
        stems = sorted(program_paths, key=lambda v: (-len(v), v))
        source_map, families = {}, defaultdict(list)
        for row in members:
            if row["source"] == "ntp4vc":
                stem = next((s for s in stems if row["item_id"].startswith(s + "_")), None)
                if stem is None:
                    raise ValueError(f"no released Why3 program for {row['item_id']}")
                program = program_paths[stem].relative_to(root).as_posix()
                if program not in metadata:
                    keep(program)
                source_map[row["theorem_id"]] = program
                families[program].append(row["theorem_id"])
        partitions = partition_items(members, groups=[*families.values(), *duplicate_groups])
        jsonl(stage / "membership.jsonl",
              ({**row, **partitions[row["theorem_id"]], "program_source": source_map.get(row["theorem_id"])}
               for row in members))

        indexes = {dataset: json.loads(archived(f"data/{dataset}/data/index.json"))
                   for dataset in manifest["datasets"]}
        indexes["verina"]["by_id"] = {r["id"]: r for r in indexes["verina"]["tasks"]}
        mapped_bases = {"individually_reviewed_span", "released_identifier", "membership_identifier"}
        counts, statuses = defaultdict(int), defaultdict(int)
        coverage = defaultdict(lambda: defaultdict(int))
        observed = set()
        with (stage / "artifacts.jsonl").open("wb") as stream:
            for dataset, shard in manifest["datasets"].items():
                name = "eval/data/extended/" + shard["file"]
                rows = json.loads(keep(name, shard["sha256"]))
                if len(rows) != shard["records"]:
                    raise ValueError(f"incorrect shard count in {name}")
                for row in rows:
                    theorem_id, prover = row["theorem_id"], row["prover"]
                    key = theorem_id, prover
                    member = by_id[theorem_id]
                    if (key in observed or dataset != member["source"] or row["source"] != dataset
                            or row["item_id"] != member["item_id"]
                            or row["artifact"] != member["artifacts"][prover]):
                        raise ValueError(f"inconsistent membership for {key}")
                    observed.add(key)
                    raw = project_file(root, row["artifact"]).read_bytes()
                    if digest(raw) != row["sha256"] or raw != row["content"].encode("utf-8"):
                        raise ValueError(f"source differs from release: {row['artifact']}")
                    blob = store_blob(stage / "blobs", raw)
                    record = {k: v for k, v in row.items() if k != "content"}
                    targets = locators.locate(raw, blob)
                    if targets:
                        for target in targets:
                            target["basis"] = "individually_reviewed_span"
                    else:
                        targets = indexed_targets.locate(raw, blob, member, prover, indexes,
                                                         manifest["membership"], metadata)
                    candidates = []
                    mapped = []
                    for target in targets:
                        counts[target["basis"]] += 1
                        target["source_locator_id"] = object_id(
                            "released_source_occurrence", manifest["membership_sha256"], row["artifact"], blob,
                            target["start_byte"], target["end_byte"], target["actual_kind"])
                        if target["basis"] in mapped_bases:
                            mapped.append(target)
                        else:
                            target["benchmark_role"] = "candidate_target_specification"
                            candidates.append(target)
                    if mapped:
                        status = mapped[0]["basis"]
                    elif candidates:
                        status = "candidate_only"
                    elif prover == "metamath" and indexed_targets.comment_only_metamath(raw):
                        status = "comment_only_no_declaration"
                    else:
                        status = "unresolved"
                    statuses[status] += 1
                    coverage[dataset][prover] += bool(mapped)
                    stream.write(encode({**record, **partitions[theorem_id], "source_blob": blob,
                                         "target_locators": mapped, "candidate_target_locators": candidates,
                                         "target_locator_status": status,
                                         "checking_status": "statement_only"}) + b"\n")
        expected = {(m["theorem_id"], p) for m in members for p in m["artifacts"]}
        if observed != expected or len(observed) != manifest["records"]:
            raise ValueError("incomplete release artifacts")

        jsonl(stage / "alignments.jsonl",
              ({"theorem_id": m["theorem_id"], "relation": "dataset_correspondence",
                "direction": "symmetric", "artifacts": m["artifacts"], "assumptions": None,
                "source": manifest["membership"], "evidence": manifest["membership_sha256"]}
               for m in members))
        by_artifact = {path: m["theorem_id"] for m in members for path in m["artifacts"].values()}
        source_refs = {}

        def source_ref(path):
            if path not in source_refs:
                try:
                    key = store_blob(stage / "blobs", project_file(root, path).read_bytes())
                except (FileNotFoundError, ValueError):
                    # Reviews can cite old absolute installation paths or files
                    # absent from the public release. Retain the original locator.
                    key = None
                source_refs[path] = SourceRef(path, key)
            return source_refs[path]

        semantic = "corpus-extension/semantic_canonical_resolutions.json"
        reviews = json.loads(archived(semantic))["resolutions"]

        def reviewed_edges():
            for review_key, decision in sorted(reviews.items()):
                target = source_ref(decision["candidate_path"])
                sources = tuple(source_ref(p) for p in decision["source_authority"] if p != target.path)
                yield Correspondence("reviewed_formalization", "source_to_target", sources,
                                     target, by_artifact.get(target.path), None, semantic, review_key,
                                     metadata[semantic], decision["decision"], decision["native_check"],
                                     target.content_sha256 == decision["candidate_sha256"]).to_dict()

        jsonl(stage / "reviewed_correspondences.jsonl", reviewed_edges())
        canonical = "corpus-extension/putnambench_canonical_resolutions.json"
        putnam = json.loads(archived(canonical))
        putnam_ids = {m["item_id"]: m["theorem_id"] for m in members if m["source"] == "putnambench"}
        jsonl(stage / "canonical_statements.jsonl",
              ({"item_id": key, "theorem_id": putnam_ids.get(key), "source": canonical,
                "source_commit": putnam["official_commit"], "evidence_sha256": metadata[canonical],
                "review": value} for key, value in sorted(putnam["resolutions"].items())))
        mapped_count = sum(counts[basis] for basis in mapped_bases)
        importer_sources = (Path(__file__), Path(datasets.__file__), Path(locators.__file__),
                            Path(indexed_targets.__file__))
        source_hash = object_id([(p.name, digest(p.read_bytes())) for p in importer_sources])
        importer_dir = Path(__file__).resolve().parent
        report = {"schema_version": 1, "corpus_revision": _revision(root),
                  "programs": len(families), "reviewed_correspondences": len(reviews), "declared_target_locators": mapped_count,
                  "candidate_target_locators": sum(counts.values()) - mapped_count,
                  "artifact_locator_status_counts": statuses,
                  "locator_basis_counts": counts, "artifacts_with_target_locators": coverage,
                  "missing_review_source_paths": sorted(k for k, v in source_refs.items() if v.content_sha256 is None),
                  "release_source_commit": manifest["source_commit"],
                  "importer_revision": build_revision or source_hash,
                  "importer_source_sha256": source_hash,
                  "importer_git_revision": _revision(importer_dir, "log", "-1", "--format=%H", "--", ".", "../datasets.py"),
                  "items": len(members), "artifacts": len(observed), "metadata_blobs": metadata}
        (stage / "manifest.json").write_bytes(encode(report))
        stage.rename(out)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    result = import_release(args.checkout, args.destination)
    print(f"Imported {result['items']} benchmark items and {result['artifacts']} artifacts.")
