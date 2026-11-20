"""Export released benchmark references in Hugging Face and TRL dataset shapes."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from contextlib import ExitStack
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from tempfile import TemporaryDirectory

from .storage import digest, encode, read_jsonl


VIEWS = (
    "pretraining_reference",
    "statement_translation_reference",
    "statement_translation_reviewed",
    "proof_translation_reference",
    "formalization_reference",
    "informalization_reference",
)
ACCEPTED_REVIEWS = {"accept_manual_repair", "accept_manual_review", "accept_corrected_source"}
PARTITIONS = {"train": "train", "valid": "validation", "validation": "validation", "test": "test"}


def read_blob(corpus: Path, key: str) -> bytes:
    if len(key) != 64 or any(c not in "0123456789abcdef" for c in key):
        raise ValueError(f"invalid source hash {key!r}")
    data = (corpus / "blobs" / key[:2] / key[2:]).read_bytes()
    if digest(data) != key:
        raise ValueError(f"corrupt corpus blob {key}")
    return data


@dataclass(frozen=True)
class Source:
    text: str
    path: str
    sha256: str
    prover: str


def archived_source(row, path, prover, field):
    raw = row[field]
    return Source(raw, path, digest(raw.encode("utf-8")), prover)


def benchmark_inputs(corpus, metadata):
    def archived(path):
        return read_blob(corpus, metadata[path])

    # The release selected nTP4VC from the upstream test list. The importer's
    # generic partitions group VCs but do not encode that upstream constraint.
    ntp4vc_test = set()
    if "data/ntp4vc/data/test_set.lean.txt.lst" in metadata:
        for line in archived("data/ntp4vc/data/test_set.lean.txt.lst").decode("utf-8").splitlines():
            if line.strip():
                path = PurePosixPath(line.strip())
                ntp4vc_test.add(PurePosixPath(*path.parts[2:-3], path.stem).as_posix())
    members = {}
    partitions = {}
    for member in read_jsonl(corpus / "membership.jsonl"):
        split = PARTITIONS[member["partition"]]
        upstream = member.get("upstream_split")
        if upstream is not None and PARTITIONS[upstream] != split:
            raise ValueError("benchmark record crosses its upstream split")
        key = member["source"], member["theorem_id"]
        group = member["group_id"]
        if key in members or partitions.setdefault(group, split) != split:
            raise ValueError("duplicate item or conflicting benchmark group splits")
        if member["source"] == "ntp4vc":
            if member["item_id"] not in ntp4vc_test:
                raise ValueError(f"nTP4VC item missing from pinned test list: {member['item_id']}")
            member["protected_split"] = "test"
        members[key] = member

    statements = defaultdict(dict)
    for row in read_jsonl(corpus / "artifacts.jsonl"):
        key = row["source"], row["theorem_id"]
        member = members[key]
        prover, path, sha = row["prover"], row["artifact"], row["source_blob"]
        if (prover in statements[key] or member["artifacts"][prover] != path
                or sha != row["sha256"] or row["partition"] != member["partition"]):
            raise ValueError(f"inconsistent corpus artifact {path}")
        source = Source(read_blob(corpus, sha).decode("utf-8"), path, sha, prover)
        statements[key][prover] = source, row["target_locator_status"]
    for key, member in members.items():
        if statements[key].keys() != member["artifacts"].keys():
            raise ValueError(f"incomplete corpus item {key}")

    proof_path = "eval/data/proofs.json"
    proofs = defaultdict(dict)
    for row in json.loads(archived(proof_path)):
        key = row["source"], row["theorem_id"]
        prover = row["prover"]
        if prover in proofs[key] or not row["content"].strip():
            raise ValueError(f"duplicate or empty proof reference {key} {prover}")
        proofs[key][prover] = archived_source(row, proof_path, prover, "content")

    minif2f = {r["item_id"]: key for key, r in members.items() if key[0] == "minif2f"}
    nl_path = "eval/data/minif2f_nl4itp.jsonl"
    language = {}
    for line in archived(nl_path).splitlines():
        row = json.loads(line)
        key = minif2f.get(f"{row['split']}/{row['name']}")
        if key is None or not row.get("nl", "").strip():
            continue
        if key in language:
            raise ValueError(f"duplicate NL4ITP reference {key}")
        english = archived_source(row, nl_path, "english", "nl")
        formal = [archived_source(row, nl_path, prover, field)
                  for prover, field in (("lean4", "lean4"), ("rocq", "rocq"),
                                        ("isabelle", "isabelle"), ("hol-light", "hol_light"))
                  if row.get(field) and row[field].strip()]
        language[key] = english, formal
    return members, statements, proofs, language


def review_index(corpus, metadata):
    """Index eligible reviews by exact source and target content and keep known rejections."""
    reviews, blocked = {}, set()
    evidence = {}
    for row in read_jsonl(corpus / "reviewed_correspondences.jsonl"):
        target = row["target"]
        target_key = target["path"], target["content_sha256"]
        source_path, source_hash = row["evidence_source"], row["evidence_sha256"]
        if metadata.get(source_path) != source_hash:
            raise ValueError(f"review evidence is absent from the import: {source_path}")
        if source_path not in evidence:
            evidence[source_path] = json.loads(read_blob(corpus, source_hash))["resolutions"]
        original = evidence[source_path][row["evidence_key"]]
        if (original["decision"] != row["decision"] or original["native_check"] != row["native_check"]
                or original["candidate_path"] != target["path"]
                or (original["candidate_sha256"] == target["content_sha256"]) != row["source_matches_review"]):
            raise ValueError(f"review differs from archived evidence: {row['evidence_key']}")
        if row["decision"].startswith("blocked_") and row["source_matches_review"]:
            blocked.add(target_key)
        if (row["decision"] not in ACCEPTED_REVIEWS or not row["source_matches_review"]
                or row["native_check"] != "passed"):
            continue
        for authority in row["sources"]:
            if authority["path"] not in original["source_authority"]:
                raise ValueError(f"review source differs from archived evidence: {row['evidence_key']}")
            if authority["content_sha256"]:
                key = authority["path"], authority["content_sha256"], *target_key
                reviews[key] = row
    return reviews, blocked


def record(key, member, source, target=None, review=None):
    return {
        "source": key[0], "theorem_id": key[1], "group_id": member.get("group_id"),
        "item_id": member.get("item_id"), "release_partition": member.get("partition"),
        "upstream_split": member.get("protected_split") or member.get("upstream_split"),
        "reference_only": True, "source_prover": source.prover,
        "source_path": source.path, "source_sha256": source.sha256,
        "target_prover": target.prover if target else None,
        "target_path": target.path if target else None,
        "target_sha256": target.sha256 if target else None,
        "review_key": review["evidence_key"] if review else None,
        "review_evidence_path": review["evidence_source"] if review else None,
        "review_evidence_sha256": review["evidence_sha256"] if review else None,
        "target_native_check": review["native_check"] if review else None,
    }


def source_split(members, key):
    member = members.get(key)
    if member is None:
        return "unassigned"
    return member.get("protected_split") or PARTITIONS[member["partition"]]


def duplicate_hashes(members, statements, proofs, language):
    partitions = defaultdict(set)
    for source_rows in (statements, proofs, language):
        for key, group in source_rows.items():
            if source_rows is statements:
                entries = [source for source, _ in group.values()]
            elif source_rows is proofs:
                entries = group.values()
            else:
                english, formal = group
                entries = [english, *formal]
            for source in entries:
                partitions[source.sha256].add(source_split(members, key))
    return {sha for sha, splits in partitions.items() if len(splits) > 1}


def training_rows(view, members, statements, proofs, language, reviews, blocked, duplicates, *, style):
    def pair(key, source, target, task, review=None):
        prompt = f"{task} from {source.prover} to {target.prover}.\n\n{source.text}"
        result = record(key, members.get(key, {}), source, target, review)
        result["prompt"] = prompt
        result["completion"] = target.text
        if style == "chat":
            result["prompt"] = [{"role": "user", "content": prompt}]
            result["completion"] = [{"role": "assistant", "content": target.text}]
        return source_split(members, key), result

    if view == "pretraining_reference":
        seen = set()
        for source_rows in (statements, proofs):
            for key, group in source_rows.items():
                sources = [source for source, _ in group.values()] if source_rows is statements else group.values()
                for source in sources:
                    if source.sha256 in duplicates or source.sha256 in seen:
                        continue
                    seen.add(source.sha256)
                    yield source_split(members, key), {**record(key, members.get(key, {}), source), "text": source.text}
    elif view == "proof_translation_reference":
        for key, group in proofs.items():
            sources = [s for s in group.values() if s.sha256 not in duplicates]
            for source in sources:
                for target in sources:
                    if source.prover != target.prover:
                        yield pair(key, source, target, "Translate the proof file")
    elif view in {"formalization_reference", "informalization_reference"}:
        for key, (english, formal) in language.items():
            if english.sha256 not in duplicates:
                for source in formal:
                    if source.sha256 not in duplicates:
                        if view == "formalization_reference":
                            yield pair(key, english, source, "Formalize the statement")
                        else:
                            yield pair(key, source, english, "State the theorem in English")
    else:
        for key, group in statements.items():
            sources = [s for s, status in group.values() if s.sha256 not in duplicates
                       and status != "comment_only_no_declaration" and (s.path, s.sha256) not in blocked]
            for source in sources:
                for target in sources:
                    if source.prover == target.prover:
                        continue
                    review = reviews.get((source.path, source.sha256, target.path, target.sha256))
                    if review or view == "statement_translation_reference":
                        yield pair(key, source, target, "Translate the formal statement", review)


def arrow_schema(pa, view, style):
    text = pa.string()
    columns = [(key, text) for key in (
        "source", "item_id", "release_partition", "upstream_split", "source_prover", "source_path", "source_sha256",
        "target_prover", "target_path", "target_sha256", "review_key", "review_evidence_path",
        "review_evidence_sha256", "target_native_check",
    )]
    columns += [("theorem_id", pa.int64()), ("group_id", pa.int64()), ("reference_only", pa.bool_())]
    if view == "pretraining_reference":
        columns.append(("text", text))
    else:
        prompt = pa.list_(pa.struct([("role", text), ("content", text)])) if style == "chat" else text
        columns += [("prompt", prompt), ("completion", prompt)]
    return pa.schema(columns)


def write_view(destination, rows, *, view, format, style):
    destination.mkdir()
    counts = Counter()
    if format == "parquet":
        import pyarrow as pa
        import pyarrow.parquet as pq

        schema = arrow_schema(pa, view, style)
    writers, batches = {}, defaultdict(list)
    with ExitStack() as stack:
        for split, row in rows:
            if split not in writers:
                out = destination / f"{split}.{format}"
                if format == "parquet":
                    writers[split] = stack.enter_context(pq.ParquetWriter(out, schema, compression="zstd"))
                else:
                    writers[split] = stack.enter_context(out.open("wb"))
            counts[split] += 1
            writer = writers[split]
            if format == "jsonl":
                writer.write(encode(row) + b"\n")
            else:
                batch = batches[split]
                batch.append(row)
                if len(batch) >= 1024:
                    writer.write_table(pa.Table.from_pylist(batch, schema=schema))
                    batch.clear()
        for split, batch in batches.items():
            if batch:
                writers[split].write_table(pa.Table.from_pylist(batch, schema=schema))
    return dict(counts)


def export_benchmark(corpus, output, *, include_benchmark_references=False, views=VIEWS,
                     format="jsonl", style="standard"):
    """Convert a frozen benchmark import to trainer-shaped reference files."""
    if not include_benchmark_references:
        raise ValueError("benchmark references include evaluation data; pass --include-benchmark-references to export")
    if not views or set(views) - set(VIEWS) or len(set(views)) != len(views):
        raise ValueError("choose one or more distinct benchmark views")
    if format not in {"jsonl", "parquet"} or style not in {"standard", "chat"}:
        raise ValueError("unsupported output format or style")
    if format == "parquet":
        try:
            import pyarrow.parquet  # noqa: F401
        except ImportError as error:
            raise ValueError("Parquet export requires the itpeval[parquet] extra") from error
    corpus, output = Path(corpus).resolve(), Path(output).absolute()
    if output.exists():
        raise FileExistsError(output)
    raw_manifest = (corpus / "manifest.json").read_bytes()
    manifest = json.loads(raw_manifest)
    metadata = manifest["metadata_blobs"]
    members, statements, proofs, language = benchmark_inputs(corpus, metadata)
    if len(members) != manifest["items"] or sum(map(len, statements.values())) != manifest["artifacts"]:
        raise ValueError("input corpus counts do not match its manifest")
    reviews, blocked = review_index(corpus, metadata)
    duplicates = duplicate_hashes(members, statements, proofs, language)
    report = {
        "schema_version": 1, "reference_only": True, "format": format, "style": style,
        "input_manifest_sha256": digest(raw_manifest), "release_source_commit": manifest["release_source_commit"],
        "excluded_hashes_in_multiple_partitions": len(duplicates),
        "license_notices": "notices/",
        "partition_policy": (
            "Preserves item and program-family grouping. nTP4VC remains in its pinned upstream test split. "
            "Other partitions follow the imported assignment and preserve known upstream splits. "
            "Identical content in multiple partitions is excluded. "
            "Unassigned historical proofs lack a split. Train is an imported split name. "
            "All views contain benchmark references and may contaminate evaluations if used for training."
        ),
        "provenance": "provenance/",
        "views": {},
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as temp:
        stage = Path(temp) / "reference"
        stage.mkdir()
        notices = stage / "notices"
        notices.mkdir()
        for name, sha in metadata.items():
            if name == "LICENSE" or name.startswith("data/third_party_licenses/"):
                (notices / Path(name).name).write_bytes(read_blob(corpus, sha))
            elif (PurePosixPath(name).match("data/*/data/index.json")
                  or name in {"data/ntp4vc/data/test_set.lean.txt.lst",
                              "corpus-extension/semantic_canonical_resolutions.json"}):
                relpath = PurePosixPath(name)
                if relpath.is_absolute() or ".." in relpath.parts:
                    raise ValueError(f"invalid archived metadata path: {name}")
                path = stage / "provenance" / relpath
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(read_blob(corpus, sha))
        for view in views:
            rows = training_rows(view, members, statements, proofs, language, reviews, blocked, duplicates, style=style)
            report["views"][view] = write_view(stage / view, rows, view=view, format=format, style=style)
        (stage / "manifest.json").write_bytes(encode(report))
        stage.rename(output)
    return report


def add_arguments(parser):
    parser.add_argument("--corpus", type=Path, required=True, help="directory from the released corpus importer")
    parser.add_argument("--output", type=Path, required=True, help="new output directory")
    parser.add_argument("--include-benchmark-references", action="store_true",
                        help="acknowledge evaluation data and export reference views")
    parser.add_argument("--view", action="append", choices=VIEWS, dest="views")
    parser.add_argument("--format", choices=("jsonl", "parquet"), default="jsonl")
    parser.add_argument("--style", choices=("standard", "chat"), default="standard")


def run_command(args):
    report = export_benchmark(args.corpus, args.output, views=args.views or VIEWS,
                              include_benchmark_references=args.include_benchmark_references,
                              format=args.format, style=args.style)
    print(json.dumps(report, ensure_ascii=False))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    add_arguments(parser)
    args = parser.parse_args()
    try:
        return run_command(args)
    except (OSError, ValueError, ImportError) as exc:
        parser.exit(2, f"{parser.prog}: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
