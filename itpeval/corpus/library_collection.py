"""Collect native library extraction bundles without rerunning their provers."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.core.declarations import Context, FormalObject
from itpeval.corpus.contexts import ContextTable
from itpeval.corpus.datasets import premise_rows
from itpeval.corpus.parquet import _schema, write_rows_parquet
from itpeval.corpus.storage import digest, encode, object_id, read_jsonl


@dataclass(frozen=True)
class Library:
    name: str
    revision: str | None
    bundles: tuple[Path, ...]
    license: str | None = None


def load_catalog(path: Path) -> tuple[Library, ...]:
    """Load library snapshots and resolve bundle locations relative to the catalog."""
    path = Path(path).resolve(strict=True)
    document = json.loads(path.read_bytes())
    if (not isinstance(document, dict) or set(document) != {"schema_version", "libraries"}
            or type(document["schema_version"]) is not int or document["schema_version"] != 1
            or not isinstance(document["libraries"], list) or not document["libraries"]):
        raise ValueError("expected a version-one catalog with a nonempty libraries list")

    libraries = []
    snapshots = set()
    for entry in document["libraries"]:
        if (not isinstance(entry, dict) or {"name", "bundles"} - entry.keys()
                or entry.keys() - {"name", "revision", "license", "bundles"}):
            raise ValueError("each library entry needs a name and a list of bundles")
        name = entry["name"]
        revision = entry.get("revision")
        license_name = entry.get("license")
        if not isinstance(name, str) or not name.strip():
            raise ValueError("each library needs a nonempty name")
        if any(value is not None and (not isinstance(value, str) or not value.strip())
               for value in (revision, license_name)):
            raise ValueError(f"expected a nonempty revision or license label for {name}")
        if (name, revision) in snapshots:
            raise ValueError(f"duplicate library snapshot: {name} ({revision})")
        locations = entry["bundles"]
        if (not isinstance(locations, list) or not locations
                or not all(isinstance(location, str) and location.strip() for location in locations)):
            raise ValueError(f"choose at least one bundle directory for {name}")
        bundles = tuple((path.parent / location).resolve(strict=True) for location in locations)
        if len(set(bundles)) != len(bundles):
            raise ValueError(f"duplicate bundle path for {name}")
        if any(not bundle.is_dir() for bundle in bundles):
            raise ValueError(f"bundle paths for {name} must select directories")
        snapshots.add((name, revision))
        libraries.append(Library(name, revision, bundles, license_name))
    return tuple(libraries)


def _bundle_report(bundle):
    raw = (bundle / "report.json").read_bytes()
    report = json.loads(raw)
    if (not isinstance(report, dict) or type(report.get("schema_version")) is not int
            or report["schema_version"] != 1 or report.get("failed") != []):
        raise ValueError(f"expected a complete version-one extraction in {bundle}")
    required = ("prover", "environment_id", "entrypoint", "extractor_revision", "project_inputs",
                "declarations", "fields", "succeeded", "skipped")
    if any(key not in report for key in required) or any(
            not isinstance(report[key], str) or not report[key]
            for key in ("prover", "environment_id", "entrypoint")):
        raise ValueError(f"missing extraction report fields in {bundle}")
    if (type(report["declarations"]) is not int or report["declarations"] < 0
            or not isinstance(report["succeeded"], list)
            or not all(isinstance(unit, str) for unit in report["succeeded"])
            or not isinstance(report["skipped"], list)
            or not isinstance(report["fields"], dict)
            or not isinstance(report["fields"].get("proof_used_premises"), str)):
        raise ValueError(f"invalid counts, coverage or fields in {bundle}")
    bundle_id = object_id(1, report["extractor_revision"], report["environment_id"],
                          report["project_inputs"], report["entrypoint"])
    return report, bundle_id, digest(raw)


def _write_bundle(bundle, report, provenance, declarations, premises, premise_visibility):
    contexts = ContextTable(bundle)
    context_records = ((Context.from_dict({**row, "visible": []}) for row in contexts.metadata_rows())
                       if contexts.compact else (contexts.context(context_id) for context_id in contexts))
    for context in context_records:
        if context.environment_id != report["environment_id"]:
            raise ValueError(f"invalid context provenance in {bundle}")

    declaration_ids = set()
    for row in read_jsonl(bundle / "declarations.jsonl"):
        declaration = FormalObject.from_dict(row)
        if ((declaration.prover, declaration.environment_id) != (report["prover"], report["environment_id"])
                or declaration.context_id not in contexts or declaration.declaration_id in declaration_ids):
            raise ValueError(f"invalid declaration provenance or duplicate declaration in {bundle}")
        declaration_ids.add(declaration.declaration_id)
        declarations.write(encode({**row, **provenance}) + b"\n")
    if len(declaration_ids) != report["declarations"]:
        raise ValueError(f"declaration count does not match the report in {bundle}")

    for row in premise_rows(bundle, visibility=premise_visibility, contexts=contexts):
        task_id = object_id("premise_selection", provenance["bundle_id"], row["declaration"]["declaration_id"])
        premises.write(encode({"schema_version": 1, "operation": "premise_selection",
                               "task_id": task_id, **row, **provenance}) + b"\n")
    return len(declaration_ids)


def export_collection(catalog: Path, output: Path, *, format: str = "jsonl", premise_visibility="expanded") -> dict:
    """Export declaration and premise-selection tables with library and bundle provenance."""
    if format not in {"jsonl", "parquet", "both"}:
        raise ValueError("format must be jsonl, parquet or both")
    if premise_visibility not in {"expanded", "reference"}:
        raise ValueError("expected expanded or reference premise visibility")
    libraries = load_catalog(catalog)
    output = Path(output).absolute()
    if output.exists() or output.is_symlink():
        raise FileExistsError(output)
    if format in {"parquet", "both"}:
        try:
            import pyarrow as pa
        except ImportError as exc:
            raise ValueError("Parquet export requires the itpeval[parquet] extra") from exc

    result = {"schema_version": 1, "format": format, "premise_visibility": premise_visibility, "libraries": []}
    total = 0
    output.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=output.parent) as tmp:
        stage = Path(tmp) / "collection"
        stage.mkdir()
        with (stage / "declarations.jsonl").open("wb") as declarations, (stage / "premises.jsonl").open("wb") as premises:
            for library in libraries:
                reports = []
                seen = set()
                successful_sources = set()
                count = 0
                for bundle in library.bundles:
                    report, bundle_id, report_sha256 = _bundle_report(bundle)
                    if bundle_id in seen:
                        raise ValueError(f"duplicate bundle for {library.name}: {bundle}")
                    seen.add(bundle_id)
                    provenance = {"library": library.name, "library_revision": library.revision, "bundle_id": bundle_id}
                    row_count = _write_bundle(bundle, report, provenance, declarations, premises, premise_visibility)
                    count += row_count
                    successful_sources.update((report["environment_id"], source) for source in report["succeeded"])
                    reports.append({"bundle_id": bundle_id, "path": str(bundle), "report_sha256": report_sha256,
                                    **{key: report[key] for key in ("prover", "environment_id", "entrypoint",
                                                                   "declarations", "fields", "succeeded", "skipped")}})
                result["libraries"].append({"name": library.name, "revision": library.revision,
                                            "license": library.license, "declarations": count,
                                            "successful_source_units": len(successful_sources), "bundles": reports})
                total += count
        if format in {"parquet", "both"}:
            columns = [pa.field(key, pa.string()) for key in ("library", "library_revision", "bundle_id")]
            for view in ("declarations", "premises"):
                source = stage / f"{view}.jsonl"
                schema = pa.schema([*_schema(pa, view), *columns])
                write_rows_parquet(source, stage / f"{view}.parquet", schema)
                if format == "parquet":
                    source.unlink()
        result["counts"] = {"declarations": total, "premises": total}
        (stage / "manifest.json").write_bytes(encode(result) + b"\n")
        stage.rename(output)
    return result


def add_arguments(parser):
    parser.add_argument("--catalog", type=Path, required=True, help="JSON catalog of named library extraction bundles")
    parser.add_argument("--output", type=Path, required=True, help="new collection directory")
    parser.add_argument("--format", choices=("jsonl", "parquet", "both"), default="jsonl")
    parser.add_argument("--premise-visibility", choices=("expanded", "reference"), default="expanded",
                        help="write visibility inline or reference each bundle context")


def run_command(args):
    result = export_collection(args.catalog, args.output, format=args.format, premise_visibility=args.premise_visibility)
    print(json.dumps({"path": str(args.output.resolve()), "counts": result["counts"]}, ensure_ascii=False))
    return 0
