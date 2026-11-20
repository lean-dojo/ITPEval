"""Build the documentation from release metadata and preserve repository-relative citations."""
from io import BytesIO
from html import escape
import hashlib
import json
import os
from pathlib import Path
import re
from statistics import median
import subprocess
from urllib.parse import quote, urlsplit
from zipfile import ZIP_DEFLATED, ZipFile

try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10
    import tomli as tomllib

from bs4 import BeautifulSoup
from mkdocs.plugins import event_priority
from mkdocs.structure.files import File
from mkdocs.utils import get_relative_url

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
LINK = re.compile(r"(?<=\]\()([^\s)]+)(?=\))")


def nav_sources(entries):
    for item in entries:
        for value in item.values() if isinstance(item, dict) else (item,):
            if isinstance(value, list):
                yield from nav_sources(value)
            else:
                yield Path(value)


def on_config(config):
    metadata = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))["project"]
    profiles = json.loads((ROOT / "website/provers.json").read_text(encoding="utf-8"))
    provers = []
    for source in nav_sources(config.nav):
        if source.parent != Path("provers") or source.suffix != ".md" or source.stem == "index":
            continue
        title = (DOCS / source).read_text(encoding="utf-8").splitlines()[0].removeprefix("# ")
        provers.append(dict(id=source.stem, title=title, **profiles[source.stem]))
    if set(profiles) != {p["id"] for p in provers}:
        raise ValueError("Every prover guide needs a profile in website/provers.json")
    # Chapter timings come from the same file the HTML video player uses.
    chapters = (ROOT / "website/theme/assets/tour/chapters.vtt").read_text(encoding="utf-8")
    starts = {name: int(minute) * 60 + int(second) for minute, second, name in
              re.findall(r"^00:(\d{2}):(\d{2})\.000 --> [^\n]+\n([^\n]+)", chapters, re.M)}
    for prover in provers:
        prover["tour_start"] = starts[prover["title"]]
    config.extra.update(version=metadata["version"], provers=provers)
    return config


def source_asset(path):
    """Offer linked code directories as small archives containing tracked source files."""
    rel = path.relative_to(ROOT).as_posix()
    if path.is_dir():
        names = subprocess.check_output(["git", "ls-files", "-z", "--", rel], cwd=ROOT).decode().split("\0")
        data = BytesIO()
        with ZipFile(data, "w", ZIP_DEFLATED) as archive:
            for name in sorted(filter(None, names)):
                archive.write(ROOT / name, Path(name).relative_to(path.parent.relative_to(ROOT)))
        return "assets/repository/" + rel + ".zip", data.getvalue()
    target = "assets/repository/" + rel.removeprefix(".")
    if path.suffix.lower() not in {".json", ".jsonl", ".jpg", ".png", ".txt"}:
        target += ".txt"
    return target, path.read_bytes()


def add_explorer_data(files, config):
    runtime = ROOT / "benchmarks/runtime"
    timing = json.loads((runtime / "cache-latency.json").read_bytes())
    timings = {}
    proofs = {}
    fixtures = ROOT / "itpeval/tests/fixtures/projects"
    for row in timing["rows"]:
        timings[row["prover"]] = {
            key: median(sample[key] for sample in row["samples"])
            for key in ("miss_s", "hit_s")
        }
    for profile in config.extra["provers"]:
        prover = profile["id"]
        project = fixtures / prover / "completion"
        task = json.loads((project / "completion.json").read_bytes())
        source = (project / task["entrypoint"]).read_text(encoding="utf-8")
        anchor = task["anchor"]
        slot = task["proof_slot"]
        offset = source.index(anchor) + anchor.index(slot)
        directory = runtime / "evidence" / prover
        conformance = json.loads((directory / "conformance.json").read_bytes())
        episode_path = directory / conformance["episode"]
        episode = json.loads(episode_path.read_bytes())
        transitions = episode["transitions"]
        started = [task["allowed_edits"][1], task["allowed_edits"][0]]
        if [step["action"]["candidate"] for step in transitions] != started:
            raise ValueError(f"The proof exercise and recorded edits differ for {prover}")
        guide = profile["completion_guide"]
        attempts = [
            {"candidate": step["action"]["candidate"],
             "verdict": step["observation"]["checker_outcome"],
             "explanation": explanation}
            for step, explanation in zip(transitions, (guide["first_reason"], guide["solution_reason"]))
        ]
        uri = f"assets/proof-episodes/{prover}.jsonl"
        files.append(File.generated(config, uri, content=episode_path.read_bytes()))
        proofs[prover] = {"entrypoint": task["entrypoint"],
                          "before": source[:offset], "after": source[offset + len(slot):],
                          "attempts": attempts, "evidence": uri}
    for name, records in (("proof-exercises", proofs), ("timing-comparison", timings)):
        files.append(File.generated(config, f"assets/{name}.json", content=json.dumps(records, ensure_ascii=False)))
    scale = {}
    for name in ("scalability-nine.json", "scalability-hol-light.json"):
        receipt = runtime / name
        if receipt.is_file():
            for row in json.loads(receipt.read_bytes())["provers"]:
                scale[row["prover"]] = {
                    "jobs": len(row["jobs"]),
                    "samples": [{key: sample[key] for key in (
                        "workers", "attempts_per_second", "p95_time_to_verdict_s",
                    )} for sample in row["samples"]],
                }
    config.extra["scale_comparison"] = set(scale) == set(proofs)
    if config.extra["scale_comparison"]:
        files.append(File.generated(config, "assets/scale-comparison.json", content=json.dumps(scale)))


def on_files(files, config):
    add_explorer_data(files, config)
    skill_root = DOCS / "agents/skills"
    adapters = ROOT / "examples/prover-adapters"
    sprig = adapters / "sprig"
    # Only ship source, adapter scripts and the public example; local experiments stay local.
    archives = [
        ("itpeval-agent-skills", skill_root, sorted(skill_root.glob("*/SKILL.md"))),
        ("sprig", adapters, [sprig / name for name in (
            "sprig.py", "kernel.py", "check.sh", "install.sh", "version.sh", "adapter.json",
            "typed-adapter.json", "verify.py", "extract.py", "source.py", "hello/completion.json",
            "hello/problem.json", "hello/proof.json", "test_sprig.py")]),
    ]
    for name, base, entries in archives:
        bundle = BytesIO()
        with ZipFile(bundle, "w", ZIP_DEFLATED) as archive:
            for entry in entries:
                archive.write(entry, entry.relative_to(base).as_posix())
        files.append(File.generated(config, f"assets/{name}.zip", content=bundle.getvalue()))
    # Markdown authors can use the same relative links on GitHub and on the website.
    styles = []
    for p in config.extra["provers"]:
        selector = f'[data-prover="{p["id"]}"]'
        styles.append(f'{selector}, [data-listing="{p["id"]}"] {{ --prover-accent: {p["accent"]}; }}')
        if p["logo"]:
            styles.append(f'{selector}::before {{ background-image: url("provers/{p["logo"]}"); }}')
        else:
            styles.append(f'{selector}::before {{ display: none; }}')
    files.append(File.generated(config, "assets/prover-logos.css", content="\n".join(styles)))
    # Preserve bookmarks to the Lean example after moving it under its prover.
    target = "../../provers/lean4/mathlib-and-cslib/"
    redirect = (f'<!doctype html><html lang="en"><title>Mathlib and CSLib</title>'
                f'<script>location.replace("{target}" + location.search + location.hash)</script>'
                f'<meta http-equiv="refresh" content="0;url={target}"><a href="{target}">Mathlib and CSLib</a></html>')
    files.append(File.generated(config, "guides/lean-libraries/index.html", content=redirect))
    license_path = ROOT / "LICENSE"
    license_uri, license_text = source_asset(license_path)
    files.append(File.generated(config, license_uri, content=license_text))
    assets = {license_path: license_uri}
    frozen = json.loads((ROOT / "eval/benchmark-lock.json").read_text(encoding="utf-8"))["revision"]
    for doc in files.documentation_pages():
        origin = DOCS / doc.src_uri

        def resolve(match):
            ref = urlsplit(match.group())
            if ref.scheme or ref.netloc or not ref.path:
                return match.group()
            path = (origin.parent / ref.path).resolve()
            if path.is_relative_to(DOCS) and path.suffix != ".py":
                target = Path(os.path.relpath(path, origin.parent)).as_posix()
                return target + ("#" + ref.fragment if ref.fragment else "")
            rel = path.relative_to(ROOT)
            if not path.exists():
                raise FileNotFoundError(f"{doc.src_uri} links to missing {rel}")
            if rel.parts[0] in {"data", "corpus-extension", "eval"}:
                kind = "tree" if path.is_dir() else "blob"
                target = f"{config.repo_url}/{kind}/{frozen}/{quote(rel.as_posix())}"
            else:
                if path not in assets:
                    uri, raw = source_asset(path)
                    files.append(File.generated(config, uri, content=raw))
                    assets[path] = uri
                target = Path(os.path.relpath(assets[path], Path(doc.src_uri).parent)).as_posix()
            return target + ("#" + ref.fragment if ref.fragment else "")

        content = doc.content_string
        # Preserve fenced examples even if a code sample contains Markdown syntax.
        parts = re.split(r"(^`{3,}[^\n]*\n.*?^`{3,}[ \t]*$)", content, flags=re.M | re.S)
        doc.content_string = "".join(piece if i % 2 else LINK.sub(resolve, piece)
                                     for i, piece in enumerate(parts))
    config.extra["release_files"] = {}
    distribution_dir = os.getenv("ITPEVAL_DOCS_DIST")
    if distribution_dir:
        release_files = {}
        version = config.extra["version"]
        for kind, filename, key in (("wheel", f"itpeval-{version}-py3-none-any.whl", "wheel_sha256"),
                                    ("sdist", f"itpeval-{version}.tar.gz", "sdist_sha256")):
            content = (Path(distribution_dir) / filename).read_bytes()
            sha = hashlib.sha256(content).hexdigest()
            for prover in config.extra["provers"]:
                receipt = ROOT / "benchmarks/runtime/evidence" / prover["id"] / "distribution.json"
                if json.loads(receipt.read_bytes())[kind][key] != sha:
                    raise ValueError(f"{filename} differs from the {prover['id']} release receipt")
            uri = "downloads/" + filename
            files.append(File.generated(config, uri, content=content))
            release_files[kind] = {"name": filename, "uri": uri, "sha256": sha}
        config.extra["release_files"] = release_files
    return files


def on_page_markdown(markdown, page, config, files):
    if "<!-- dataset-controls -->" in markdown:
        options = []
        for prover in config.extra["provers"]:
            selected = " selected" if prover["id"] == "metamath" else ""
            options.append(f'<option value="{escape(prover["id"])}"{selected}>{escape(prover["title"])}</option>')
        controls = ('<div class="dataset-controls" hidden><label>Prover <select name="prover">'
                    + "".join(options) + '</select></label><label>Format <select name="format">'
                    '<option value="jsonl">JSON Lines</option><option value="parquet">Parquet</option>'
                    '</select></label></div>')
        markdown = markdown.replace("<!-- dataset-controls -->", controls)
    if page.file.src_uri == "start/quickstart.md" and config.extra["release_files"]:
        wheel = config.extra["release_files"]["wheel"]
        sdist = config.extra["release_files"]["sdist"]
        return markdown.replace("<!-- release-downloads -->",
                                f"Already have a virtual environment? Download the [wheel](../{wheel['uri']}) "
                                f"or [source archive](../{sdist['uri']}) and install it with `python -m pip install FILENAME`.")
    return markdown


def on_page_content(html, page, config, files):
    soup = BeautifulSoup(html, "html.parser")
    profiles = config.extra["provers"]
    by_name = {name.casefold(): p for p in profiles for name in (p["id"], p["title"])}
    by_name["isabelle"] = by_name["isabelle/hol"]

    def brand(element, profile):
        if profile:
            element["data-prover"] = profile["id"]

    for link in soup.select("a[href]"):
        brand(link, by_name.get(link.get_text(strip=True).casefold()))
    if page.file.src_uri.startswith("provers/") and soup.h1:
        brand(soup.h1, by_name.get(Path(page.file.src_uri).stem))

    if page.file.src_uri == "start/proof-completion.md":
        guide_table = soup.select_one("h2#choose-your-prover").find_next_sibling("table")
        guide_table.insert_before(proof_explorer(page, config))
    elif page.file.src_uri in {"runtime/measurements/startup-and-caching.md", "runtime/measurements/throughput.md"}:
        marker = soup.find(string=lambda node: node.strip() == "timing-controls")
        if marker:
            marker.replace_with(timing_explorer(config))
        marker = soup.find(string=lambda node: node.strip() == "scale-controls")
        if marker and config.extra["scale_comparison"]:
            marker.replace_with(scale_explorer(config))
    elif page.file.src_uri.startswith("provers/") and (heading := soup.select_one("h2#proof-completion")):
        listing = heading.find_next_sibling("figure", class_="proof-listing")
        if listing:
            listing.insert_after(proof_explorer(page, config, prover=Path(page.file.src_uri).stem))
    for table in soup.find_all("table"):
        wrapper = soup.new_tag("div", attrs={"class": "table-wrap", "tabindex": "0", "role": "region"})
        heading = table.find_previous(["h1", "h2", "h3"])
        wrapper["aria-label"] = heading.get_text(" ", strip=True) if heading else "Table"
        if page.file.src_uri == "provers/index.md":
            wrapper["class"].append("prover-directory")
        if page.file.src_uri == "start/proof-completion.md":
            wrapper["class"].append("exercise-table")
        table.wrap(wrapper)
        for cell in table.select("tbody tr > td:first-child"):
            if not cell.find("a"):
                brand(cell, by_name.get(cell.get_text(strip=True).casefold()))
    return str(soup)


def prover_select(config, selected):
    options = []
    for profile in config.extra["provers"]:
        choice = " selected" if profile["id"] == selected else ""
        options.append(f'<option value="{profile["id"]}"{choice}>{escape(profile["title"])}</option>')
    return '<label>Prover <select name="prover">' + "".join(options) + "</select></label>"


def proof_explorer(page, config, prover=None):
    controls = prover_select(config, "lean4") if prover is None else ""
    link = get_relative_url("provers/", page.url)
    return BeautifulSoup(f"""
      <details class="docs-explorer proof-explorer" data-exercise="{prover or ''}" data-guide-base="{link}" hidden>
        <summary>Try two proof candidates</summary>
        <div class="explorer-body">
          <p>Choose an edit to see how it fits in the file. Submit it to reveal the result of a recorded native check.</p>
          <div class="explorer-controls">{controls}<label>Proof fragment <select name="candidate"></select></label></div>
          <strong class="exercise-file"></strong>
          <pre><code><span class="source-before"></span><mark class="formal-proof"></mark><span class="source-after"></span></code></pre>
          <button type="button" class="btn primary">Reveal verdict</button>
          <div aria-live="polite" class="proof-feedback"></div>
          <p class="explorer-links"><a class="exercise-guide">Open the editor exercise</a>
            <a class="exercise-evidence">Read the recorded episode</a></p>
        </div>
      </details>""", "html.parser").details


def timing_explorer(config):
    return BeautifulSoup(f"""
      <section class="docs-explorer timing-explorer" aria-label="Compare verification times" hidden>
        <div class="explorer-body">
          <div class="explorer-controls">{prover_select(config, 'hol-light')}</div>
          <dl class="timing-values" aria-live="polite">
            <div><dt>Run the native checker</dt><dd data-time="miss_s"></dd></div>
            <div><dt>Repeat the exact candidate</dt><dd data-time="hit_s"></dd></div>
            <div><dt>First time ÷ repeat time</dt><dd data-speedup></dd></div>
          </dl>
          <p>Median wall time from three trials on the fixed proof task, including validation of the project lock.</p>
        </div>
      </section>""", "html.parser").section


def scale_explorer(config):
    return BeautifulSoup(f"""
      <section class="docs-explorer scale-explorer" aria-label="Compare batch throughput" hidden>
        <div class="explorer-body">
          <div class="explorer-controls">{prover_select(config, 'agda')}</div>
          <dl class="timing-values" aria-live="polite">
            <div><dt>Distinct jobs per run</dt><dd data-job-count></dd></div>
            <div><dt>1 worker</dt><dd data-throughput="1"></dd></div>
            <div><dt>Up to 4 workers</dt><dd data-throughput="4"></dd></div>
            <div><dt>4-worker p95 time to verdict</dt><dd data-verdict-time></dd></div>
          </dl>
          <p>Time to verdict includes time spent waiting for a worker. Both runs checked the same inputs with result caching disabled.</p>
        </div>
      </section>""", "html.parser").section


@event_priority(-100)
def on_post_build(config):
    # A local script works under a project subpath and needs no search service.
    site = Path(config.site_dir)
    index = json.loads((site / "search/search_index.json").read_text(encoding="utf-8"))
    (site / "assets/doc-search.js").write_text(
        "window.ITPEvalSearch = " + json.dumps(index["docs"], ensure_ascii=True) + ";\n", encoding="utf-8"
    )
