"""Validate the built documentation, or run the quickstart with an installed Lean."""
import argparse
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


class PageLinks(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.targets = set()
        self.links = []
        self.feed(text)
        self.close()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.targets.add(attrs["id"])
        key = {"a": "href", "link": "href", "script": "src", "img": "src"}.get(tag)
        if key in attrs:
            self.links.append(attrs[key])


def check_site(site):
    site = site.resolve(strict=True)
    pages = {p: PageLinks(p.read_text(encoding="utf-8")) for p in site.rglob("*.html")}
    home = site / "index.html"
    if home not in pages:
        raise ValueError("Missing homepage")
    index = json.loads((site / "search/search_index.json").read_text(encoding="utf-8"))
    search_links = [entry["location"] for entry in index["docs"]]
    if not search_links:
        raise ValueError("Empty documentation search index")
    checked = 0
    for file, page in pages.items():
        refs = page.links + (search_links if file == home else [])
        for link in refs:
            ref = urlsplit(link)
            if ref.netloc or ref.scheme:
                continue
            target = (file.parent / unquote(ref.path)).resolve() if ref.path else file
            if target.is_dir():
                target = target / "index.html"
            if not target.is_relative_to(site) or not target.is_file():
                raise ValueError(f"{file.relative_to(site)}: missing target {link}")
            if ref.fragment and target in pages and unquote(ref.fragment) not in pages[target].targets:
                raise ValueError(f"{file.relative_to(site)}: missing section {link}")
            checked += 1
    print(f"Checked {len(pages)} pages and {checked} local links, assets and search locations.")


def _code_blocks(document, *languages):
    tags = "|".join(re.escape(language) for language in languages)
    return re.findall(rf"^`{{3}}(?:{tags})\n(.*?)^`{{3}}$", document, re.M | re.S)


def _run_shell(code, cwd):
    return subprocess.check_output(["bash", "-eu", "-o", "pipefail", "-c", code], cwd=cwd, text=True)


def _check_reference_cli(cwd):
    document = (ROOT / "docs/reference/cli.md").read_text(encoding="utf-8")
    file_check, *commands = _code_blocks(document, "bash", "sh")
    result = json.loads(_run_shell(file_check, cwd))
    if (result.get("prover") != "lean4" or result.get("ok") is not True or result.get("returncode") != 0):
        raise ValueError(f"CLI file check did not accept MyProof.lean: {result!r}")

    available_commands = []
    for command in commands:
        if re.search(r"^itpeval dataset metamath\s", command, re.M):
            # CI's Lean job does not install Metamath. Keep the documented
            # dataset check when running against a prefix that has it.
            probe = subprocess.run(["itpeval", "toolchains", "status", "metamath", "--json"],
                                   cwd=cwd, stdout=subprocess.PIPE, text=True)
            (tool,) = json.loads(probe.stdout)["toolchains"]
            if probe.returncode == 1 and tool["status"] == "missing":
                print("Skipped the CLI dataset example because Metamath is not installed.")
                continue
            probe.check_returncode()
        available_commands.append(command)
    _run_shell("\n".join(available_commands), cwd)


def check_quickstart():
    doc = (ROOT / "docs/start/quickstart.md").read_text(encoding="utf-8")
    source, *_ = _code_blocks(doc, "lean4")
    examples = _code_blocks(doc, "python")
    outputs = _code_blocks(doc, "text")
    file_check, proof_check = _code_blocks(doc, "bash", "sh")
    with tempfile.TemporaryDirectory() as workspace:
        python_dir, shell_dir, reference_dir = (Path(workspace) / name for name in ("python", "shell", "reference"))
        for directory in (python_dir, shell_dir, reference_dir):
            directory.mkdir()
            (directory / "MyProof.lean").write_text(source, encoding="utf-8")

        for code, output in zip(examples, outputs, strict=True):
            actual = subprocess.check_output([sys.executable, "-I", "-c", code], cwd=python_dir, text=True)
            if actual.strip() != output.strip():
                raise ValueError(f"Documented output differs from native result: {actual!r}")
            print(actual.strip())

        actual = _run_shell(file_check, shell_dir)
        if not actual.startswith("[ITPEval] prover=lean4 ok=True rc=0 "):
            raise ValueError(f"Quickstart shell file check did not accept MyProof.lean: {actual!r}")
        evidence = json.loads(_run_shell(proof_check, shell_dir))
        if (evidence.get("task_success") is not True or evidence.get("checker_outcome") != "accepted"
                or evidence.get("target_preservation") != "preserved"):
            raise ValueError(f"Quickstart shell proof check did not accept the locked theorem: {evidence!r}")

        _check_reference_cli(reference_dir)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-quickstart", action="store_true", help="requires the installed package and Lean")
    args = parser.parse_args()
    if args.native_quickstart:
        check_quickstart()
    else:
        check_site(ROOT / "website/dist")
