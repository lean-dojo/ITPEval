# Maintain the ITPEval documentation site

Edit pages in `docs/`, navigation in `mkdocs.yml`, and the theme in `website/theme/`. Prover artwork and walkthrough settings live in `website/provers.json`.

## Preview a change

Run these commands from the repository root with Python 3.10 or newer and Git. Create an environment with `python -m venv .venv`. Activate it with `source .venv/bin/activate` in Bash or `.\.venv\Scripts\Activate.ps1` in PowerShell.

```bash
# Run from the activated environment.
python -m pip install -r website/requirements.txt
python -m mkdocs serve --watch-theme --dev-addr 127.0.0.1:8764
```

Open the local preview. In VS Code Remote SSH, forward port 8764 from the Ports panel if needed. The static build goes to `website/dist/`. [Local preview](http://127.0.0.1:8764/)

## Run examples in the browser

For in-page execution, build the site and launch its optional local Jupyter server from the repository root. Install ITPEval and the toolchains you want to use in this environment.

```bash
python -m pip install -r website/requirements.txt
# The local kernel runs the code in the documentation against this checkout.
python -m pip install -e . jupyter-server ipykernel
python -m mkdocs build
python -m website.preview
```

Open the address Jupyter prints. Examples run from the repository root. Python cells on a page share a kernel, and shell cells use separate Bash processes. The static site supports editing, JSON validation, notebook downloads, and links to the Lean Playground.

Use `$...$` or `\(...\)` for inline math and `$$...$$` or `\[...\]` for display math. Keep prover source, shell variables, and literal delimiters inside code spans or fences. [KaTeX auto-render options](https://katex.org/docs/autorender.html)

## Add documentation

Add pages to `mkdocs.yml` and link to them from the relevant guide. Put platform and toolchain requirements beside the examples that need them. Search indexes headings and body text, and queries can be bookmarked with `search/?q=...`.

The sidebar and header use the order in `mkdocs.yml`. Put a section’s landing page first. For a nested section with its own overview, give the overview the same navigation label as the section. Link directly to chapters and preserve old fragment IDs when moving content.

For a backend change, update its fixture and evidence, then run `python -m scripts.generate_capabilities` before rebuilding the site.

After changing a documented Python signature, run `python -m scripts.generate_api_reference`. It updates the signature blocks in the function reference. CI checks those blocks against the checkout.

Use relative links. The build pins links to benchmark data and packages linked repository sources. Source-directory archives include tracked files.

## Typeset a prover listing

Set the excerpt’s `file` and `lines` in the profile’s `reading` entry. Set `fragment` to the exact proof text to underline. For automatic proof events, explain how the prover establishes the claim and omit `fragment`.

For a library excerpt, record the line range, symbol, libraries, and native checking status in the profile. Use native comment syntax in source examples. Put explanations beside JSON and expected output so readers can copy them directly. Highlighting rules live in `website/proof_listings.py`.

When changing an exercise, update its recorded episode to match the task manifest. The runtime comparison reads its medians from `benchmarks/runtime/cache-latency.json`.

The listing design draws on work on proof presentation and syntax highlighting. [*Untangling Mechanized Proofs*](https://pit-claudel.fr/clement/papers/alectryon-SLE20.pdf) · [*Syntax Highlighting Beyond Code Snippets*](https://arxiv.org/abs/2001.11334)

## Update the prover film

Set `logo_is_wordmark` when the artwork spells out the prover’s name. The film adds a text label for symbol-only logos.

The film uses `website/tour/scene.html` and the prover profiles. Update excerpt line ranges when examples change. Check in the rendered film, poster, captions, and chapter timings so the site can build without video tools.

```bash
# Use a documentation virtual environment for these optional rendering tools.
python -m pip install pillow playwright imageio-ffmpeg
python -m playwright install chromium
python website/tour/render.py
```

## Validate and host a release

Run `python -m mkdocs build --strict` and `python website/check.py`. With Lean installed, set `ITPEVAL_PREFIX` and run `python website/check.py --native-quickstart` to check the tutorial’s output.

In GitHub, select **Settings → Pages → Build and deployment → GitHub Actions**. From **Actions → Documentation → Run workflow**, choose the revision to publish. Pull requests and pushes build a static artifact for review. [Documentation workflow](../.github/workflows/documentation.yml)

Set `ITPEVAL_DOCS_DIST` to include the qualified wheel and source archive on the quickstart. The build checks their hashes against the installation receipts.

Upstream artwork sources are recorded in the prover profiles. HOL4’s lantern comes from its project PDF. HOL Light appears by name. [Prover profiles](provers.json)
