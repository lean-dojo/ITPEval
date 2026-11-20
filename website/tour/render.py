"""Render the homepage film from repository examples. See website/README.md."""
import base64
from io import BytesIO
import json
import mimetypes
from pathlib import Path
import subprocess

import imageio_ffmpeg
from PIL import Image
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[2]
THEME = ROOT / "website/theme/assets"
OUTPUT = THEME / "tour"
FPS = 20
CHAPTER_SECONDS = 6


def data_url(path):
    mime = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
    return f"data:{mime};base64," + base64.b64encode(path.read_bytes()).decode()


def collect():
    profiles = json.loads((ROOT / "website/provers.json").read_text())
    scenes = []
    for key, profile in profiles.items():
        report = json.loads((ROOT / f"benchmarks/runtime/evidence/{key}/extraction.json").read_text())
        source = ROOT / "itpeval/tests/fixtures/projects" / key / "library" / report["entrypoint"]
        first, last = profile["example_lines"]
        excerpt = "\n".join(source.read_text().splitlines()[first - 1:last]).strip()
        if profile["example_symbol"] not in excerpt:
            raise ValueError(f"Review the selected source lines for {key}")
        adapter = json.loads((ROOT / "itpeval/provers" / key / "adapter.json").read_text())
        logo = profile["logo"]
        scenes.append(dict(id=key, name="Isabelle/HOL" if key == "isabelle" else adapter["name"],
                           image=data_url(ROOT / "docs/assets/provers" / logo) if logo else None,
                           wordmark=profile.get("logo_is_wordmark", False),
                           file=source.name, source=excerpt, symbol=profile["example_symbol"],
                           accent=profile["accent"], declaration=profile["checked_example"]["name"],
                           status=profile["checked_example"]["status"], note=profile["example_comment"],
                           files=len(report["succeeded"]), declarations=report["declarations"]))
    return scenes


def stamp(seconds):
    return f"00:{seconds // 60:02d}:{seconds % 60:02d}.000"


def render():
    scenes = collect()
    OUTPUT.mkdir(exist_ok=True)
    captions = ["WEBVTT", ""]
    chapters = ["WEBVTT", ""]
    with sync_playwright() as browser_tools:
        browser = browser_tools.chromium.launch()
        page = browser.new_page(viewport={"width": 960, "height": 540}, device_scale_factor=1)
        page.goto(Path(__file__).with_name("scene.html").as_uri())
        fonts = [("DocSans", "dm-sans-latin-400-normal"), ("DocMono", "ibm-plex-mono-latin-400-normal")]
        for family, name in fonts:
            page.add_style_tag(content=f'@font-face {{font-family:{family};src:url("{data_url(THEME / "fonts" / (name + ".woff2"))}")}}')
        cmd = [imageio_ffmpeg.get_ffmpeg_exe(), "-y", "-loglevel", "error", "-f", "image2pipe",
               "-vcodec", "png", "-r", str(FPS), "-i", "-", "-an", "-c:v", "libx264",
               "-crf", "19", "-pix_fmt", "yuv420p", "-movflags", "+faststart", str(OUTPUT / "libraries.mp4")]
        with subprocess.Popen(cmd, stdin=subprocess.PIPE) as encoder:
            for i, scene in enumerate(scenes):
                page.evaluate("args => selectScene(...args)", [scene, i, len(scenes)])
                page.evaluate("document.fonts.ready")
                for frame in range(FPS * CHAPTER_SECONDS):
                    # The record settles in the first second. Hold that frame for reading.
                    if frame <= FPS:
                        page.evaluate("seconds => drawFrame(seconds)", frame / FPS)
                        png = page.screenshot()
                    encoder.stdin.write(png)
                    if i == 0 and frame == FPS * 2:
                        Image.open(BytesIO(png)).convert("RGB").save(OUTPUT / "poster.webp", quality=90)
                timing = f"{stamp(i * CHAPTER_SECONDS)} --> {stamp((i + 1) * CHAPTER_SECONDS)}"
                captions += [timing, f"{scene['name']} · {scene['file']}",
                             f"{scene['declaration']} · {scene['status'].replace('_', ' ')}", ""]
                chapters += [timing, scene["name"], ""]
            encoder.stdin.close()
            if encoder.wait():
                raise RuntimeError("Video encoding failed")
        browser.close()
    (OUTPUT / "captions.vtt").write_text("\n".join(captions))
    (OUTPUT / "chapters.vtt").write_text("\n".join(chapters))


if __name__ == "__main__":
    render()
