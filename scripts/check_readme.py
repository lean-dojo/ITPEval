"""Execute every runnable README block in one clean shell and disposable checkout."""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        checkout = work / "checkout"
        subprocess.run(["git", "clone", "--quiet", "--shared", root, checkout], check=True)
        # Exercise the working copy as well as committed CI revisions. The
        # editable installs, toolchain, exports and native logs stay disposable.
        changed = subprocess.check_output(["git", "diff", "--name-only", "--no-renames", "-z", "HEAD"], cwd=root)
        new = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=root)
        for name in filter(None, os.fsdecode(changed + new).split("\0")):
            original, target = root / name, checkout / name
            if original.is_file():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(original, target)
            else:
                target.unlink(missing_ok=True)
        blocks = re.findall(r"^```(\w+)\n(.*?)^```$", (checkout / "README.md").read_text(),
                            flags=re.MULTILINE | re.DOTALL)
        commands = ["set -eu -o pipefail"]
        for language, body in blocks:
            if language in {"bash", "sh"}:
                commands.append(body)
            elif language == "python":
                commands.extend(["python - <<'ITPEVAL_README_PYTHON'", body, "ITPEVAL_README_PYTHON"])
            else:
                raise ValueError(f"unhandled README code block language {language!r}")
        env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH" and not k.startswith("ITPEVAL_")}
        venv = work / "venv"
        subprocess.run([sys.executable, "-m", "venv", venv], check=True)
        env.update(PATH=str(venv / "bin") + os.pathsep + env["PATH"], VIRTUAL_ENV=str(venv),
                   ITPEVAL_RESULTS_DIR=str(work / "benchmark-results"))
        subprocess.run(["bash", "-c", "\n".join(commands)], cwd=checkout, env=env, check=True)
        manifest = json.loads((checkout / "released-corpus/manifest.json").read_bytes())
        if (manifest["items"], manifest["artifacts"]) != (2634, 26340):
            raise ValueError("README benchmark import lost released items or language artifacts")
        for pattern in ("metamath-dataset/*.premises.jsonl", "evidence/metamath/episodes.jsonl"):
            if not any(checkout.glob(pattern)):
                raise ValueError(f"README did not produce {pattern}")
        print(f"Passed {len(blocks)} README blocks, including both installs and the benchmark dry run.")


if __name__ == "__main__":
    main()
