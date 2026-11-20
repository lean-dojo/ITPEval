"""Build fixed HOL4 dependency theories at stable paths for native Holmake."""
import fcntl
import json
import os
from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import tempfile

from itpeval.backends.projects import project_file
from itpeval.core.records import digest
from itpeval.environments.cache import sha256
from itpeval.runtime.process import run_process


def _contents(root):
    return {p.relative_to(root).as_posix(): sha256(p) for p in sorted(root.rglob("*"))
            if p.is_file()}


@dataclass(frozen=True)
class TheoryBuild:
    environment_id: str
    path: Path
    content_id: str
    cache_hit: bool

    def validate(self, prepared):
        if prepared.environment_id != self.environment_id or digest(_contents(self.path)) != self.content_id:
            raise ValueError("HOL4 dependency theory build changed or belongs to a different environment")

    def stage(self, prepared, workspace):
        """Stage native dependency objects where Holmake may write scan metadata."""
        self.validate(prepared)
        local = Path(workspace) / "dependencies"
        shutil.copytree(self.path, local)
        return ["--no_prereqs", "-I", str(local)]


def prepare_theories(prepared, source_files, *, timeout_s=300):
    """Compile only named trusted theory sources. An attempt's own products stay separate."""
    prepared.validate()
    names = tuple(sorted(set(source_files)))
    pattern = r"[A-Za-z][A-Za-z0-9_']*Script\.sml"
    if prepared.spec.prover != "hol4" or not names or not all(re.fullmatch(pattern, n) for n in names):
        raise ValueError("expected a HOL4 environment and top-level dependency theory scripts")
    key = digest({"environment": prepared.environment_id, "sources": names, "format": 2})
    store = prepared.cache / "builds/hol4" / key
    store.mkdir(parents=True, exist_ok=True)
    index = store / "complete.json"
    with (store / "build.lock").open("ab") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if index.exists():
            info = json.loads(index.read_text())
            build = TheoryBuild(prepared.environment_id, store / info["directory"], info["content_id"], True)
            build.validate(prepared)
            return build
        # .uo files embed absolute paths. Publish the index after compilation
        # without relocating the underlying native build directory.
        directory = Path(tempfile.mkdtemp(prefix="dependencies-", dir=store))
        try:
            for name in names:
                shutil.copy2(project_file(prepared.project, name), directory / name)
            targets = [name.removesuffix("Script.sml") + "Theory.uo" for name in names]
            native_env = {k: os.environ[k] for k in ("HOME", "PATH", "LANG", "LC_ALL", "USER") if k in os.environ}
            native_env.update(prepared.environment)
            proc = run_process([str(prepared.prefix / "hol4/bin/Holmake"), *targets], cwd=directory, env=native_env,
                               timeout_s=timeout_s)
            if proc.outcome != "exited" or proc.returncode or not all(
                    (directory / ".hol/objs" / t).is_file() for t in targets):
                raise RuntimeError("HOL4 dependency compilation failed: " + (proc.stdout + proc.stderr)[-1500:])
            fingerprint = digest(_contents(directory))
            tmp = index.with_suffix(".tmp")
            tmp.write_text(json.dumps({"directory": directory.name, "content_id": fingerprint}))
            tmp.replace(index)
        except BaseException:
            shutil.rmtree(directory)
            raise
    return TheoryBuild(prepared.environment_id, directory, fingerprint, False)
