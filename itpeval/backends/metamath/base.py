"""Native verification and reuse of a fixed Metamath database include closure."""
import fcntl
import json
import re
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import project_file
from itpeval.core.records import digest
from itpeval.core.types import logical_path
from itpeval.environments.cache import sha256, write_json
from itpeval.runtime.process import run_process

from .syntax import tokens


@dataclass(frozen=True)
class VerifiedBase:
    base_id: str
    files: tuple[tuple[str, str], ...]
    cache_hit: bool
    receipt_path: Path


class BaseVerificationError(ValueError):
    def __init__(self, check):
        super().__init__("native base verification did not establish complete proofs")
        self.check = check


def _name(name):
    logical_path(name)
    if not re.fullmatch(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*\.mm", name):
        raise ValueError(f"unsupported Metamath include path {name!r}")
    return name


def _closure(prepared, entrypoint):
    files = {}

    def visit(path):
        if path in files:
            return
        source = project_file(prepared.project, _name(path))
        files[path] = sha256(source)
        words = iter(tokens(source.read_bytes()))
        for word, _, _ in words:
            if word == "$[":
                include = next(words, ("",))[0]
                if next(words, ("",))[0] != "$]":
                    raise ValueError(f"invalid include in {path}")
                visit(include)
    visit(entrypoint)
    return files


def _native(prepared, directory, entrypoint, commands, budget, *, cancel, timeout_s):
    executable = prepared.prefix / "metamath/bin/metamath"
    return run_process([str(executable), "set width 9999", f'read "{_name(entrypoint)}"', *commands, "exit"],
                       cwd=directory, env={"LANG": "C"}, cancel=cancel, timeout_s=timeout_s,
                       max_log_bytes=budget.max_log_bytes, memory_bytes=budget.memory_bytes,
                       cpu_seconds=budget.cpu_seconds)


def prepare_base(prepared, entrypoint, *, budgets=None, cancel=None):
    """Verify every proof in the trusted include closure and publish its native receipt."""
    from itpeval.core.types import Budgets
    budget = budgets or Budgets()
    if prepared.spec.prover != "metamath" or prepared.spec.checking_profile != "strict":
        raise ValueError("a verified base requires a strict prepared Metamath environment")
    prepared.validate()
    files = _closure(prepared, entrypoint)
    module = Path(__file__)
    identity = {"schema": 1, "environment_id": prepared.environment_id, "entrypoint": entrypoint, "files": files,
                "verifier": sha256(module), "tokenizer": sha256(module.with_name("syntax.py"))}
    key = digest(identity)
    root = prepared.cache / "builds/metamath" / key
    root.mkdir(parents=True, exist_ok=True)
    receipt = root / "verified.json"
    with (root / "build.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if receipt.exists():
            record = json.loads(receipt.read_bytes())
            native = record["native"]
            if (record["identity"] != identity or digest(native) != record["receipt_hash"] or native["returncode"]
                    or "?Error" in native["stdout"] or "All proofs in the database were verified" not in native["stdout"]):
                raise ValueError("damaged Metamath dependency verification receipt")
            return VerifiedBase(key, tuple(sorted(files.items())), True, receipt)
        with TemporaryDirectory() as tmp:
            stage = Path(tmp)
            for name in files:
                dest = stage / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(project_file(prepared.project, name).read_bytes())
                if sha256(dest) != files[name]:
                    raise ValueError("Metamath base input changed while preparing its native verification")
            check = _native(prepared, stage, entrypoint, ["verify proof *"], budget,
                            cancel=cancel, timeout_s=budget.timeout_s)
        if (check.outcome != "exited" or check.returncode or check.truncated or "?Error" in check.stdout
                or "All proofs in the database were verified" not in check.stdout):
            raise BaseVerificationError(check)
        native = {"stdout": check.stdout, "stderr": check.stderr, "duration_ms": check.duration_ms,
                  "returncode": check.returncode, "prover_build": prepared.spec.prover_build}
        write_json(receipt, {"identity": identity, "native": native, "receipt_hash": digest(native)})
    return VerifiedBase(key, tuple(sorted(files.items())), False, receipt)


def _verify_extension(task, artifact, prepared, base, *, stage, cancel=None):
    """Verify a sole target after a previously verified leading include in a fresh native process."""
    if task.prover != "metamath" or task.operation != "proof_completion":
        raise ValueError("a verified Metamath base applies only to a proof completion")
    build = prepare_base(prepared, base, cancel=cancel)
    verified = dict(build.files)
    provided = {f.path: f for f in artifact.files}
    entry = artifact.entrypoint
    if entry in verified or any(n not in provided or provided[n].sha256 != h for n, h in verified.items()):
        raise ValueError("the assembled artifact differs from the verified base include closure")
    words = [w for w, _, _ in tokens(provided[entry].data)]
    target, = task.targets
    if (words[:3] != ["$[", base, "$]"] or "$[" in words[3:] or "$a" in words[3:]
            or words.count("$p") != 1 or words[words.index("$p") - 1] != target):
        raise ValueError("a cached-base client must start with its base include and define a single target $p")
    check = _native(prepared, stage, entry, [f"verify proof {target}", f"show trace_back {target} /axioms"],
                    task.budgets, cancel=cancel, timeout_s=task.budgets.timeout_s)
    if check.outcome != "exited" or check.returncode or check.truncated:
        return check, None, build
    logs = check.stdout
    if "?Error" in logs:
        return check, "rejected", build
    if "were not proved" in logs:
        return check, "incomplete", build
    verified_label = rf"^MM> verify proof {re.escape(target)}\n{re.escape(target)}\s*\nMM>"
    assumptions = re.search(r'Statement "' + re.escape(target) + r'" assumes the following axioms'
                            r' \(\$a statements\):\n(.*?)\nMM>', logs, re.DOTALL)
    if (not re.search(verified_label, logs, re.MULTILINE) or "No errors were found." not in logs or not assumptions):
        return check, None, build
    axioms = set() if assumptions[1].strip() == "(None)" else set(assumptions[1].split())
    return check, "accepted" if axioms.issubset(task.allowed_assumptions) else "policy_rejected", build
