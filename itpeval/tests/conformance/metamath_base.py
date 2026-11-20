"""Compare fresh and verified-base checking of a compressed, disjoint-variable proof."""
import json
import shutil
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import CompletionManifest, build_task
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.verification.service import verify


def project(root):
    source = ROOT / "tests/fixtures/projects/metamath/library"
    shutil.copytree(source, root)
    stmt = "pair-rule $p |- pair x y $= ( pair-dv ) ABC $."
    manifest = CompletionManifest("client.mm", ("base.mm", "set-a1i.mm", "client.mm"), stmt, "pair-rule",
                                  "|- pair x y", "( pair-dv ) ABC",
                                  ("( pair-dv ) ABC", "( pair-dv ) ABA", "vx vy pair-dv"),
                                  allowed_assumptions=("pair-dv",))
    (root / "completion.json").write_text(json.dumps(manifest.to_dict(), sort_keys=True))


def measure(prefix, cache):
    with TemporaryDirectory() as tmp:
        root = Path(tmp) / "project"
        project(root)
        env = prepare_project("metamath", root, prefix=prefix, cache=cache, project_name="itpeval/verified-mm-base")
        return check_prepared(env)


def check_prepared(env):
    task = build_task(env)
    checks = []
    for candidate, expected in zip(task.allowed_edits, (True, False, True)):
        checked = verify(task, candidate, prepared=env)
        partial = verify(task, candidate, prepared=env, metamath_base="base.mm")
        if (checked.task_success is not expected or partial.task_success is not expected
                or checked.checker_outcome != partial.checker_outcome):
            raise ValueError(str((checked.to_dict(), partial.to_dict()))[-2300:])
        checks.append({"candidate": candidate, "fresh": checked.to_dict(), "with_base": partial.to_dict()})
    from itpeval.backends.metamath.base import prepare_base
    base = prepare_base(env, "base.mm")
    return {"environment_id": env.environment_id, "prover_build": env.spec.prover_build,
            "base": json.loads(base.receipt_path.read_text()), "base_id": base.base_id,
            "task": task.to_dict(), "checks": checks}
