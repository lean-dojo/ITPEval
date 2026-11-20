"""Compare fresh HOL4 theory builds with immutable precompiled dependencies."""
import argparse
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic

from itpeval.backends.hol4.theories import prepare_theories
from itpeval.backends.registry import ROOT
from itpeval.environments import prepare_project
from itpeval.runtime.process import run_process


def measure(prefix, cache):
    env = prepare_project("hol4", ROOT / "tests/fixtures/projects/hol4/library", prefix=prefix, cache=cache)
    deps = ("baseScript.sml", "refuteUnusedScript.sml")
    start = monotonic()
    build = prepare_theories(env, deps)
    preparation = monotonic() - start
    assert prepare_theories(env, deps).cache_hit
    good = (env.project / "sampleScript.sml").read_text()
    cases = (("valid", good, True), ("invalid", good.replace("simp[twice_def]", "NO_TAC"), False),
             ("valid_again", good, True))
    output = []
    for label, text, expected in cases:
        for cached in (False, True):
            with TemporaryDirectory() as tmp:
                root = Path(tmp) / "attempt"
                root.mkdir()
                flags = build.stage(env, tmp) if cached else []
                if not cached:
                    for name in deps:
                        (root / name).write_bytes((env.project / name).read_bytes())
                (root / "sampleScript.sml").write_text(text)
                result = run_process([str(env.prefix / "hol4/bin/Holmake"), *flags, "sampleTheory.uo"],
                                     cwd=root, timeout_s=120)
                success = result.returncode == 0 and (root/".hol/objs/sampleTheory.uo").exists()
                if (result.outcome != "exited" or success is not expected
                        or (not expected and 'Tactic failure proving "twice_zero"' not in result.stdout + result.stderr)):
                    raise RuntimeError(f"{label}: {result.stdout[-1300:]} {result.stderr[-1300:]}")
                output.append({"case": label, "precompiled_dependencies": cached, "success": success,
                               "native_ms": result.duration_ms, "cpu_s": result.cpu_time_s,
                               "peak_process_rss_bytes": result.peak_process_rss_bytes})
                build.validate(env)
    return {"environment_id": env.environment_id, "prover_build": env.spec.prover_build,
            "dependency_content_id": build.content_id, "dependencies": list(deps),
            "first_prepare_cache_hit": build.cache_hit, "preparation_s": preparation,
            "dependency_hashes_unchanged": True, "samples": output}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("prefix", "cache", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(json.dumps(measure(args.prefix, args.cache), indent=2) + "\n")
