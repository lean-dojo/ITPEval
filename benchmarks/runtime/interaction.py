"""Run native goal, typed-hole and verified-stack conformance."""
import argparse
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import build_task
from itpeval.backends.registry import ROOT, curated_project, require_capabilities
from itpeval.environments import prepare_project
from itpeval.extraction import extract_project
from itpeval.learning.qualification import _record
from itpeval.runtime.interaction import AgdaHoleSession, LeanTacticSession, MetamathStackReplay


def probe(prover, prefix, cache):
    if prover == "metamath":
        from itpeval.tests.conformance.metamath_base import project as base_project
        with TemporaryDirectory() as tmp:
            project = Path(tmp) / "project"
            base_project(project)
            env = prepare_project(prover, project, prefix=prefix, cache=cache, project_name="itpeval/verified-mm-base")
    else:
        project = curated_project(prover)
        if prover in {"acl2", "agda"}:
            project = ROOT / "tests/fixtures/projects" / prover / ("library" if prover == "acl2" else "interaction")
        extra = {}
        if prover == "rocq":
            aux = prefix / "auxiliary/rocq"
            extra = {"petanque": aux / "pet", "petanque_runtime": aux / "lib"}
        env = prepare_project(prover, project, prefix=prefix, cache=cache, toolchain_inputs=extra)
    detail = {}
    if prover == "acl2":
        from itpeval.backends.acl2.interaction import replay_events
        require_capabilities(prover, ("replay_event",), prepared=env)
        names = ["MY-ID", "GUARDED-ID", "MY-ID-ID"]
        trace = replay_events(env, "events.lisp", names)
        replay = replay_events(env, "events.lisp", names[:1])
        states = trace["transitions"]
        passed = (replay["transitions"] == states[:1] and [s["name"] for s in states] == names
                  and states[1]["symbol_class"] == ":COMMON-LISP-COMPLIANT"
                  and ":DEFINITION MY-ID" in states[2]["rules"])
        return env, {"replay_event": passed}, {"trace": trace, "fresh_replay": replay}
    if prover == "mizar":
        from itpeval.backends.mizar.diagnostics import article_errors
        from itpeval.verification.service import verify
        require_capabilities(prover, ("article_errors",), prepared=env)
        task = build_task(env)
        result = verify(task, task.allowed_edits[1], prepared=env)
        errors = article_errors(task, result)
        passed = result.task_success is False and any(e["line"] > 0 and e["error_code"] > 0 for e in errors)
        return env, {"article_errors": passed}, {"errors": errors, "evidence": result.to_dict()}
    if prover == "rocq":
        from itpeval.backends.rocq.interaction import command_trace
        require_capabilities(prover, ("inspect_goals", "step_proof", "proof_branching"), prepared=env)
        task = build_task(env)
        detail = command_trace(task, ["intro p.", "exact p.", (1, "assumption."), (0, "exact I.")], prepared=env)
        states = detail["states"]
        observed = bool(states[0].get("goals", {}).get("goals"))
        solved = len(states) == 5 and all(states[i].get("native", {}).get("proof_finished") for i in (2, 3))
        passed = solved and bool(states[-1].get("error"))
        return env, {"step_proof": passed, "inspect_goals": observed, "proof_branching": solved}, detail
    if prover in {"hol4", "hol-light", "pvs"}:
        require_capabilities(prover, ("step_proof", "inspect_goals"), prepared=env)
        task = build_task(env)
        if prover == "pvs":
            from itpeval.backends.pvs.interaction import command_trace
            states = command_trace(task, ["(grind)"], prepared=env)
            detail["states"] = states
            passed = states[-1]["status"] == "proved"
            observed = states[0]["status"] == "init" and bool(states[0]["states"])
        else:
            from itpeval.backends.hol_tactics import tactic_trace
            solving = "ITAUT_TAC" if prover == "hol-light" else "PROVE_TAC []"
            trace = tactic_trace(task, ["ALL_TAC", solving], prepared=env)
            detail["trace"] = trace
            calls = trace["invocations"]
            passed = trace["status"] == "returned" and len(calls) == 2 and not calls[-1]["subgoals"]
            observed = bool(calls and calls[0]["goal"] and calls[0]["subgoals"])
        return env, {"step_proof": passed, "inspect_goals": observed}, detail
    if prover == "metamath":
        require_capabilities(prover, ("replay_stack",))
        bundle = extract_project(env, "client.mm", Path(cache) / "metamath-replays")
        decls = [json.loads(line) for line in (bundle.path / "declarations.jsonl").read_text().splitlines()]
        target = next(d for d in decls if d["name"] == "pair-rule")
        s = MetamathStackReplay(env, bundle.path, target["declaration_id"])
        handle = s.handle
        transitions = []
        for _ in s.transitions:
            handle, item = s.step(handle)
            transitions.append(item)
        detail.update(declaration_id=target["declaration_id"], transitions=transitions)
        passed = bool(transitions) and transitions[-1]["height_after"] == 1
        from itpeval.tests.conformance.metamath_base import check_prepared
        detail["verified_base"] = check_prepared(env)
        checks = detail["verified_base"]["checks"]
        operations = {"replay_stack": passed, "action_traces": passed and len(transitions) == 3,
                      "verify_base_database": all(c["fresh"]["task_success"] == c["with_base"]["task_success"]
                                                  for c in checks) and "base_verification_cache_hit" in
                                              checks[-1]["with_base"]["evidence_references"]}
    elif prover == "lean4":
        require_capabilities(prover, ("step_proof", "inspect_goals"))
        s = LeanTacticSession(build_task(env), env)
        handle, detail["transaction"] = s.step(s.handle, "rfl")
        before, after = (detail["transaction"][k] for k in ("before", "after"))
        final = s.finalize(handle)
        detail["final"] = final.to_dict()
        operations = {"step_proof": final.task_success is True and not after["goal"]["goals"],
                      "inspect_goals": any("⊢ x = x" in goal for goal in before["goal"]["goals"])}
    else:
        require_capabilities(prover, ("refine_hole", "case_split", "inspect_goals"))
        s = AgdaHoleSession(build_task(env), env)
        initial = s.inspect(s.handle)
        detail["initial_goals"] = [event["info"] for event in initial
                                   if event.get("info", {}).get("kind") == "AllGoalsWarnings"]
        detail["clauses"] = s.case_split(s.handle, "x")
        handle, refresh = s.give(s.handle, "x")
        detail["native_goal_updates"] = [e for e in refresh if e["kind"] in {"GiveAction","InteractionPoints"}]
        final = s.finalize(handle)
        detail["final"] = final.to_dict()
        operations = {"refine_hole": final.task_success is True and any(e["kind"] == "GiveAction" for e in refresh),
                      "case_split": detail["clauses"] == ["ident false = ?", "ident true = ?"],
                      "inspect_goals": any(g["visibleGoals"] for g in detail["initial_goals"])}
    old = s.handle
    s.reset()
    try:
        s.require(old)
        raise AssertionError("reset failed to invalidate the native state handle")
    except ValueError:
        pass
    return env, operations, detail


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    native = ("lean4", "agda", "metamath", "pvs", "hol4", "hol-light", "rocq", "mizar", "acl2")
    parser.add_argument("--prover", action="append", choices=native)
    args = parser.parse_args()
    passed = True
    for prover in args.prover or native:
        env, operations, details = probe(prover, args.prefix, args.cache)
        output = args.output / prover / "native-interaction.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps({"prover": prover, "environment_id": env.environment_id,
                                     "prover_build": env.spec.prover_build, "operations": operations,
                                     "native": details}, ensure_ascii=False, indent=2) + "\n")
        if args.report is not None:
            _record(args.report, [{"prover": prover, "operation": name, "environment_id": env.environment_id,
                                  "prover_build": env.spec.prover_build, "status": "implemented/tested" if ok else "failed",
                                  "evidence_path": str(output.relative_to(args.report.parent))}
                                 for name, ok in operations.items()])
        passed = passed and all(operations.values())
    raise SystemExit(0 if passed else 1)
