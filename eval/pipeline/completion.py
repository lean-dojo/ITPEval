"""Run generation and verification for one constrained task in a prepared environment."""

from __future__ import annotations

import argparse
from pathlib import Path

from eval.pipeline.jsonl import load_jsonl, result_writer, write_jsonl_atomic
from eval.pipeline.models import select_models
from eval.pipeline.task_profile import TaskProfile, completion_record, completion_request
from eval.pipeline.translate import translate
from eval.pipeline.verify import failed_verification, verify_translation_record
from itpeval.core.records import digest


def run(profile: TaskProfile, model: dict, output: Path, *, prerecorded: str | None = None,
        generate_only: bool = False) -> dict:
    profile.validate()
    request = completion_request(profile)
    source = "model_provider" if prerecorded is None else digest(prerecorded)
    manifest = profile.manifest(source, {**model, "max_tokens": 16000, "temperature": 0.0,
                                         "generate_only": generate_only})
    with result_writer(output):
        manifest.bind(output)
        prior = load_jsonl(output)
        if prior:
            if len(prior) != 1 or prior[0].get("run_id") != manifest.run_id:
                raise ValueError("result does not match its run manifest")
            return prior[0]

        candidate = prerecorded
        error = ""
        if candidate is None:
            try:
                candidate = translate(system_prompt=request["system_prompt"], user_prompt=request["user_prompt"],
                                      model_cfg=model, max_tokens=16000, temperature=0.0)
            except Exception as exc:
                candidate, error = "", f"{type(exc).__name__}: {exc}"
        generated = completion_record(request, model, candidate)
        if error:
            generated["translate_error"] = error
        record = generated
        if not generate_only:
            try:
                record = verify_translation_record(generated, profile=profile)
            except Exception as exc:
                record = failed_verification(generated, exc, profile)
        record["run_id"] = manifest.run_id
        write_jsonl_atomic(output, [record])
        return record


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lock", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--generate-only", action="store_true", help="write the generated response for post-hoc verification")
    parser.add_argument("--task-manifest", default="completion.json", help="reviewed project-relative task manifest")
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--model", help="one model label from the benchmark configuration")
    inputs.add_argument("--candidate", type=Path, help="file with the exact prerecorded proof edit")
    args = parser.parse_args(argv)
    if args.model:
        models = select_models(args.model)
        if len(models) != 1:
            parser.error("select one model")
        model = models[0]
        candidate = None
    else:
        model = {"label": "prerecorded", "id": "prerecorded", "provider": "local"}
        candidate = args.candidate.read_bytes().decode("utf-8")
    result = run(TaskProfile.from_lock(args.lock, args.task_manifest), model, args.output, prerecorded=candidate,
                 generate_only=args.generate_only)
    print(f"{result['custom_id']} " + ("generated" if args.generate_only else f"task_success={result['task_success']}"))


if __name__ == "__main__":
    main()
