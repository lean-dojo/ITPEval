"""Native adapter registry and reviewed single-slot proof tasks."""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, replace
from functools import lru_cache
from importlib import import_module
from pathlib import Path

from itpeval.backends.external import external_adapter, external_adapter_ids
from itpeval.core.capabilities import Capability
from itpeval.core.types import Artifact, Budgets, EditableRegion, TaskSpec

ROOT = Path(__file__).resolve().parents[1]

_NATIVE_SESSIONS = {
    "acl2": ("itpeval.backends.acl2.interaction", "ACL2ProofBuilderSession"),
    "agda": ("itpeval.runtime.interaction", "AgdaHoleSession"),
    "hol-light": ("itpeval.backends.hol_tactics", "HOLProofSession"),
    "hol4": ("itpeval.backends.hol_tactics", "HOLProofSession"),
    "isabelle": ("itpeval.backends.isabelle.interaction", "IsabelleProofSession"),
    "lean4": ("itpeval.runtime.interaction", "LeanTacticSession"),
    "metamath": ("itpeval.backends.metamath.interaction", "MetamathProofSession"),
    "mizar": ("itpeval.backends.mizar.interaction", "MizarArticleSession"),
    "pvs": ("itpeval.backends.pvs.interaction", "PVSProofSession"),
    "rocq": ("itpeval.backends.rocq.interaction", "RocqIDESession"),
}


@lru_cache(maxsize=1)
def _manifest() -> dict:
    return json.loads(Path(__file__).with_name("tasks.json").read_text(encoding="utf-8"))


def prover_ids() -> tuple[str, ...]:
    return tuple(_manifest())


def project_prover_ids() -> tuple[str, ...]:
    """Return built-in IDs and the explicitly configured typed adapter IDs."""
    return (*prover_ids(), *(prover for prover in external_adapter_ids() if prover not in _manifest()))


def curated_project(prover: str) -> Path:
    if prover not in _manifest():
        raise ValueError(f"unknown prover {prover!r}")
    return ROOT / "tests" / "fixtures" / "projects" / prover / "completion"


def curated_task(prover: str, environment_id: str) -> TaskSpec:
    project = curated_project(prover)
    data = _manifest()[prover]
    entry = data["entrypoint"]
    files = {name: (project / name).read_bytes() for name in data["files"]}
    source, slot = files[entry], data["slot"].encode()
    if source.count(slot) != 1:
        raise ValueError(f"ambiguous or absent curated proof slot in {prover}")
    start = source.index(slot)
    # Redact the reference completion; the task keeps a byte-range insertion point.
    files[entry] = source[:start] + source[start + len(slot):]
    artifact = Artifact.from_files(entry, files, ("removed reference proof fragment",))
    return TaskSpec(prover, environment_id, "proof_completion", artifact,
                    targets=(data["target"],), editable_regions=(EditableRegion(entry, start, start),),
                    allowed_assumptions=tuple(data["assumptions"]),
                    allowed_edits=tuple(data["allowed_edits"]), obligations=tuple(data["obligations"]),
                    proof_atoms=tuple(data.get("atoms", ())), native_receipt=data["receipt"],
                    budgets=Budgets.from_dict(data["budgets"]) if "budgets" in data else Budgets())


def receipt(prover: str) -> str | None:
    return _manifest()[prover]["receipt"]


@dataclass(frozen=True)
class NativeBackend:
    prover: str

    def curated_task(self, environment_id: str) -> TaskSpec:
        return curated_task(self.prover, environment_id)

    def _require_project(self, prepared):
        if self.prover != prepared.spec.prover:
            raise ValueError("project belongs to another backend")

    def build_task(self, prepared, manifest_path: str = "completion.json") -> TaskSpec:
        from .projects import build_task
        self._require_project(prepared)
        return build_task(prepared, manifest_path)

    def inspect_declarations(self, prepared, entrypoint: str, destination: Path, *, timeout_s: float = 180,
                             context_storage="expanded"):
        from itpeval.extraction import extract_project
        self._require_project(prepared)
        return extract_project(prepared, entrypoint, destination, timeout_s=timeout_s, context_storage=context_storage)

    def open_document(self, task: TaskSpec, *, prepared):
        from itpeval.runtime.sessions import DocumentSession
        self._require_project(prepared)
        if task.prover != self.prover:
            raise ValueError("task belongs to another backend")
        return DocumentSession(task, prepared)

    def open_native_session(self, task: TaskSpec, *, prepared, **options):
        """Open the prover's native session for a supported, reviewed task."""
        self._require_project(prepared)
        if task.prover != self.prover:
            raise ValueError("task belongs to another backend")
        if self.prover not in _NATIVE_SESSIONS:
            raise NotImplementedError(f"{self.prover} uses the document session for proof tasks")
        module, name = _NATIVE_SESSIONS[self.prover]
        return getattr(import_module(module), name)(task, prepared, **options)

    def check(self, task: TaskSpec, candidate: str | None = None, *, prepared, **options):
        from itpeval.verification.service import verify
        if task.prover != self.prover:
            raise ValueError("task belongs to another backend")
        return verify(task, candidate, prepared=prepared, **options)

    def check_document(self, task: TaskSpec, document: Artifact | str | bytes, *, prepared, **options):
        from itpeval.verification import verify_document
        if task.prover != self.prover:
            raise ValueError("task belongs to another backend")
        return verify_document(task, document, prepared=prepared, **options)

    def capabilities(self, *, prepared=None, qualification_report=None) -> tuple[Capability, ...]:
        from itpeval.extraction import ADAPTERS

        if prepared is not None:
            self._require_project(prepared)
        if self.prover not in _manifest():
            adapter = prepared.adapter if prepared is not None else external_adapter(self.prover)
            if adapter is None:
                raise ValueError(f"no typed adapter configured for {self.prover!r}")
            registered = (
                Capability("proof_completion", "experimental", "Fixed target and a detached certificate file"),
                Capability("edit_document", "experimental", "Resubmit the detached certificate"),
                Capability("reset", "experimental", "Discard certificate revisions"),
                Capability("fork_document", "experimental", "Copy the current certificate to an independent session"),
                Capability("checkpoint_document", "experimental", "Serialize the certificate and replay under the same lock",
                           survives_restart=True, portable_between_workers=True),
                Capability("inspect_declarations", "experimental" if adapter.extractor is not None else "inapplicable",
                           "Read declaration events from the configured adapter"),
            )
            return self._qualify(registered, prepared, qualification_report)
        registered = (
            Capability("check_artifact", "experimental", "Fresh process and byte-exact inputs"),
            Capability("proof_completion", "experimental", "Project manifest or curated proof slot with reviewed fragments and supported compositions"),
            Capability("edit_document", "experimental", "Resubmit a fragment in a fresh workspace"),
            Capability("reset", "experimental", "Discard revisions and invalidate ephemeral handles"),
            Capability("fork_document", "experimental", "Copy a document revision into an independent session"),
            Capability("checkpoint_document", "experimental", "Serialize the candidate and replay it under the same lock",
                       survives_restart=True, portable_between_workers=True),
            Capability("checkpoint_actions", "experimental", "Replay saved native actions and compare goal revisions",
                       survives_restart=True, portable_between_workers=True),
            Capability("inspect_declarations", "experimental" if self.prover in ADAPTERS
                       else "planned", "See extraction report for field availability"),
            Capability("step_proof", "experimental" if self.prover in {
                "lean4", "pvs", "hol4", "hol-light", "rocq", "isabelle", "acl2", "metamath",
            } else "planned", "Elaborated state feedback in an isolated native transaction"),
            Capability("inspect_goals", "experimental",
                       "Theses from verification of a supplied Mizar article" if self.prover == "mizar"
                       else "Goals or sequents observed through the backend's native interface"),
            Capability("refine_hole", "experimental" if self.prover == "agda" else "planned",
                       "Agda Cmd_give against a typed interaction point"),
            Capability("case_split", "experimental" if self.prover == "agda" else "planned",
                       "Native Agda case-split proposal; fixed binders remain immutable"),
            Capability("proof_branching", "experimental" if self.prover in {
                "lean4", "rocq", "isabelle", "hol4", "hol-light", "pvs",
            } else "planned", "Replay a native THENL tactic tree and edit one pending branch" if self.prover in {"hol4", "hol-light"}
                       else "Replay and fork the ordered native command prefix" if self.prover == "pvs"
                       else "Native prover state IDs are local to one isolated invocation"),
            Capability("checkpoint_proof", "experimental" if self.prover in {"hol4", "hol-light", "pvs"} else "planned",
                       "Replay the saved proof commands under the same locked task" if self.prover == "pvs"
                       else "Replay the serialized tactic tree under the same locked task",
                       survives_restart=True, portable_between_workers=True),
            Capability("warm_proof_session", "experimental" if self.prover == "hol-light" else "planned",
                       "Run native goal observations in isolated children of a preloaded HOL core"),
            Capability("automated_search", "experimental", {
                "acl2": "Search with reviewed proof-builder simplification and case analysis",
                "agda": "Ask Auto for a term, or reconstruct one using local premises selected by E or Vampire",
                "hol4": "Search a selected native subgoal with Metis, E, or Vampire",
                "hol-light": "Search a selected native subgoal with MESON",
                "isabelle": "Ask Sledgehammer about the initial goal and replay a recovered proof",
                "lean4": "Observe a native goal or supply a ground Horn map, then replay a proof",
                "metamath": "Search reviewed labels for the pending Proof Assistant steps",
                "mizar": "Try reviewed article justifications on the locked proposition",
                "pvs": "Try a reviewed strategy on the focused sequent, with optional Horn search by E or Vampire",
                "rocq": "Observe a native goal or supply a ground Horn map, then replay a proof",
            }[self.prover]),
            Capability("atp_from_state", "experimental",
                       "Search and apply a result at the saved goal or subgoal revision"),
            Capability("external_atp_goal", "experimental" if self.prover in {
                "agda", "hol4", "isabelle", "lean4", "pvs", "rocq",
            } else "planned",
                       "Run E or Vampire on a supported native goal and check a native proof"),
            Capability("proof_portfolio", "experimental",
                       "Explore alternate native actions and ATP trials from saved proof states, then replay the winning branch",
                       survives_restart=True, portable_between_workers=True),
            Capability("action_traces", "experimental" if self.prover in {"lean4", "metamath", "mizar", "pvs"} else "planned",
                       "Native proof or checking transitions with source context where available"),
            Capability("replay_stack", "experimental" if self.prover == "metamath" else "inapplicable",
                       "Step through reconstructed transitions from a natively verified proof"),
            Capability("verify_base_database", "experimental" if self.prover == "metamath" else "inapplicable",
                       "Reuse full native verification of a fixed include closure while checking the new target"),
            Capability("replay_event", "experimental" if self.prover == "acl2" else "inapplicable",
                       "Reconstruct an ordered prefix of named book events and observe each native world change"),
            Capability("article_errors", "experimental" if self.prover == "mizar" else "inapplicable",
                       "Native Mizar article path, line, column and verifier error number"),
            Capability("snapshot", "planned", "No process snapshot is available"),
        )

        if prepared is not None:
            tools = dict(prepared.extra_inputs)
            stock_isabelle_tools = True
            if self.prover == "lean4":
                required = {"proof_branching": ("pantograph",), "action_traces": ("leandojo_tracer",)}
            elif self.prover == "rocq":
                required = {"proof_branching": ("petanque", "petanque_runtime")}
            elif self.prover == "isabelle":
                tools_for_branching = ("isa_repl", "auto_sledgehammer")
                required = {"proof_branching": tools_for_branching}
                # process_theories entered the distributions in Isabelle2025-1.
                release = re.match(r"Isabelle(\d{4})(?:-(\d+))?\b", prepared.spec.prover_build)
                if release and (int(release[1]), int(release[2] or 0)) < (2025, 1):
                    stock_isabelle_tools = False
                    required.update(dict.fromkeys(("step_proof", "inspect_goals"), tools_for_branching))
            else:
                required = {}
            def resolve(capability):
                if not stock_isabelle_tools and capability.operation in {"automated_search", "atp_from_state", "external_atp_goal"}:
                    return replace(capability, status="inapplicable", semantics="Requires Isabelle process_theories")
                if self.prover == "hol-light" and capability.operation == "warm_proof_session":
                    from itpeval.backends.hol_light.worker import ForkedHOLLight
                    if not ForkedHOLLight.supports_project(prepared):
                        return replace(capability, status="inapplicable", semantics="Requires a reviewed warm-worker project")
                missing = [r for r in required.get(capability.operation, ()) if "external/" + r not in tools]
                if missing:
                    return replace(capability, status="inapplicable",
                                   semantics="This environment requires locked " + ", ".join(missing))
                return capability
            registered = tuple(resolve(c) for c in registered)
        return self._qualify(registered, prepared, qualification_report)

    def _qualify(self, registered, prepared, qualification_report):
        if qualification_report is None:
            return registered
        if prepared is None or prepared.spec.prover != self.prover:
            raise ValueError("qualification lookup requires a matching prepared environment")
        prepared.validate()
        tested = set()
        with Path(qualification_report).open(encoding="utf-8") as rows:
            for line in rows:
                if not line.strip():
                    continue
                row = json.loads(line)
                if (row["prover"] == self.prover and row["environment_id"] == prepared.environment_id
                        and row["prover_build"] == prepared.spec.prover_build
                        and row["status"] == "implemented/tested"):
                    tested.add(row["operation"])
        return tuple(replace(c, status="implemented/tested") if c.operation in tested and c.status == "experimental"
                     else c for c in registered)


def get_backend(prover: str) -> NativeBackend:
    if prover not in _manifest() and external_adapter(prover) is None:
        raise ValueError(f"unknown prover {prover!r}")
    return NativeBackend(prover)

def require_capabilities(prover: str, required, *, allow_experimental=True, prepared=None,
                         qualification_report=None) -> tuple[Capability, ...]:
    """Resolve a search algorithm's required operations before it opens a session."""
    available = {c.operation: c for c in get_backend(prover).capabilities(
        prepared=prepared, qualification_report=qualification_report)}
    statuses = {"implemented/tested", "tested"}
    if allow_experimental:
        statuses.add("experimental")
    selected = []
    for operation in required:
        capability = available.get(operation)
        if capability is None or capability.status not in statuses:
            raise NotImplementedError(f"{prover}: required operation {operation!r} is unavailable")
        selected.append(capability)
    return tuple(selected)
