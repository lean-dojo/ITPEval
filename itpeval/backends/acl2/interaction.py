"""Inspect ACL2 world events and replay native proof-builder instructions."""
from dataclasses import dataclass
from itertools import islice
import os
import re
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.projects import _declared_statement, project_file
from itpeval.core.records import Record
from itpeval.core.types import Budgets
from itpeval.runtime.interaction import _ProofSession
from itpeval.runtime.process import run_process
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import assemble, validate_inputs

from .syntax import _HEAD, _forms

_NAMES = re.compile(r"[A-Z][A-Z0-9_+*/<>=!?-]*")
_HEADER = re.compile(r"ITP_EVENT_(\d+)_(BEFORE|AFTER)\n(.*?)\nITP_END_EVENT", re.DOTALL)


def replay_events(prepared, entrypoint, names, *, budgets=None, cancel=None):
    """Reconstruct the world and return native before/after observations.

    Actions select the next named top-level event in a locked ACL2 book.
    Replaying a prefix starts again from the pinned image in a private workspace.
    """
    if prepared.spec.prover != "acl2" or prepared.spec.checking_profile != "strict":
        raise ValueError("event replay requires a strict prepared ACL2 project")
    prepared.validate()
    source = project_file(prepared.project, entrypoint)
    raw = re.sub(rb"(?im)^\s*:q[ \t]*\Z", b"", source.read_bytes().rstrip())
    steps = [name.upper() for name in names]
    commands, selected = [], []
    for start, end, form in _forms(raw):
        if len(selected) == len(steps):
            break
        m = _HEAD.match(form)
        head = m[1].decode().upper() if m else None
        if head in {"IN-PACKAGE", "INCLUDE-BOOK"}:
            if (head == "IN-PACKAGE" and m[2] != b"ACL2") or (
                    head == "INCLUDE-BOOK" and not re.search(rb":dir\s+:system\b", form, re.IGNORECASE)):
                raise ValueError("event replay supports package ACL2 and pinned system-book imports")
            commands.append(form.decode())
            continue
        if head not in {"DEFUN", "DEFUND", "DEFTHM", "DEFTHMD", "DEFCONST"} or not m[3]:
            raise ValueError(f"unsupported source form at byte {start}")
        name = m[3].decode().upper()
        i = len(selected)
        if name != steps[i] or not _NAMES.fullmatch(name):
            raise ValueError(f"expected next project event {name} at byte {start}")
        selected.append((name, head, start, end))
        commands.append(f'(cw "ITP_EVENT_{i}_BEFORE~%~x0~%ITP_FIELD~%~x1~%ITP_END_EVENT~%" '
                        f"(max-absolute-event-number (w state)) (get-event '{name} (w state)))")
        commands.append(form.decode())
        commands.append(f'(cw "ITP_EVENT_{i}_AFTER~%~x0~%ITP_FIELD~%~x1~%ITP_FIELD~%~x2~%'
                        f'ITP_FIELD~%~x3~%ITP_END_EVENT~%" (max-absolute-event-number (w state)) '
                        f"(get-event '{name} (w state)) (symbol-class '{name} (w state)) "
                        "(get-event-data 'rules state))")
    if len(selected) != len(steps):
        raise ValueError("event sequence extends beyond the checked book")
    commands += ['(cw "ITP_FINISHED_EVENTS~%")', ':q']
    budget = budgets or Budgets()
    with TemporaryDirectory() as tmp:
        root = Path(tmp)
        driver = root / "events.lsp"
        driver.write_text("\n".join(commands) + "\n")
        env = {k: os.environ[k] for k in ("HOME", "PATH", "LANG") if k in os.environ}
        check = run_process([str(prepared.prefix / "acl2/bin/acl2")], env=env, cwd=root, stdin_path=driver,
                            timeout_s=budget.timeout_s, cpu_seconds=budget.cpu_seconds,
                            memory_bytes=budget.memory_bytes, max_log_bytes=budget.max_log_bytes, cancel=cancel)
    if (check.outcome != "exited" or check.returncode or check.truncated or "ITP_FINISHED_EVENTS" not in check.stdout
            or re.search(r"ACL2 Error|\*+ FAILED \*+|HARD ACL2 ERROR", check.stdout)):
        raise ValueError(f"ACL2 event replay failed ({check.outcome}): {(check.stdout + check.stderr)[-1200:]}")
    observed = {(int(i), when): text.strip().split("\nITP_FIELD\n") for i, when, text in _HEADER.findall(check.stdout)}
    transitions = []
    for i, (name, kind, start, end) in enumerate(selected):
        before, existing = observed[i, "BEFORE"]
        after, event, symbol_class, runes = observed[i, "AFTER"]
        if existing != "NIL" or event == "NIL" or int(after) <= int(before):
            raise ValueError("native world did not admit the requested fresh event")
        transitions.append({"name": name, "kind": kind, "source_bytes": [start, end],
                            "world_before": int(before), "world_after": int(after),
                            "event_before": existing, "event_after": event,
                            "symbol_class": symbol_class, "rules": runes})
    return {"environment_id": prepared.environment_id, "entrypoint": entrypoint,
            "prover_build": prepared.spec.prover_build, "transitions": transitions}


_BUILDER_COMMANDS = frozenset(("s", "bash", "split", "demote", "promote", "top", "undo"))
_AUTOMATION_COMMANDS = ("s", "bash")
_ACTION_LIMIT = 256
_NO_GOALS = "There are no unproved goals!"
_NO_CHANGE = "*** NO CHANGE ***"
_BUILDER_PROMPT = "->: "
_BEGIN_BUILDER = "ITPEVAL_PROOF_BUILDER_BEGIN"
_END_BUILDER = "ITPEVAL_PROOF_BUILDER_END"


def _reviewed_instruction(command):
    return isinstance(command, str) and command in _BUILDER_COMMANDS


def _instruction_fragment(commands):
    return ":instructions (" + " ".join(":" + command for command in commands) + ")"


class ACL2TraceFailure(RuntimeError):
    def __init__(self, outcome, message):
        super().__init__(message)
        self.outcome = outcome


@dataclass(frozen=True)
class ProofBuilderState(Record):
    task_id: str
    environment_id: str
    source_path: str
    target: str
    command: str | None
    goals: tuple[str, ...]
    focused_term: str | None
    hypotheses: str
    complete: bool
    diagnostic: str


class ACL2ProofBuilderSession(_ProofSession):
    """Replay reviewed, argument-free native proof-builder commands.

    The builder's completed state supplies an `:instructions` fragment. The
    original task policy and native ACL2 verifier still govern final acceptance.
    """

    prover = "acl2"

    def __init__(self, task, prepared):
        super().__init__(task, prepared)
        validate_inputs(task, task.artifact)
        if prepared.spec.checking_profile != "strict":
            raise ValueError("the ACL2 proof-builder requires a strict project profile")
        self._history = []
        self._states = ()
        # Find the containing top-level theorem and replay only its fixed prefix.
        artifact = assemble(task, task.allowed_edits[0])
        slot = task.editable_regions[0]
        raw = next(file.data for file in artifact.files if file.path == slot.path)
        self._target = task.targets[0]
        for start, end, form in _forms(raw):
            if start <= slot.start < end:
                head = _HEAD.match(form)
                if (not head or head[1].lower() not in {b"defthm", b"defthmd"} or not head[3]
                        or head[3].decode().casefold() != self._target.casefold()):
                    break
                self._statement = _declared_statement("acl2", form[head.end():].decode(), "")
                if self._statement is not None:
                    self._prologue = raw[:start].decode()
                    return
                break
        raise ValueError("the ACL2 proof-builder requires a named top-level theorem")

    def reset(self):
        self._history.clear()
        self._states = ()
        return super().reset()

    def _run(self, command, root, cancel, input_file=None, *, timeout_s=None):
        self.prepared.validate()
        env = {key: os.environ[key] for key in ("HOME", "PATH", "LANG", "LC_ALL", "USER") if key in os.environ}
        env.update(self.prepared.environment)
        budgets = self.task.budgets
        result = run_process(command, cwd=root, env=env, cancel=cancel, stdin_path=input_file,
                             timeout_s=budgets.timeout_s if timeout_s is None else timeout_s,
                             memory_bytes=budgets.memory_bytes, cpu_seconds=budgets.cpu_seconds,
                             max_log_bytes=budgets.max_log_bytes)
        if result.outcome != "exited" or result.returncode or result.truncated:
            outcome = result.outcome if result.outcome != "exited" else "backend_error"
            raise ACL2TraceFailure(outcome, f"ACL2 interaction failed ({outcome}, rc={result.returncode})\n"
                                            + (result.stderr or result.stdout)[-2000:])
        return result.stdout

    def _trace(self, actions, cancel, *, timeout_s=None):
        queries = [":goals", ":p", ":hyps"]
        commands = [self._prologue, f'(cw "{_BEGIN_BUILDER}~%")',
                    f"(verify {self._statement})", *queries]
        for action in actions:
            commands.extend((f":{action}", *queries))
        commands.extend((":comm", ":exit", f'(cw "{_END_BUILDER}~%")', ":q"))
        with TemporaryDirectory(prefix="itpeval-acl2-proof-") as tmp:
            root = Path(tmp)
            source = root / "source"
            self.task.artifact.materialize(source)
            driver = root / "proof-builder.lsp"
            driver.write_text("\n".join(commands) + "\n", encoding="utf-8")
            raw = self._run([str(self.prepared.prefix / "acl2/bin/acl2")], source, cancel, driver,
                            timeout_s=timeout_s)
        _, beginning, body = raw.partition(_BEGIN_BUILDER)
        body, ending, _ = body.partition(_END_BUILDER)
        outputs = body.split(_BUILDER_PROMPT)
        if not (beginning and ending) or len(outputs) != 6 + 4 * len(actions):
            raise ACL2TraceFailure("backend_error", "ACL2 did not finish the proof-builder transaction\n" + raw[-1600:])
        states = []
        for index, action in enumerate([None, *actions]):
            start = 1 + 4 * index
            goals, term, hypotheses = map(str.strip, outputs[start:start + 3])
            complete = _NO_GOALS in goals
            states.append(ProofBuilderState(
                self.task.task_id, self.environment_id, self.task.artifact.entrypoint, self._target,
                action, () if complete else tuple(goals.splitlines()), term if not complete else None,
                hypotheses if not complete else "", complete, outputs[start - 1].strip() if index else "",
            ))
        candidate = None
        if states[-1].complete:
            # ACL2 lists the active command stack newest first. Its :instructions
            # form instead executes oldest first, excluding discarded commands.
            lines = re.findall(r"^\s*\d+\.\s+:([A-Za-z]+)\s*$", outputs[-2], re.M)
            instructions = tuple(command.lower() for command in reversed(lines))
            if not instructions or any(command not in _BUILDER_COMMANDS for command in instructions):
                raise ValueError("ACL2 returned a proof outside the supported instruction profile")
            candidate = _instruction_fragment(instructions)
        return tuple(states), candidate

    def inspect(self, handle, *, cancel=None):
        self.require(handle)
        if not self._states:
            self._states, self.candidate = self._trace(self._history, cancel)
        return self._states[-1]

    def automation_commands(self, handle):
        """Return native search commands whose full prefixes pass the task's edit policy."""
        self.require(handle)
        if self.candidate is not None or len(self._history) >= _ACTION_LIMIT:
            return ()
        return tuple(command for command in _AUTOMATION_COMMANDS
                     if permitted(self.prover, _instruction_fragment((*self._history, command)),
                                  self.task.allowed_edits, self.task.proof_atoms))

    def fork(self, handle):
        """Copy the committed command history into an independent session."""
        self.require(handle)
        child = ACL2ProofBuilderSession(self.task, self.prepared)
        child._history = self._history.copy()
        child._states, child.candidate, child.revision = self._states, self.candidate, self.revision
        return child

    def step(self, handle, instruction, *, cancel=None, timeout_s=None):
        self.require(handle)
        if not _reviewed_instruction(instruction) or len(self._history) >= _ACTION_LIMIT:
            raise ValueError("expected a supported ACL2 proof-builder instruction")
        if timeout_s is not None and not 0 < timeout_s <= self.task.budgets.timeout_s:
            raise ValueError("ACL2 trace timeout must be positive and fit the task's wall budget")
        actions = [*self._history, instruction]
        states, candidate = self._trace(actions, cancel, timeout_s=timeout_s)
        if _NO_CHANGE in states[-1].diagnostic:
            return self.handle, states[-1]
        self._history = actions
        self._states, self.candidate = states, candidate
        self.revision += 1
        return self.handle, states[-1]

    def replay_prefix(self, handle, commands, *, cancel=None):
        """Restore the initial and all committed builder states in one native run."""
        self.require(handle)
        if self._history:
            raise ValueError("ACL2 replay_prefix requires an unused proof session")
        actions = list(islice(commands, _ACTION_LIMIT + 1))
        if len(actions) > _ACTION_LIMIT or not all(map(_reviewed_instruction, actions)):
            raise ValueError("expected a bounded prefix of supported ACL2 proof-builder instructions")
        states, candidate = self._trace(actions, cancel)
        for index, state in enumerate(states[1:], 1):
            if _NO_CHANGE in state.diagnostic:
                raise ValueError(f"ACL2 instruction did not commit at replay step {index}: {state.diagnostic}")
        self._history = actions
        self._states, self.candidate = states, candidate
        self.revision = len(actions)
        return states
