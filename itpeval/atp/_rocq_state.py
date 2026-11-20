"""Read one native RocqIDE state with a private Ltac2 observer."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
import xml.etree.ElementTree as ET

if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from itpeval.backends.rocq._ide import _add, _observe
from itpeval.extraction.native.rocq import call, elem


_MARKER = "ITPEVAL_ROCQ_HORN "


class _Reader:
    def __init__(self):
        self.parser = ET.XMLPullParser(["end"])
        self.parser.feed('<!DOCTYPE protocol [<!ENTITY nbsp "&#32;">]><protocol>')
        self.messages = []

    def feed(self, data):
        self.parser.feed(data)

    def read_events(self):
        for event, node in self.parser.read_events():
            if node.tag == "feedback":
                content = node.find("feedback_content[@val='message']/message/richpp")
                state = node.find("state_id")
                if content is not None and state is not None:
                    notice = "".join(content.itertext())
                    if notice.startswith(_MARKER):
                        self.messages.append((state.get("val"), notice[len(_MARKER):]))
            yield event, node


def _compile(argv, diagnostic: Path):
    # Compilation may fail at the open proof. The caller checks its parser
    # positions independently, without buffering all native diagnostics.
    with diagnostic.open("wb") as errors:
        return subprocess.run(argv, stdout=subprocess.DEVNULL, stderr=errors, check=False).returncode


def _diagnostic(path: Path) -> str:
    with path.open("rb") as errors:
        errors.seek(max(path.stat().st_size - 1600, 0))
        return errors.read().decode(errors="replace").strip()


def _native_prefix(request, raw: bytes):
    timing = Path(request["timing"])
    diagnostic = timing.with_suffix(".stderr")
    _compile([request["rocq"], "compile", "-time-file", str(timing), *request["flags"], request["entrypoint"]],
             diagnostic)
    if not timing.is_file():
        raise ValueError("Rocq did not report parser positions: " + _diagnostic(diagnostic))
    slot = request["slot"]
    spans = [(int(lo), int(hi)) for lo, hi in re.findall(r"^Chars (\d+) - (\d+) ", timing.read_text(), re.M)]
    commands = [(lo, hi) for lo, hi in spans if hi <= slot]
    marker = (slot, slot + len(b"idtac."))
    if not commands or (raw[commands[-1][1]:slot].strip() and marker not in spans):
        raise ValueError("Rocq parser positions do not reach the prepared proof slot")
    return commands


def _protocol(request, raw, commands):
    entry = request["entrypoint"]
    slot = request["slot"]
    namespace = request["namespace"]
    probe = Path(request["probe"])
    probe_flags = ["-Q", str(probe.parent), namespace]
    diagnostic = probe.with_suffix(".stderr")
    if _compile([request["rocq"], "compile", *probe_flags, str(probe)], diagnostic):
        raise ValueError("Rocq could not compile the Ltac2 observer: " + _diagnostic(diagnostic))

    reader = _Reader()
    with subprocess.Popen([request["ide"], "-main-channel", "stdfds", "-async-proofs", "off", "-topfile", entry,
                           *request["flags"], *probe_flags], stdin=subprocess.PIPE, stdout=subprocess.PIPE) as proc:
        try:
            state = call(proc, reader, "Init", elem("option", val="none")).find("state_id").get("val")
            state = _add(proc, reader, state, f"From {namespace} Require HornProbe.", 0, 1, 0)
            for start, stop in commands:
                state = _add(proc, reader, state, raw[start:stop].decode(), start,
                             raw[:start].count(b"\n") + 1, raw.rfind(b"\n", 0, start) + 1)
            cursor = slot
            line = raw[:slot].count(b"\n") + 1
            beginning = raw.rfind(b"\n", 0, slot) + 1
            for command in request.get("prefix", ()):
                state = _add(proc, reader, state, command, cursor, line, beginning)
                cursor += len(command.encode()) + 1
                line += command.count("\n") + 1
                beginning = cursor
            observation = _observe(proc, reader, None)
            groups = observation["goals"]
            if groups is None or observation["complete"]:
                return {"reason": "no_open_goal"}
            focused = ET.fromstring(groups["focused"])
            background = ET.fromstring(groups["background"])
            if (len(focused) != 1 or any(len(branch) for frame in background for branch in frame)
                    or any(len(ET.fromstring(groups[group])) for group in ("shelved", "given_up"))):
                return {"reason": "multiple_or_unfocused_goals", "focused_goals": len(focused)}

            reader.messages.clear()
            action = f"ltac2:({namespace}.HornProbe.observe ())."
            observed_state = _add(proc, reader, state, action, cursor, line, beginning)
            _observe(proc, reader, action)
            call(proc, reader, "Quit", elem("unit"))
            messages = [notice for state_id, notice in reader.messages if state_id == observed_state]
        finally:
            proc.stdin.close()
            if proc.poll() is None:
                proc.terminate()
    return {"messages": messages, "focused_goals": 1}


def run(request):
    raw = Path(request["entrypoint"]).read_bytes()
    return _protocol(request, raw, _native_prefix(request, raw))


if __name__ == "__main__":
    try:
        print(json.dumps(run(json.loads(Path(sys.argv[1]).read_bytes())), ensure_ascii=False))
    except (OSError, ValueError) as error:
        sys.exit(str(error))
