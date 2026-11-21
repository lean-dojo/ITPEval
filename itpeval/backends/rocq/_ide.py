"""Supervised RocqIDE transaction using the installed compiler's parser."""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
import xml.etree.ElementTree as ET

# The supervised process starts in a private project directory. Locate this
# installation when the caller is using ITPEval directly from a checkout.
if not __package__:
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from itpeval.extraction.native.rocq import call, elem


def _add(proc, parser, state, command, start, line, bol):
    command = elem("pair", elem("string", text=command), elem("int", text="0"))
    parent = elem("pair", elem("state_id", val=state), elem("bool", val="false"))
    body = elem("pair", elem("pair", command, parent), elem("int", text=str(start)))
    location = elem("pair", elem("int", text=str(line)), elem("int", text=str(bol)))
    response = call(proc, parser, "Add", elem("pair", body, location))
    return response.find("./pair/state_id").get("val")


def _observe(proc, parser, action):
    goals = call(proc, parser, "Goal", elem("unit")).find("./option/goals")
    groups = ("focused", "background", "shelved", "given_up")
    if goals is not None and len(goals) != len(groups):
        raise ValueError("unknown RocqIDE goal layout")
    pending = any(len(group) for group in goals) if goals is not None else True
    return {"command": action, "complete": not pending,
            "goals": None if goals is None else
            {key: ET.tostring(group, encoding="unicode") for key, group in zip(groups, goals)},
            "error": None}


def run(request):
    src = request["entrypoint"]
    raw = Path(src).read_bytes()
    flags = request["flags"]
    slot = request["slot"]
    spans = request["spans"]
    if not spans:
        timing = request["timing"]
        process = subprocess.run([request["rocq"], "compile", "-time-file", timing, *flags, src],
                                 capture_output=True, text=True)
        # Compilation can fail after the slot. The native parser positions of
        # earlier successful commands still identify the original proof state.
        if not Path(timing).is_file():
            raise ValueError("Rocq did not emit parser positions: " + process.stderr[-1600:])
        before = [(int(lo), int(hi)) for lo, hi in re.findall(
            r"^Chars (\d+) - (\d+) ", Path(timing).read_text(), re.M) if int(hi) <= slot]
        if not before or raw[before[-1][1]:slot].strip():
            raise ValueError("Rocq parser positions do not reach the prepared proof slot")
        spans = before
    parser = ET.XMLPullParser(["end"])
    parser.feed('<!DOCTYPE protocol [<!ENTITY nbsp "&#32;">]><protocol>')
    with subprocess.Popen([request["ide"], "-main-channel", "stdfds", "-async-proofs", "off",
                           "-topfile", src, *flags], stdin=subprocess.PIPE, stdout=subprocess.PIPE) as proc:
        try:
            state = call(proc, parser, "Init", elem("option", val="none")).find("state_id").get("val")
            for start, stop in spans:
                state = _add(proc, parser, state, raw[start:stop].decode(),
                             start, raw[:start].count(b"\n") + 1, raw.rfind(b"\n", 0, start) + 1)
            observed = _observe(proc, parser, None)
            if observed["goals"] is None or observed["complete"]:
                raise ValueError("Rocq did not find an open proof at the prepared slot")
            responses = [observed]
            source = raw[:slot]
            for action in request["actions"]:
                try:
                    state = _add(proc, parser, state, action, len(source),
                                 source.count(b"\n") + 1, source.rfind(b"\n") + 1)
                    responses.append(_observe(proc, parser, action))
                except ValueError as error:
                    # A failed Add does not count as a successful proof step.
                    responses.append({**responses[-1], "command": action, "error": str(error)})
                    break
                source += action.encode() + b"\n"
            call(proc, parser, "Quit", elem("unit"))
            return {"spans": spans, "observations": responses}
        finally:
            proc.stdin.close()
            if proc.poll() is None:
                proc.terminate()


if __name__ == "__main__":
    print(json.dumps(run(json.loads(Path(sys.argv[1]).read_bytes())), ensure_ascii=False))
