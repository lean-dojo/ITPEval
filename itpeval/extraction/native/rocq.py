"""Read all four goal classes after each parser-delimited Rocq command via RocqIDE."""

import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path


def elem(tag, *children, text=None, **attrs):
    node = ET.Element(tag, attrs)
    node.text = text
    node.extend(children)
    return node


def call(proc, reader, name, argument):
    proc.stdin.write(ET.tostring(elem("call", argument, val=name)))
    proc.stdin.flush()
    while True:
        for _, node in reader.read_events():
            if node.tag == "value":
                if node.get("val") != "good":
                    raise ValueError(f"{name} failed: {''.join(node.itertext())}")
                return node
        chunk = os.read(proc.stdout.fileno(), 65536)
        if not chunk:
            raise ValueError(f"RocqIDE closed before answering {name}")
        reader.feed(chunk)


def replay(executable, src, timing, output, flags):
    raw = Path(src).read_bytes()
    spans = json.loads(Path(timing).read_bytes())
    reader = ET.XMLPullParser(["end"])
    reader.feed('<!DOCTYPE protocol [<!ENTITY nbsp "&#32;">]><protocol>')
    with subprocess.Popen([executable, "-main-channel", "stdfds", "-async-proofs", "off",
                           "-topfile", src, *flags], stdin=subprocess.PIPE, stdout=subprocess.PIPE) as proc:
        try:
            state = call(proc, reader, "Init", elem("option", val="none")).find("state_id").get("val")
            trace = []
            for start, stop in spans:
                text = raw[start:stop].decode()
                command = elem("pair", elem("string", text=text), elem("int", text="0"))
                parent = elem("pair", elem("state_id", val=state), elem("bool", val="false"))
                body = elem("pair", elem("pair", command, parent), elem("int", text=str(start)))
                line = raw[:start].count(b"\n") + 1
                bol = raw.rfind(b"\n", 0, start) + 1
                location = elem("pair", elem("int", text=str(line)), elem("int", text=str(bol)))
                response = call(proc, reader, "Add", elem("pair", body, location))
                state = response.find("./pair/state_id").get("val")
                reply = call(proc, reader, "Goal", elem("unit"))
                goals = reply.find("./option/goals")
                result = None
                if goals is not None:
                    if len(goals) != 4:
                        raise ValueError("unknown RocqIDE goal layout")
                    # Background goals are pairs of lists (before/after) per focus
                    # frame. Preserve that structure and the native goal IDs.
                    result = {key: ET.tostring(group, encoding="unicode")
                              for key, group in zip(("focused", "background", "shelved", "given_up"), goals)}
                trace.append({"start_byte": start, "end_byte": stop, "goals": result})
            call(proc, reader, "Quit", elem("unit"))
            Path(output).write_text(json.dumps(trace, ensure_ascii=False))
        finally:
            proc.stdin.close()
            if proc.poll() is None:
                proc.terminate()


if __name__ == "__main__":
    replay(*sys.argv[1:5], sys.argv[5:])
