"""Supervised framed Pétanque RPC round-trip for a single native proof."""
import json
from pathlib import Path
import subprocess
import sys


def rpc(proc, method, params, rid):
    payload = json.dumps({"jsonrpc":"2.0", "id":rid, "method":method, "params":params}).encode()
    proc.stdin.write(f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload)
    proc.stdin.flush()
    while True:
        length = None
        while True:
            line = proc.stdout.readline(8192)
            if not line:
                raise RuntimeError("Pétanque terminated before responding")
            if not line.strip():
                break
            if line.lower().startswith(b"content-length:"):
                length = int(line.split(b":", 1)[1])
        if length is None or not 0 <= length <= 32 * 1024**2:
            raise RuntimeError("invalid Pétanque RPC frame")
        msg = json.loads(proc.stdout.read(length))
        if msg.get("id") == rid:
            return msg


def main():
    spec = json.loads(Path(sys.argv[2]).read_text())
    root = Path.cwd()
    proc = subprocess.Popen([sys.argv[1], f"--root={root}"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        start = rpc(proc, "petanque/start", {"uri":(root/spec["path"]).as_uri(), "thm":spec["target"]}, 0)
        states = []
        ids = []
        response = start
        for i, (parent, command) in enumerate([(None, None), *spec["actions"]]):
            if command is not None:
                response = rpc(proc, "petanque/run", {"st": ids[parent], "tac": command}, 2 * i)
            if "error" in response:
                states.append({"parent": parent, "command": command, "error": response["error"]})
                break
            result = response["result"]
            state = result["st"]
            ids.append(state)
            goals = rpc(proc, "petanque/goals", {"st": state}, 2 * i + 1)
            states.append({"parent": parent, "command": command, "native": result, "goals": goals.get("result"),
                           "error": goals.get("error")})
            if "error" in goals:
                break
        print(json.dumps(states, ensure_ascii=False))
    finally:
        proc.terminate()
        proc.wait()


if __name__ == "__main__":
    main()
