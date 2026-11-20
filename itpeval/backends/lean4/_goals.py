"""Small framed LSP client for a supervised Lean server transaction."""
import json
from pathlib import Path
import subprocess
import sys


def proof_error(observation):
    has_goals = bool((observation["goal"] or {}).get("goals"))
    # A tagged unsolved-goals diagnostic is expected at an open tactic state.
    return next((diagnostic["message"] for diagnostic in observation["diagnostics"]
                 if diagnostic.get("severity") == 1 and
                 (not has_goals or 1 not in (diagnostic.get("leanTags") or ()))), None)


def exchange(server, request, uri, diagnostics):
    packet = json.dumps({"jsonrpc": "2.0", **request}, ensure_ascii=False).encode()
    server.stdin.write(f"Content-Length: {len(packet)}\r\n\r\n".encode() + packet)
    server.stdin.flush()
    if "id" not in request:
        return None
    while True:
        size = None
        while True:
            line = server.stdout.readline(8192)
            if not line:
                raise RuntimeError("Lean language server exited before replying")
            if line == b"\r\n":
                break
            if line.lower().startswith(b"content-length:"):
                size = int(line.split(b":", 1)[1])
        if size is None or size < 0 or size > 32 * 1024 * 1024:
            raise RuntimeError("invalid Lean LSP frame length")
        response = json.loads(server.stdout.read(size))
        if response.get("method") == "textDocument/publishDiagnostics":
            params = response["params"]
            if params["uri"] == uri:
                diagnostics[params.get("version")] = params["diagnostics"]
        elif response.get("id") == request["id"]:
            if "error" in response:
                raise RuntimeError(str(response["error"]))
            return response["result"]


def main():
    lean, root, spec = sys.argv[1:]
    spec = json.loads(Path(spec).read_text())
    uri = (Path(root) / spec["entrypoint"]).as_uri()
    server = subprocess.Popen([lean, "--server"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, cwd=root)
    diagnostics = {}
    def send(method, params, rid=None):
        request = {"method": method, "params": params}
        if rid is not None:
            request["id"] = rid
        return exchange(server, request, uri, diagnostics)
    try:
        send("initialize", {"processId": None, "rootUri": Path(root).as_uri(), "capabilities": {}}, 0)
        send("initialized", {})
        output = []
        for i, revision in enumerate(spec["revisions"], 1):
            diagnostics.clear()
            text = revision["text"]
            document = {"uri": uri, "version": i}
            if i == 1:
                send("textDocument/didOpen", {"textDocument": {**document, "languageId": "lean4", "text": text}})
            else:
                send("textDocument/didChange", {"textDocument": document, "contentChanges": [{"text": text}]})
            send("textDocument/waitForDiagnostics", document, 3*i)
            result = send("$/lean/plainGoal", {"textDocument": {"uri": uri},
                                              "position": revision["position"]}, 3*i + 1)
            observation = {"version": i, "goal": result,
                           "diagnostics": diagnostics.get(i, diagnostics.get(None, []))}
            output.append(observation)
            if spec.get("stop_on_refusal") and (not (result or {}).get("goals") or
                                                proof_error(observation) is not None):
                break
        print(json.dumps(output, ensure_ascii=False))
        send("shutdown", None, 3*len(output) + 2)
        send("exit", None)
    finally:
        server.terminate()
        server.wait()


if __name__ == "__main__":
    main()
