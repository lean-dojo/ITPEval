"""One disposable Isa-REPL server and client under the runtime's job supervisor."""
import json
import os
import socket
import subprocess
import sys
import time
from pathlib import Path


def main():
    root = Path.cwd()
    request = json.loads((root / "request.json").read_text())
    sys.path.insert(0, request["isa_repl"])
    from IsaREPL import Client

    # The upstream binary protocol accepts a TCP address. Restrict the listener
    # to loopback and keep its lifetime within this one supervised job.
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        address = f"127.0.0.1:{sock.getsockname()[1]}"
    run_theory = root / "ITPEvalProbe.thy"
    run_theory.write_text(
        'theory ITPEvalProbe imports Isa_REPL.Isa_REPL begin\n'
        'ML \\<open> REPL.disable_output (); Isabelle_Thread.join (REPL_Server.startup '
        '(Path.explode (getenv "ITPEVAL_REPL_ROOT")) NONE (getenv "ITPEVAL_REPL_ADDRESS")) \\<close>\nend\n')
    env = dict(os.environ, USER_HOME=str(root), REPL_PID=str(os.getpid()), REPL_DEFAULT_SESSION="HOL",
               ITPEVAL_REPL_ROOT=str(root), ITPEVAL_REPL_ADDRESS=address)
    cmd = [request["isabelle"], "process", "-l", "HOL", "-d", request["isa_repl"],
           "-d", request["auto_sledgehammer"], "-o", "threads=2", "-o", "quick_and_dirty=false",
           "-e", 'Thy_Info.use_thy "ITPEvalProbe"']
    server = subprocess.Popen(cmd, env=env, stdin=subprocess.DEVNULL)
    try:
        while server.poll() is None:
            try:
                client = Client(address, "HOL")
                break
            except ConnectionRefusedError:
                time.sleep(0.15)
        else:
            raise RuntimeError("Isabelle terminated before the REPL started")
        with client:
            initial, error = client.eval(request["prologue"])
            if error:
                raise ValueError(f"could not enter the target proof: {error}")
            client.record_state("target")
            branches = []
            for action in request["candidates"]:
                restored = client.rollback("target")
                outputs, error = client.eval(action)
                branches.append({"candidate": action, "restored": Client.parse_output(restored),
                                 "commands": [Client.parse_output(r) for r in outputs or ()],
                                 "error": error})
            result = {"initial": [Client.parse_output(r) for r in initial], "branches": branches,
                      "client_version": Client.VERSION}
            (root / "observations.json").write_text(json.dumps(result, ensure_ascii=False))
    finally:
        server.terminate()
        try:
            server.wait(timeout=3)
        except subprocess.TimeoutExpired:
            server.kill()
            server.wait()


if __name__ == "__main__":
    main()
