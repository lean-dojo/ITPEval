"""Supervise Linux/POSIX foreground commands and their process group."""
from __future__ import annotations

import os
import json
import tempfile
import selectors
import signal
import sys
import subprocess
import time
from contextlib import nullcontext
from dataclasses import dataclass
from pathlib import Path
from threading import Event
from typing import Mapping, Sequence

from .logging import LogTail


@dataclass(frozen=True)
class ProcessResult:
    returncode: int
    outcome: str
    stdout: str
    stderr: str
    duration_ms: int
    truncated: bool
    peak_process_rss_bytes: int | None = None
    cpu_time_s: float | None = None


def task_environment(environ: Mapping[str, str] | None = None) -> dict[str, str]:
    env = dict(os.environ if environ is None else environ)
    for key in ("ITPEVAL_TASK", "ITPEVAL_TASK_DIR", "ITPEVAL_TASK_ROOT", "ITPEVAL_TASK_FILE",
                "ITPEVAL_OPERATION", "ITPEVAL_EXPECT_TARGET", "ITPEVAL_LOCAL_SOURCES",
                "ITPEVAL_ISABELLE_USER_HOME"):
        env.pop(key, None)
    return env


def _kill_group(pid: int) -> None:
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def run_process(command: Sequence[str], *, cwd: Path | None = None,
                env: Mapping[str, str] | None = None, timeout_s: float | None = None,
                max_log_bytes: int = 1 << 20, cancel: Event | None = None,
                memory_bytes: int | None = None, cpu_seconds: int | None = None,
                merge_stderr: bool = False, stdin_path: Path | None = None) -> ProcessResult:
    """Return bounded tail logs. Limits apply individually to descendant processes."""
    if max_log_bytes <= 0:
        raise ValueError("max_log_bytes must be positive")
    if cancel is not None and cancel.is_set():
        return ProcessResult(-signal.SIGKILL, "cancelled", "", "", 0, False)
    argv = list(command)
    if memory_bytes is not None or cpu_seconds is not None:
        limits = []
        if memory_bytes is not None:
            limits.append(f"--as={memory_bytes}")
        if cpu_seconds is not None:
            limits.append(f"--cpu={cpu_seconds}:{cpu_seconds + 1}")
        argv = ["prlimit", *limits, "--", *argv]
    started = time.monotonic()
    deadline = None if timeout_s is None else started + timeout_s
    guarded = sys.platform.startswith("linux") and Path("/proc/self/task").exists()
    metrics = tempfile.TemporaryFile() if guarded else None
    if guarded:
        # The guardian only uses the standard library. Skip Python site initialization on each launch.
        argv = [sys.executable, "-S", str(Path(__file__).with_name("_linux_job.py")), str(metrics.fileno()), *argv]
    input_context = stdin_path.open("rb") if stdin_path is not None else nullcontext(subprocess.DEVNULL)
    with input_context as task_input:
        proc = subprocess.Popen(argv, cwd=cwd, env=env, start_new_session=True,
                                stdin=task_input, stdout=subprocess.PIPE,
                                pass_fds=(metrics.fileno(),) if guarded else (),
                                stderr=subprocess.STDOUT if merge_stderr else subprocess.PIPE)
    streams = {name: LogTail(max_log_bytes) for name in ("stdout", "stderr")}
    outcome = "exited"
    def terminate():
        if guarded:
            proc.terminate()
        else:
            _kill_group(proc.pid)

    # Read one bounded chunk per ready fd to avoid starving the deadline check.
    try:
        with selectors.DefaultSelector() as selector:
            selector.register(proc.stdout, selectors.EVENT_READ, "stdout")
            if proc.stderr is not None:
                selector.register(proc.stderr, selectors.EVENT_READ, "stderr")
            while selector.get_map() or proc.poll() is None:
                if outcome == "exited":
                    if cancel is not None and cancel.is_set():
                        outcome = "cancelled"
                    elif deadline is not None and time.monotonic() >= deadline:
                        outcome = "timeout"
                if outcome != "exited" or (not guarded and proc.poll() is not None):
                    terminate()
                for key, _ in selector.select(0.05):
                    data = os.read(key.fd, 65536)
                    if not data:
                        selector.unregister(key.fileobj)
                        continue
                    streams[key.data].append(data)
    finally:
        terminate()
        proc.wait()
        proc.stdout.close()
        if proc.stderr is not None:
            proc.stderr.close()
    if outcome == "exited":
        if proc.returncode in (-signal.SIGXCPU, -signal.SIGXFSZ, 128 + signal.SIGXCPU):
            outcome = "resource_exhausted"
        elif proc.returncode < 0 or proc.returncode in (134, 135, 137, 139):
            outcome = "crash"
    peak, cpu = None, None
    native_signal = None
    if metrics is not None:
        with metrics:
            metrics.seek(0)
            payload = metrics.read()
            if payload:
                info = json.loads(payload)
                peak, cpu = info["peak_rss_bytes"], info["cpu_seconds"]
                native_signal = info["signal"]
                if info["launch_error"] and outcome == "exited":
                    outcome = "unavailable_environment"
    if outcome == "exited" and native_signal is not None:
        outcome = "resource_exhausted" if native_signal in (signal.SIGXCPU, signal.SIGXFSZ) else "crash"
    return ProcessResult(proc.returncode, outcome, streams["stdout"].text(), streams["stderr"].text(),
                         round((time.monotonic() - started) * 1000),
                         any(log.truncated for log in streams.values()), peak, cpu)
