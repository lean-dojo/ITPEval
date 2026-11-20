"""Single checker launch path shared by strict and benchmark compatibility modes."""
from pathlib import Path
from threading import Event

from .process import run_process


def execute_checker(script: Path, workspace: Path, env: dict[str, str], *,
                    timeout_s: float | None, cancel: Event | None = None,
                    max_log_bytes: int = 1 << 20, memory_bytes: int | None = None,
                    cpu_seconds: int | None = None):
    return run_process(["/bin/bash", str(script)], cwd=workspace, env=env, timeout_s=timeout_s,
                       cancel=cancel, max_log_bytes=max_log_bytes, memory_bytes=memory_bytes,
                       cpu_seconds=cpu_seconds)
