"""Opt-in preloaded HOL Light process for the packaged, reviewed proof projects."""
from __future__ import annotations

from contextlib import ExitStack
from hashlib import sha256
import json
import math
import os
from pathlib import Path
import select
import socket
import struct
import subprocess
import sys
from tempfile import TemporaryDirectory, TemporaryFile
from threading import RLock
from time import monotonic

from itpeval.runtime import process
from itpeval.runtime.process import ProcessResult, run_process


# Snapshot inventory digests cover the manifest, every source, and mode bits.
# Atom and source review for arbitrary OCaml scripts is outside this profile.
_PROFILES = frozenset({
    "971998fc113f6541bcd08320fb9f74cb5872063da97b9c033f0a9b17e4ed019c",  # completion
    "6a86f970d7c14484e4706c6b23029c21882c3dae37a4aeecf479d0753fb10d30",  # interaction
    "882af122550df96243f2688ae041694aa29068c9e216df34b115cf4fe85f4d33",  # warm-import
    "8b0ddd133494202e23232f9a9b87a376bbb5fd27c4a1305f8d9299ddba6c4bad",  # automation
})
_COORDINATOR = Path(__file__).with_name("worker.ml")
_TRACE = Path(__file__).with_name("tactics.ml")
_TACTICS = Path(__file__).resolve().parents[1] / "hol_tactics.py"
_GUARDIAN = Path(process.__file__).with_name("_linux_job.py")
_NATIVE_IO = _GUARDIAN.parents[1] / "extraction/native_io.py"
_REQUIRED_ROOTS = {"launchers", "src", "opamroot/hol-light/lib", "opamroot/hol-light/bin"}


def _environment(prepared):
    env = {key: os.environ[key] for key in ("HOME", "PATH", "USER", "LANG") if key in os.environ}
    env.update(prepared.environment)
    return env


def _descendants(pid):
    pending = [pid]
    result = set()
    while pending:
        parent = pending.pop()
        try:
            children = Path(f"/proc/{parent}/task/{parent}/children").read_text()
        except FileNotFoundError:
            continue
        for child in map(int, children.split()):
            if child not in result:
                result.add(child)
                pending.append(child)
    return result


def _stop_process(guardian):
    if guardian.poll() is None:
        # The Linux subreaper kills and waits for the native parent, all its
        # children, and descendants that already left their process group.
        guardian.terminate()
        guardian.wait()


def _tail(path, maximum):
    if not path.is_file():
        return "", False
    with path.open("rb") as stream:
        size = stream.seek(0, os.SEEK_END)
        stream.seek(max(0, size - maximum))
        return stream.read(maximum).decode("utf-8", errors="replace"), size > maximum


class _Stopped(RuntimeError):
    pass


def _check_deadline(deadline, cancel):
    if cancel is not None and cancel.is_set():
        raise _Stopped("cancelled")
    if monotonic() >= deadline:
        raise _Stopped("timeout")


class ForkedHOLLight:
    """Reuse the pinned HOL core in isolated process children.

    The reviewed profile covers the packaged HOL Light completion, branching,
    local-import, and automation exercises. Start with a context manager or `start()` and
    release the process with `close()`. A worker serializes its requests.
    """

    @staticmethod
    def supports_project(prepared) -> bool:
        """Check platform, project profile and the local compiler layout without starting a worker."""
        if (not sys.platform.startswith("linux") or not Path("/proc/self/task").is_dir()
                or not hasattr(socket, "SO_PEERCRED")):
            return False
        if (prepared.spec.prover != "hol-light" or prepared.spec.checking_profile != "strict"
                or prepared.spec.project_revision not in _PROFILES or prepared.spec.options
                or prepared.library_paths or prepared.extra_inputs
                or not _REQUIRED_ROOTS.issubset(prepared.build.get("runtime_roots", {}))):
            return False
        root = prepared.prefix / "hol-light"
        launch = root / "bin/hollight-run"
        compile_ = root / "opamroot/hol-light/bin/ocamlc"
        return all(path.is_file() and os.access(path, os.X_OK) for path in (launch, compile_))

    def __init__(self, prepared, *, startup_timeout_s=180):
        if (not sys.platform.startswith("linux") or not Path("/proc/self/task").is_dir()
                or not hasattr(socket, "SO_PEERCRED")):
            raise NotImplementedError("the preloaded HOL Light worker requires the Linux job guardian")
        if not math.isfinite(startup_timeout_s) or startup_timeout_s <= 0:
            raise ValueError("worker startup timeout must be positive and finite")
        if not self.supports_project(prepared):
            raise ValueError("warm HOL Light requires a packaged proof project and the pinned distribution layout")
        self.prepared = prepared
        self.startup_timeout_s = startup_timeout_s
        self._lock = RLock()
        self._resources = ExitStack()
        self._closed = False
        self._guardian = None
        self._control = None
        self._identity = None
        self._baseline = set()

    @property
    def active(self):
        return not self._closed and self._control is not None and self._guardian.poll() is None

    def _require_task(self, task, prepared):
        if (prepared.environment_id != self.prepared.environment_id or prepared.prefix != self.prepared.prefix
                or task.environment_id != prepared.environment_id or task.prover != "hol-light"
                or task.manifest_path != "completion.json" or task.artifact.entrypoint != "hello.ml"):
            raise ValueError("warm HOL Light session requires the worker's reviewed task and prepared lock")
        if task.budgets.cpu_seconds is not None or task.budgets.memory_bytes is not None:
            raise ValueError("warm HOL Light requires default CPU and address-space limits")

    def _fingerprint(self):
        files = (_COORDINATOR, _TRACE, Path(__file__), _TACTICS, _GUARDIAN, _NATIVE_IO)
        return (tuple(sha256(path.read_bytes()).hexdigest() for path in files),
                tuple(sorted(_environment(self.prepared).items())))

    def _validate(self, prepared):
        prepared.validate()
        if self._identity != self._fingerprint():
            raise ValueError("preloaded HOL Light worker implementation or launch environment changed")

    def _wait_input(self, channel, deadline, cancel):
        while True:
            _check_deadline(deadline, cancel)
            if self._guardian.poll() is not None:
                raise RuntimeError("preloaded HOL Light parent exited")
            if select.select([channel], [], [], min(0.05, max(0, deadline - monotonic())))[0]:
                return

    def _response(self, deadline, cancel):
        message = bytearray()
        while b"\n" not in message:
            self._wait_input(self._control, deadline, cancel)
            chunk = self._control.recv(128)
            if not chunk or len(message) + len(chunk) > 128:
                raise RuntimeError("incomplete or oversized HOL Light worker response")
            message.extend(chunk)
        if not message.endswith(b"\n") or message.count(b"\n") != 1:
            raise RuntimeError("invalid HOL Light worker response")
        try:
            kind, value = message.decode("ascii").split()
            return kind, int(value)
        except ValueError as exc:
            raise RuntimeError("invalid HOL Light worker response") from exc

    def start(self, *, cancel=None):
        with self._lock:
            if self._closed:
                raise RuntimeError("HOL Light worker is closed")
            if self.active:
                return self
            if self._guardian is not None:
                self.close()
                raise RuntimeError("preloaded HOL Light parent exited")
            try:
                self._identity = self._fingerprint()
                self._validate(self.prepared)
                self._boot(cancel)
                self._validate(self.prepared)
                return self
            except BaseException:
                self.close()
                raise

    def _boot(self, cancel):
        deadline = monotonic() + self.startup_timeout_s
        work = Path(self._resources.enter_context(TemporaryDirectory(prefix="itpeval-hol-worker-")))
        source = work / "worker.ml"
        coordinator = _COORDINATOR.read_bytes()
        if sha256(coordinator).hexdigest() != self._identity[0][0]:
            raise ValueError("HOL Light coordinator changed during startup")
        source.write_bytes(coordinator)
        compiler = self.prepared.prefix / "hol-light/opamroot/hol-light/bin/ocamlc"
        compiled = run_process([str(compiler), "-I", "+unix", "-I", "+compiler-libs", "-c", str(source)],
                               cwd=work, env=_environment(self.prepared), timeout_s=min(30, self.startup_timeout_s),
                               max_log_bytes=16384, cancel=cancel)
        if compiled.outcome != "exited" or compiled.returncode:
            raise RuntimeError("HOL Light coordinator compilation failed: " + (compiled.stderr or compiled.outcome))
        loader = work / "loader.ml"
        loader.write_text('#directory "+unix";;\n#load "unix.cma";;\n#load '
                          + json.dumps(str(source.with_suffix(".cmo")), ensure_ascii=False) + ";;\n",
                          encoding="utf-8")
        listener = self._resources.enter_context(socket.socket(socket.AF_UNIX, socket.SOCK_STREAM))
        # This socket lives in the worker's private directory. SO_PEERCRED also
        # verifies that the connection belongs to the supervised process tree.
        address = str(work / "control")
        listener.bind(address)
        listener.listen(1)
        log_path = work / "startup.log"
        logs = self._resources.enter_context(log_path.open("wb"))
        metrics = self._resources.enter_context(TemporaryFile())
        exe = self.prepared.prefix / "hol-light/bin/hollight-run"
        self._guardian = subprocess.Popen(
            [sys.executable, "-S", str(_GUARDIAN), str(metrics.fileno()), str(exe), str(loader)],
            cwd=work, env={**_environment(self.prepared), "ITPEVAL_HOL_WORKER_SOCKET": address},
            stdin=subprocess.DEVNULL, stdout=logs, stderr=subprocess.STDOUT,
            pass_fds=(metrics.fileno(),), start_new_session=True,
        )
        self._resources.callback(_stop_process, self._guardian)
        try:
            self._wait_input(listener, deadline, cancel)
            control, _ = listener.accept()
            listener.close()
            self._control = self._resources.enter_context(control)
            kind, ready_pid = self._response(deadline, cancel)
            peer = control.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, struct.calcsize("3i"))
            peer_pid, peer_uid, _ = struct.unpack("3i", peer)
            self._baseline = _descendants(self._guardian.pid)
            if kind != "READY" or ready_pid != peer_pid or peer_uid != os.geteuid() or peer_pid not in self._baseline:
                raise RuntimeError("HOL Light worker failed its readiness handshake")
        except RuntimeError as exc:
            log, _ = _tail(log_path, 2400)
            raise RuntimeError(f"HOL Light worker startup failed ({exc}): {log}") from exc

    def _run(self, task, prepared, work, cancel, *, timeout_s=None):
        self._require_task(task, prepared)
        started = monotonic()
        deadline = started + (task.budgets.timeout_s if timeout_s is None else timeout_s)
        acquired = False
        dispatched = False
        try:
            while not acquired:
                _check_deadline(deadline, cancel)
                acquired = self._lock.acquire(timeout=min(0.05, max(0, deadline - monotonic())))
            if not self.active:
                if self._guardian is not None:
                    self.close()
                raise RuntimeError("HOL Light worker requires an active context or start()")
            try:
                self._validate(prepared)
            except (OSError, ValueError, RuntimeError) as exc:
                self.close()
                raise ValueError("HOL Light worker retired after locked inputs changed") from exc
            _check_deadline(deadline, cancel)
            dispatched = True
            self._control.sendall(b"RUN " + os.fsencode(work).hex().encode("ascii") + b"\n")
            kind, status = self._response(deadline, cancel)
            if kind != "EXIT" or _descendants(self._guardian.pid) - self._baseline:
                self.close()
                raise RuntimeError("HOL Light worker retired after an abnormal child exit or surviving descendant")
            stdout, stdout_clipped = _tail(work / "stdout", task.budgets.max_log_bytes)
            stderr, stderr_clipped = _tail(work / "stderr", task.budgets.max_log_bytes)
            return ProcessResult(status, "exited", stdout, stderr, round((monotonic() - started) * 1000),
                                 stdout_clipped or stderr_clipped)
        except _Stopped as exc:
            if dispatched:
                self.close()
            return ProcessResult(-9, str(exc), "", "", round((monotonic() - started) * 1000), False)
        except (OSError, RuntimeError):
            if dispatched:
                self.close()
            raise
        finally:
            if acquired:
                self._lock.release()

    def close(self):
        with self._lock:
            if not self._closed:
                self._closed = True
                self._resources.close()
                self._control = None

    def __enter__(self):
        return self.start()

    def __exit__(self, exc_type, exc, traceback):
        self.close()
