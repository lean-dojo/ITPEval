"""Linux job guardian, invoked as a separate interpreter by run_process."""
import ctypes
import os
import json
import resource
import signal
import subprocess
import sys


def main():
    # PR_SET_CHILD_SUBREAPER ensures detached grandchildren reparent here.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "setting child subreaper failed")
    stop = False

    def stop_job(signum, frame):
        nonlocal stop
        stop = True

    signal.signal(signal.SIGTERM, stop_job)
    metrics_fd = int(sys.argv[1])
    argv = sys.argv[2:]
    native_signal = None
    launch_error = None
    children = f"/proc/self/task/{os.getpid()}/children"
    try:
        try:
            proc = subprocess.Popen(argv, start_new_session=True)
        except OSError as exc:
            launch_error = str(exc)
            print(launch_error, file=sys.stderr)
            return 127 if isinstance(exc, FileNotFoundError) else 126
        while not stop:
            try:
                returncode = proc.wait(timeout=0.05)
                if returncode < 0:
                    native_signal = -returncode
                    return 128 + native_signal
                return returncode
            except subprocess.TimeoutExpired:
                pass
        return 143
    finally:
        # Direct children killed in each pass may themselves have children. After
        # waitpid these reparent to the guardian, even if they called setsid().
        while True:
            with open(children, encoding="ascii") as stream:
                pids = stream.read().split()
            if not pids:
                break
            for pid in pids:
                try:
                    os.kill(int(pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
            try:
                os.waitpid(-1, 0)
            except ChildProcessError:
                break
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        peak, cpu = usage.ru_maxrss * 1024, usage.ru_utime + usage.ru_stime
        summary = {"peak_rss_bytes": peak, "cpu_seconds": cpu, "signal": native_signal,
                   "launch_error": launch_error}
        os.write(metrics_fd, json.dumps(summary).encode())
        os.close(metrics_fd)


if __name__ == "__main__":
    raise SystemExit(main())
