"""Discover and install native prover toolchains from the public CLI."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path

from itpeval.environments.toolchains import LAUNCHERS, PACKAGE
from itpeval.runtime.process import run_process, task_environment


def _selection(args):
    if args.provers in ([], ["all"]):
        return sorted(LAUNCHERS)
    if "all" in args.provers:
        raise ValueError("use all by itself or list individual provers")
    return list(dict.fromkeys(args.provers))


def _probe(prover, prefix, timeout_s):
    launcher = prefix / prover / "bin" / LAUNCHERS[prover]
    result = {"prover": prover, "launcher": str(launcher), "version": None}
    if not launcher.is_file() or not os.access(launcher, os.X_OK):
        return {**result, "status": "missing"}
    environment = task_environment()
    environment["ITPEVAL_PREFIX"] = str(prefix)
    check = run_process(["bash", str(PACKAGE / "provers" / prover / "version.sh")],
                        cwd=prefix, env=environment, timeout_s=timeout_s, max_log_bytes=8192)
    version = check.stdout.strip()
    if check.outcome != "exited" or check.returncode != 0 or not version:
        return {**result, "status": "unavailable",
                "detail": check.stderr.strip() or f"{check.outcome}, exit code {check.returncode}"}
    return {**result, "status": "available", "version": version}


def _status(args):
    if args.timeout_s <= 0:
        raise ValueError("version query timeout must be positive")
    prefix = Path(args.prefix).expanduser().resolve()
    provers = _selection(args)
    with ThreadPoolExecutor(max_workers=min(4, len(provers))) as workers:
        tools = list(workers.map(lambda prover: _probe(prover, prefix, args.timeout_s), provers))
    if args.json:
        print(json.dumps({"prefix": str(prefix), "toolchains": tools}, ensure_ascii=False))
    else:
        print(f"Toolchains in {prefix}")
        for tool in tools:
            detail = tool["version"] or tool.get("detail") or tool["launcher"]
            print(f'{tool["prover"]:<11} {tool["status"]:<12} {detail.splitlines()[0]}')
    return int(any(tool["status"] != "available" for tool in tools))


def _install(args):
    from itpeval.environments.install import install_toolchain

    for prover in _selection(args):
        try:
            receipt = install_toolchain(prover, prefix=Path(args.prefix).expanduser(), cache=args.cache,
                                        profile=args.profile, jobs=args.jobs, timeout_s=args.timeout_s)
        except RuntimeError as exc:
            raise ValueError(str(exc)) from exc
        print(receipt, flush=True)
    return 0


def add_commands(parent):
    from itpeval.environments.install import PROFILES

    tools = parent.add_parser("toolchains", help="inspect or install pinned native provers")
    commands = tools.add_subparsers(dest="toolchains_command", required=True)
    choices = ("all", *sorted(LAUNCHERS))
    status = commands.add_parser("status", help="query installed native launchers and versions")
    status.add_argument("provers", nargs="*", choices=choices)
    status.add_argument("--timeout-s", type=float, default=20, help="deadline for each version query")
    status.add_argument("--json", action="store_true", help="emit machine-readable results")
    status.set_defaults(func=_status)
    install = commands.add_parser("install", help="install selected native builds on Linux x86-64 or WSL")
    install.add_argument("provers", nargs="+", choices=choices)
    install.add_argument("--profile", choices=PROFILES, default="stable")
    cache_home = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    install.add_argument("--cache", type=Path, default=cache_home / "itpeval/release")
    install.add_argument("--jobs", type=int, default=4, help="native build jobs for each prover")
    install.add_argument("--timeout-s", type=float, default=10800, help="deadline for each native install")
    install.set_defaults(func=_install)
