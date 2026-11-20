"""Build native file layouts for the legacy source and snippet interface."""
from __future__ import annotations

import re
from pathlib import Path


# These adapters consume one file with a conventional name in both input modes.
PLAIN_FILES = {
    "lean4": "Hello.lean", "rocq": "hello.v", "hol-light": "hello.ml",
    "acl2": "hello.lsp", "acl2r": "hello.lsp", "metamath": "hello.mm",
}

HOL4_TARGET_MARKER = "(* ITPEVAL_AGENT_TARGET *)"


def hol4_wrapper_text() -> str:
    return "\n".join(
        (
            "open HolKernel Parse boolLib;",
            "",
            'val _ = new_theory "hello";',
            "",
            HOL4_TARGET_MARKER,
            "",
            "val _ = export_theory();",
            "",
        )
    )


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content if content.endswith("\n") else content + "\n", encoding="utf-8")


def _uncomment_isabelle(code: str) -> str:
    uncommented: list[str] = []
    depth = 0
    index = 0
    while index < len(code):
        if code.startswith("(*", index):
            depth += 1
            uncommented.extend("  ")
            index += 2
            continue
        if depth and code.startswith("*)", index):
            depth -= 1
            uncommented.extend("  ")
            index += 2
            continue

        char = code[index]
        uncommented.append(char if depth == 0 or char == "\n" else " ")
        index += 1

    return "".join(uncommented)


def _isabelle_theory_name(code: str) -> str:
    match = re.search(
        r'(?m)^\s*theory\s+"?([A-Za-z][A-Za-z0-9_\'.-]*)"?\b',
        _uncomment_isabelle(code),
    )
    return match.group(1) if match else "Hello"


def _isabelle_session_imports(code: str) -> list[str]:
    header = re.search(
        r"(?ms)^\s*theory\b.*?\bimports\b(?P<imports>.*?)^\s*begin\b",
        _uncomment_isabelle(code),
    )
    if header is None:
        return []

    sessions = {
        theory_name.split(".", maxsplit=1)[0]
        for theory_name in re.findall(r'"([^"]+)"', header.group("imports"))
        if "." in theory_name and theory_name.split(".", maxsplit=1)[0].startswith("HOL-")
    }
    return sorted(sessions)


def _normalize_isabelle_placeholders(code: str) -> str:
    return re.sub(r"(?m)^([ \t]*)by[ \t]+sorry[ \t]*$", r"\1sorry", code)


def _agda_module_name(code: str) -> str:
    uncommented = re.sub(r"(?m)--.*$", "", code)
    match = re.search(
        r"(?m)^\s*module\s+([^\s;]+)\s+where\b",
        uncommented,
    )
    return match.group(1) if match else "Hello"


def _agda_module_path(module_name: str) -> Path:
    parts = module_name.split(".")
    if any(
        not part
        or part in {".", ".."}
        or "/" in part
        or "\\" in part
        for part in parts
    ):
        raise ValueError(f"unsafe Agda module name: {module_name!r}")
    return Path(*parts[:-1], f"{parts[-1]}.agda")


def _pvs_theory_name(code: str) -> str:
    uncommented = re.sub(r"(?m)%.*$", "", code)
    match = re.search(
        r"(?im)^\s*([A-Za-z][A-Za-z0-9_?'-]*)"
        r"(?:\s*\[[^\n]*\])?\s*:\s*THEORY\b",
        uncommented,
    )
    return match.group(1) if match else "Hello"


def prepare_task_dir(
    *,
    prover: str,
    code: str,
    mode: str,
    task_dir: Path,
) -> Path | None:
    """Stage a raw source file or wrap a snippet for the selected native checker.

    Return its relative entrypoint when the checker uses explicit file selection.
    Other adapters discover their conventional files inside the task directory.
    """
    mode = mode.lower().strip()
    if mode not in {"raw", "snippet"}:
        raise ValueError(f"unknown mode: {mode!r}")

    if prover in PLAIN_FILES:
        entry = Path(PLAIN_FILES[prover])
        _write_text(task_dir / entry, code)
        # These adapters accept the staged entrypoint through ITPEVAL_TASK_FILE.
        if prover in {"acl2", "acl2r", "metamath"}:
            return entry
        return None

    if prover == "agda":
        if mode == "snippet":
            wrapped = "module Hello where\n\n" + code
            relative = Path("Hello.agda")
            _write_text(task_dir / relative, wrapped)
        else:
            relative = _agda_module_path(_agda_module_name(code))
            _write_text(task_dir / relative, code)
        return relative

    if prover == "isabelle":
        if mode == "snippet":
            theory_name = "Hello"
            session_name = "ITPEval_Hello"
            thy = "theory Hello\n  imports Main\nbegin\n\n" + code + "\n\nend\n"
        else:
            theory_name = _isabelle_theory_name(code)
            session_name = f"ITPEval_{theory_name}"
            thy = _normalize_isabelle_placeholders(code)

        root_lines = [f'session "{session_name}" = HOL +']
        session_imports = _isabelle_session_imports(thy)
        if session_imports:
            root_lines.append("  sessions")
            root_lines.extend(f'    "{session}"' for session in session_imports)
        root_lines.extend(("  theories", f"    {theory_name}"))
        _write_text(
            task_dir / "ROOT",
            "\n".join(root_lines),
        )
        _write_text(task_dir / f"{theory_name}.thy", thy)
        return None

    if prover == "hol4":
        target = Path("AgentTarget.sml")
        _write_text(task_dir / target, code)
        _write_text(task_dir / "Holmakefile", "THEORIES = hello")
        _write_text(task_dir / "helloScript.sml", hol4_wrapper_text())
        return target

    if prover == "mizar":
        if mode == "snippet":
            wrapped = "environ\n\nbegin\n\n" + code + "\n"
            _write_text(task_dir / "hello.miz", wrapped)
        else:
            _write_text(task_dir / "hello.miz", code)
        return Path("hello.miz")

    if prover == "pvs":
        if mode == "snippet":
            theory_name = "Hello"
            wrapped = (
                f"{theory_name}: THEORY\n"
                "BEGIN\n\n"
                f"{code}\n\n"
                f"END {theory_name}\n"
            )
        else:
            theory_name = _pvs_theory_name(code)
            wrapped = code
        target = Path(f"{theory_name}.pvs")
        _write_text(task_dir / target, wrapped)
        return target

    raise NotImplementedError(f"unsupported prover: {prover}")
