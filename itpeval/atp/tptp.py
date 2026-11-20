"""Snapshot a TPTP problem and resolve its file dependencies."""

from __future__ import annotations

import re
from graphlib import CycleError, TopologicalSorter
from pathlib import Path

from itpeval.core.types import logical_path
from itpeval.corpus.storage import digest


_TOKENS = re.compile(
    r"%[^\n]*|/\*[\s\S]*?\*/|'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\"|[()\[\]{}.,]|[^\s()\[\]{}.,'%\"]+"
)


def _includes(text: str):
    """Locate the filename of each top-level include directive."""
    tokens = (token for token in _TOKENS.finditer(text)
              if not token.group().startswith(("%", "/*")))
    depth = 0
    new_statement = True
    for token in tokens:
        word = token.group()
        if new_statement and word == "include":
            opener, filename = next(tokens, None), next(tokens, None)
            if opener is None or opener.group() != "(" or filename is None:
                raise ValueError("invalid TPTP include directive")
            name = filename.group()
            if name.startswith("'") and name.endswith("'"):
                name = name[1:-1]
            elif not re.fullmatch(r"[a-z][A-Za-z_0-9]*", name):
                raise ValueError("expected a local filename in the TPTP include directive")
            yield logical_path(name), filename.span()
            depth = 1
            new_statement = False
            continue
        if word in ("(", "[", "{"):
            depth += 1
        if word in (")", "]", "}"):
            depth -= 1
        new_statement = depth == 0 and word == "."


def _read(root: Path, path: Path) -> tuple[Path, bytes]:
    target = path.resolve(strict=True)
    if not target.is_relative_to(root) or not target.is_file():
        raise ValueError(f"TPTP source must be a regular file inside the selected root: {path}")
    return path.relative_to(root), target.read_bytes()


def _resolve(root, path, name):
    candidates = {root / path.parent / name, root / name}
    matches = [candidate for candidate in sorted(candidates) if candidate.is_file()]
    if not matches:
        raise ValueError(f"missing TPTP include {name!r} in {path}")
    if len(matches) > 1:
        raise ValueError(f"ambiguous TPTP include {name!r} in {path}")
    if not matches[0].resolve(strict=True).is_relative_to(root):
        raise ValueError(f"TPTP include resolves outside its selected root: {name!r}")
    return matches[0].relative_to(root)


def stage_problem(problem: Path, tptp_root: Path | None, workspace: Path):
    """Stage immutable input bytes with portable, unambiguous include names.

    Return the logical and staged entrypoints and hashes of the two versions
    of each staged file. Formula text and include selection lists stay intact.
    """
    path = Path(problem).expanduser()
    # Normalize parent aliases without conflating a source symlink with its name.
    absolute = path.parent.resolve(strict=True) / path.name
    root = Path(tptp_root).expanduser().resolve(strict=True) if tptp_root is not None else absolute.parent
    if not absolute.is_relative_to(root):
        raise ValueError("TPTP problem must be inside its selected root")
    entrypoint, raw = _read(root, absolute)
    pending = {entrypoint: raw}
    sources = {}
    graph = {}
    while pending:
        path, raw = pending.popitem()
        text = raw.decode("utf-8")
        includes = [(_resolve(root, path, name), span) for name, span in _includes(text)]
        sources[path] = raw, text, includes
        graph[path] = tuple(target for target, _ in includes)
        for target, _ in includes:
            if target not in sources and target not in pending:
                _, included = _read(root, root / target)
                pending[target] = included
    try:
        order = tuple(TopologicalSorter(graph).static_order())
    except CycleError as error:
        raise ValueError("cyclic TPTP includes") from error

    staged_names = {path: f"input-{index}.p" for index, path in enumerate(sorted(order))}
    receipts = []
    for path in sorted(sources):
        raw, text, includes = sources[path]
        for target, (start, end) in reversed(includes):
            text = text[:start] + f"'{staged_names[target]}'" + text[end:]
        staged = text.encode("utf-8")
        name = staged_names[path]
        (workspace / name).write_bytes(staged)
        receipts.append((path.as_posix(), digest(raw), name, digest(staged)))
    return entrypoint.as_posix(), staged_names[entrypoint], tuple(receipts)
