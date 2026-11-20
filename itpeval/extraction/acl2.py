"""Inspect public book events, enabled theories and rule use in the admitted ACL2 world."""

import json
import re
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.backends.acl2.syntax import _HEAD, _forms
from itpeval.corpus.storage import encode

_EVENTS = {"DEFUN", "DEFTHM", "DEFTHMD", "DEFAXIOM", "DEFUND", "DEFCONST"}


@dataclass(frozen=True)
class Event:
    path: str
    name: str
    start: int
    end: int
    imports: tuple[str, ...]


def extract(ctx, entrypoint):
    if ctx.prepared.spec.options or ctx.prepared.library_paths:
        raise ValueError("use the configured ACL2 installation and its certified system books")
    # A terminal :q belongs to the CLI driver. Keep the inspected world open.
    raw = re.sub(rb"(?im)^\s*:q[ \t]*\Z", b"", ctx.source(entrypoint).rstrip())
    local, imported, imports = [], [], []
    for start, end, form in _forms(raw):
        head = _HEAD.match(form)
        if head is None:
            ctx.notes["skipped"].append(f"{entrypoint}:{start} (unsupported event)")
            continue
        event, string, symbol = (word.decode("ascii").upper() if word else "" for word in head.groups())
        if event == "IN-PACKAGE":
            if string != "ACL2":
                raise ValueError("the current extractor requires package ACL2")
        elif event == "INCLUDE-BOOK":
            book = head[2].decode()
            imports.append(book)
            relative = "books/" + book + ".lisp"
            if re.search(rb":dir\s+:system\b", form, re.IGNORECASE) and (ctx.root / relative).is_file():
                installed = list((ctx.prepared.prefix / "acl2/src").glob("acl2-*/" + relative))
                source = ctx.source(relative)
                if len(installed) != 1 or installed[0].read_bytes() != source:
                    raise ValueError(f"locked project copy differs from system book {book}")
                for a, b, item in _forms(source, sections=True):
                    match = _HEAD.match(item)
                    if match and match[1].decode().upper() in _EVENTS and match[3]:
                        imported.append(Event(relative, match[3].decode().upper(), a, b, ()))
                ctx.notes["succeeded"].append(relative)
                ctx.notes["skipped"].append(f"{relative}: macro-generated and local events")
            ctx.edge(entrypoint, "import", book, ctx.sources.get(relative))
        elif event in _EVENTS and symbol:
            local.append(Event(entrypoint, symbol, start, end, tuple(imports)))
        else:
            ctx.notes["skipped"].append(f"{entrypoint}:{start} ({event})")

    # Query the enabled theory immediately before an event and its proof rules
    # immediately afterwards. Both properties can change at the next command.
    native_input = Path(entrypoint).with_name("itpeval-extraction-events.lisp")
    with (ctx.root / native_input).open("xb") as annotated:
        position = 0
        for i, event in enumerate(local):
            annotated.write(raw[position:event.start])
            annotated.write((f'\n(cw "ITP_THEORY_{i}~%~x0~%ITP_THEORY_END~%" '
                             '(current-theory-fn :here (w state)))\n').encode())
            annotated.write(raw[event.start:event.end])
            annotated.write((f'\n(cw "ITP_RULES_{i}~%~x0~%ITP_RULES_END~%" '
                             "(get-event-data 'rules state))\n").encode())
            position = event.end
        annotated.write(raw[position:])
    commands = ['(in-package "ACL2")', f'(ld {json.dumps(str(native_input))} :ld-error-action :error)']
    events = imported + local
    for i, event in enumerate(events):
        sym = "'" + event.name
        calls = [f"(get-event {sym} (w state))", f"(getpropc {sym} 'theorem nil (w state))",
                 f"(getpropc {sym} 'unnormalized-body nil (w state))", f"(guard {sym} nil (w state))",
                 f"(symbol-class {sym} (w state))", f"(getpropc {sym} 'classes nil (w state))"]
        commands.append(f'(cw "ITP_BEGIN_{i}~%~x0~%ITP_FIELD~%~x1~%ITP_FIELD~%~x2~%'
                        f'ITP_FIELD~%~x3~%ITP_FIELD~%~x4~%ITP_FIELD~%~x5~%ITP_END~%" '
                        + " ".join(calls) + ")")
    commands += ['(cw "ITPEVAL_WORLD_DONE~%")', ':q']
    with TemporaryDirectory(dir=ctx.root.parent) as tmp:
        driver = Path(tmp) / "inspect.lsp"
        driver.write_text("\n".join(commands) + "\n")
        stdout, _ = ctx.run([ctx.prepared.prefix / "acl2/bin/acl2"], stdin_path=driver)
    if "ITPEVAL_WORLD_DONE" not in stdout or re.search(r"ACL2 Error|\*+ FAILED \*+|HARD ACL2 ERROR", stdout):
        raise ValueError(f"ACL2 rejected event replay or world queries: {stdout[-1900:]}")

    def output(tag, idx):
        m = re.search(rf"ITP_{tag}_{idx}\n(.*?)\nITP_{'END' if tag == 'BEGIN' else tag+'_END'}\n", stdout, re.DOTALL)
        if m is None:
            raise ValueError(f"missing ACL2 {tag} observation for {idx}")
        return m[1]

    known = {}
    for i, event in enumerate(events):
        form, formula, body, guard, cls, classes = output("BEGIN", i).split("\nITP_FIELD\n")
        kind = re.match(r"\(([\w-]+)\s+", form)
        if kind is None:
            raise ValueError(f"no admitted world event for {event.name}")
        detail = {"event": form, "theorem": formula, "body": body, "guard": guard,
                  "symbol_class": cls, "rule_classes": classes}
        if event.path == entrypoint:
            before = output("THEORY", i - len(imported))
            detail["enabled_theory_blob"] = ctx.evidence(before.encode())
            detail["used_runes"] = output("RULES", i - len(imported))
        visible = [key for previous, key in known.values() if previous.path == event.path or
                   (previous.path.removeprefix("books/").removesuffix(".lisp") in event.imports)]
        key = ctx.declare(event.path, event.name, kind[1].lower(), form if formula == "NIL" else formula,
                          event.start, event.end, ctx.context(event.path, visible=visible, imports=event.imports),
                          "admitted_event", evidence=[ctx.evidence(encode(detail))])
        for rule, symbol in re.findall(r"\(:(REWRITE|DEFINITION|LINEAR|TYPE-PRESCRIPTION)\s+([\w+:*/.-]+)",
                                       detail.get("used_runes", "")):
            relation = "rewrite_rule_used" if rule == "REWRITE" else "proof_used_premise"
            ctx.edge(key, relation, symbol, known[symbol][1] if symbol in known else None)
        known[event.name] = event, key
    ctx.notes["succeeded"].append(entrypoint)
    ctx.availability.update({k: "observed" for k in ("names", "kinds", "statements", "imports")})
    ctx.availability.update(context="reconstructed", source_mapping="reconstructed", rewrite_rules="observed",
                            enabled_rules="observed", proof_used_premises="observed")
