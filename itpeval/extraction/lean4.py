"""Inspect the elaborated environment produced by freshly compiled project modules."""

import json
import os
import re
from pathlib import Path
from tempfile import TemporaryDirectory

from itpeval.corpus.storage import encode

_DRIVER = """
open Lean Meta Elab Command

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def theoremProofRange? (env : Environment) (src : String) (fm : FileMap)
    (r : DeclarationRange) : Option (Nat × Nat) := do
  let start := fm.ofPosition r.pos
  let stop := fm.ofPosition r.endPos
  let cmd ← (Parser.runParserCategory env `command (String.Pos.Raw.extract src start stop)).toOption
  let theoremNode ← cmd.find? (·.isOfKind `Lean.Parser.Command.theorem)
  let valNode ← theoremNode.getArgs.find? (·.isOfKind `Lean.Parser.Command.declValSimple)
  let proof := valNode[1]
  let first ← proof.getPos?
  let last ← proof.getTailPos?
  return (start.byteIdx + first.byteIdx, start.byteIdx + last.byteIdx)

run_cmd liftTermElabM do
  let env ← getEnv
  let some idx := env.getModuleIdx? `MODULE | throwError "missing project module"
  let src ← IO.FS.readFile SOURCE_FILE
  let fm := src.toFileMap
  let md := env.header.moduleData[idx.toNat]!
  IO.println ("IMPORTS " ++ (toJson (md.imports.map fun i ↦ toString i.module)).compress)
  for n in md.constNames do
    let some ci := env.find? n | throwError "missing declaration {n}"
    let some ranges ← findDeclarationRanges? n | continue
    let r := ranges.range
    let type ← ppExpr ci.type
    let valueRefs := (ci.value? true).map fun e ↦ e.getUsedConstants.map toString
    let row := Json.mkObj [
      ("name", toJson n.toString), ("private", toJson (isPrivateName n)),
      ("proofRegion", toJson (if ci.isTheorem then theoremProofRange? env src fm r else none)),
      ("kind", toJson (declarationKind ci)),
      ("type", toJson type.pretty), ("typeTerm", toJson (reprStr ci.type)), ("start", toJson (r.pos.line, r.pos.column)),
      ("end", toJson (r.endPos.line, r.endPos.column)), ("refs", toJson valueRefs),
      ("typeRefs", toJson (ci.type.getUsedConstants.map toString)),
      ("axioms", toJson ((← collectAxioms n).map toString))]
    IO.println ("DECL " ++ row.compress)
"""


def _offset(lines, position):
    line, column = position
    return len(("".join(lines[:line - 1]) + lines[line - 1][:column]).encode())


def extract(ctx, entrypoint):
    lean = ctx.prepared.prefix / "lean4/bin/lean"
    env = {"LEAN_PATH": str(ctx.root), "LEAN_SRC_PATH": str(ctx.root)}
    # Dependencies outside the project may be supplied only by locked libraries.
    for _, path in ctx.prepared.library_paths:
        base = Path(path)
        lib = base / ".lake/build/lib/lean"
        env["LEAN_PATH"] += os.pathsep + str(lib if lib.is_dir() else base)
        env["LEAN_SRC_PATH"] += os.pathsep + str(base)
    options = ["-D" + name + "=" + value for name, value in ctx.prepared.spec.options]
    ids, visited, visible, references = {}, set(), {}, []
    header_script = """import Lean
def main (args : List String) : IO Unit := do
  for path in args do
    let (imports, _, errors) ← Lean.Elab.parseImports (← IO.FS.readFile path) path
    if errors.hasErrors then throw (IO.userError "invalid module header")
    for i in imports do IO.println i.module
"""

    def visit(path):
        if path in visited:
            return
        visited.add(path)
        raw = ctx.source(path)
        lines = raw.decode().splitlines(keepends=True)
        with TemporaryDirectory(dir=ctx.root) as tmp:
            header = Path(tmp) / "Imports.lean"
            header.write_text(header_script)
            deps, _ = ctx.run([lean, "--run", header, path], env=env)
        imported = []
        for name in dict.fromkeys(deps.splitlines()):
            dep = name.replace(".", "/") + ".lean"
            if (ctx.root / dep).is_file():
                visit(dep)
                imported.append(dep)
        ctx.run([lean, *options, "-o", Path(path).with_suffix(".olean"), path], env=env)
        name = ".".join(Path(path).with_suffix("").parts)
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part) for part in name.split(".")):
            raise ValueError(f"unsupported Lean module path {path}")
        with TemporaryDirectory(dir=ctx.root) as tmp:
            driver = Path(tmp) / "Inspect.lean"
            driver.write_text("import Lean\nimport " + name + "\n" + _DRIVER.replace("MODULE", name).replace("SOURCE_FILE", json.dumps(path)))
            stdout, _ = ctx.run([lean, *options, driver], env=env)
        imports, rows = None, []
        for line in stdout.splitlines():
            if line.startswith("IMPORTS "):
                imports = tuple(dict.fromkeys(json.loads(line[8:])))
            elif line.startswith("DECL "):
                rows.append(json.loads(line[5:]))
        if imports is None:
            raise ValueError("Lean inspection produced no module header")
        for mod in imports:
            target = mod.replace(".", "/") + ".lean"
            ctx.edge(path, "import", mod, ctx.sources.get(target))
        local = list(dict.fromkeys(d for dep in imported for d in visible[dep]))
        public = list(local)
        # Declarations produced by the same source command share its incoming scope.
        group_start = None
        context = None
        for row in sorted(rows, key=lambda r: (r["start"], r["name"])):
            if row["start"] != group_start:
                group_start = row["start"]
                context = ctx.context(path, imports=imports, visible=local)
            start, end = _offset(lines, row["start"]), _offset(lines, row["end"])
            kind = row["kind"]
            status = "admission_dependency" if "sorryAx" in row["axioms"] else (
                "axiom" if kind == "axiom" else "kernel_checked")
            evidence = ctx.evidence(encode(row))
            key = ctx.declare(path, row["name"], kind, row["type"], start, end, context,
                              status, evidence=[evidence])
            local.append(key)
            if not row["private"]:
                public.append(key)
            if row["proofRegion"] is not None:
                ctx.structures[key] = ctx.evidence(encode({"format": "lean.proof-region.v1",
                                                          "source_sha256": ctx.sources[path],
                                                          "start_byte": row["proofRegion"][0],
                                                          "end_byte": row["proofRegion"][1]}))
            ids[row["name"]] = key
            for ref in sorted(row["typeRefs"]):
                references.append((key, "statement_reference", ref))
            relation = "proof_used_premise" if kind == "theorem" else "definition_reference"
            for ref in sorted(row["refs"] or []):
                references.append((key, relation, ref))
        visible[path] = public
        ctx.notes["succeeded"].append(path)

    visit(entrypoint)
    for key, relation, ref in references:
        ctx.edge(key, relation, ref, ids.get(ref))
    ctx.availability.update({k: "observed" for k in ("names", "kinds", "source_mapping", "statements",
                             "imports", "statement_references", "proof_used_premises", "definition_references", "term_trees", "proof_regions")})
    ctx.availability["context"] = "reconstructed"
