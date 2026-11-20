"""Library-dependent artifact checks sourced from the ten pinned extraction projects."""
from itpeval.backends.registry import ROOT
from itpeval.core.types import Artifact, Budgets, TaskSpec
from itpeval.environments import prepare_project


# Each mutation changes a native source so the checker must reject it.
CASES = {
    "lean4": ("Client.lean", "Counts.next_index_zero", "False.elim"),
    "rocq": ("Client.v", "apply M.identity_eq.", "exact I."),
    "isabelle": ("Sample.thy", "by (simp add: twice_def)", "by (rule FalseE)"),
    "hol-light": ("sample.ml", "DISCH `p:bool` under_assumption", "DISCH `p:bool` (REFL 3)"),
    "hol4": ("sampleScript.sml", "simp[twice_def]", "NO_TAC"),
    "acl2": ("events.lisp", "(equal (my-id x) x)", "(equal t nil)"),
    "agda": ("Client.agda", "first = idNat zero", "first = Set"),
    "metamath": ("client.mm", "( pair-dv ) ABC", "( pair-dv ) ABA"),
    "mizar": ("sample.miz", "holds x = x by Th1", "holds x <> x by Th1"),
    "pvs": ("sample.pvs", "IMPORTING bridge, prelude_aux[int]", "IMPORTING MissingTheory, prelude_aux[int]"),
}
EXTENSIONS = {".lean", ".v", ".thy", ".ml", ".sml", ".lisp", ".agda", ".mm", ".miz", ".pvs"}


def prepare(prover, prefix, cache):
    project = ROOT / "tests/fixtures/projects" / prover / "library"
    libraries = {"local_modules": project} if prover == "lean4" else {}
    prepared = prepare_project(prover, project, prefix=prefix, cache=cache, libraries=libraries)
    entry, good, bad = CASES[prover]
    files = {p.relative_to(prepared.project).as_posix(): p.read_bytes()
             for p in prepared.project.rglob("*") if p.is_file() and
             (p.suffix in EXTENSIONS or p.name in ("ROOT", "Holmakefile"))}
    dependencies = ()
    transformations = []
    if prover == "lean4":
        dependencies = ("Counts.lean", "Mathlib/Tactic/Linter/DirectoryDependency.lean")
    if prover == "rocq":
        dependencies = ("StrictProp.v", "Library.v")
        for source in (entry, *dependencies):
            files[source] = files[source].replace(b"From ITPProject Require Import", b"Require Import")
        transformations.append("mapped the locked root ITPProject to the compiler working directory")
    if prover == "hol-light":
        files[entry] = b"load_path := Filename.dirname __FILE__ :: !load_path;;\n" + files[entry]
        transformations.append("added the entrypoint directory to the local HOL Light load path")
    if prover == "acl2":
        files["events.lsp"] = files.pop(entry)
        entry = "events.lsp"
        transformations.append("staged the ACL2 book with the shell adapter's .lsp extension")
    tasks = []
    for candidate in (good, bad):
        data = files[entry]
        if data.count(good.encode()) != 1:
            raise ValueError(f"ambiguous library benchmark mutation for {prover}")
        artifact = Artifact.from_files(entry, {**files, entry: data.replace(good.encode(), candidate.encode())},
                                       tuple(transformations))
        tasks.append(TaskSpec(prover, prepared.environment_id,
                              "statement" if prover == "pvs" else "check_artifact", artifact,
                              budgets=Budgets(timeout_s=360, max_log_bytes=64*1024),
                              dependency_sources=dependencies))
    return prepared, *tasks
