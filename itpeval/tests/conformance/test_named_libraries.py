"""Verify against inputs supplied outside the project in Rocq and Agda."""
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from itpeval.core.types import Artifact, TaskSpec
from itpeval.environments import prepare_project
from itpeval.verification.service import verify


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_PREFIX"), "requires the real Rocq and Agda toolchains")
class ExternalLibraries(unittest.TestCase):
    def test_native_check_uses_the_locked_dependency(self):
        prefix = Path(os.environ["ITPEVAL_REAL_PREFIX"]).resolve()
        for prover in ("rocq", "agda"):
            with self.subTest(prover), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                library = root / "library"
                project = root / "project"
                project.mkdir()
                library.mkdir()
                if prover == "rocq":
                    (library / "Base.v").write_text("Definition answer : nat := 2.\n")
                    subprocess.run([prefix / "rocq/bin/rocq", "compile", "-Q", ".", "Aux", "Base.v"],
                                   cwd=library, check=True)
                    entry, binding = "Goal.v", "Base.vo"
                    label = "Aux.Base"
                    text = "From Aux Require Import Base.\nLemma checked : answer = 2. Proof. reflexivity. Qed.\n"
                else:
                    (library / "Base.agda").write_text(
                        "module Base where\nopen import Agda.Builtin.Bool\nanswer : Bool\nanswer = true\n")
                    entry, binding, label = "Goal.agda", "Base.agda", "Base"
                    text = ("module Goal where\nopen import Base\nopen import Agda.Builtin.Bool\n"
                            "open import Agda.Builtin.Equality\nchecked : answer ≡ true\nchecked = refl\n")
                (project / entry).write_text(text)
                env = prepare_project(prover, project, prefix=prefix, cache=root / "cache",
                                      libraries={"Aux": library}, imports=(label,),
                                      import_bindings={label: ("library/Aux", binding)})
                artifact = Artifact.from_files(entry, {entry: text.encode()})
                result = verify(TaskSpec(prover, env.environment_id, "check_artifact", artifact), prepared=env)
                self.assertIs(result.task_success, True, result.stderr)
                env.validate()
