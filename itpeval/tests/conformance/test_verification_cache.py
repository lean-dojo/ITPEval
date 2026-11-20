"""Exercise reuse and invalidation with a real Metamath proof."""
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project
from itpeval.environments import prepare_project
from itpeval.itp import _default_prefix
from itpeval.verification.cache import verify_cached


@unittest.skipUnless(os.environ.get("ITPEVAL_REAL_METAMATH"), "requires native Metamath")
class VerificationCache(unittest.TestCase):
    def test_hits_separate_native_work_and_respect_task_policy(self):
        with tempfile.TemporaryDirectory() as tmp:
            cache = Path(tmp)
            prepared = prepare_project("metamath", curated_project("metamath"), prefix=_default_prefix(), cache=cache)
            task = build_task(prepared)
            candidate = task.allowed_edits[0]
            first = verify_cached(task, candidate, prepared=prepared, cache=cache)
            second = verify_cached(task, candidate, prepared=prepared, cache=cache)
            self.assertTrue(first.evidence.task_success)
            self.assertFalse(first.cache_hit)
            self.assertTrue(second.cache_hit)
            self.assertEqual(second.evidence, first.evidence)
            changed = replace(task, budgets=replace(task.budgets, timeout_s=task.budgets.timeout_s + 1))
            revised = verify_cached(changed, candidate, prepared=prepared, cache=cache)
            self.assertFalse(revised.cache_hit)
            self.assertNotEqual(first.key, revised.key)
            for _ in range(2):
                invalid = verify_cached(task, "admit", prepared=prepared, cache=cache)
                self.assertFalse(invalid.cache_hit)
                self.assertFalse(invalid.evidence.task_success)
