"""Check search against truth-table semantics and exercise the independent kernel."""
from itertools import combinations, product
import unittest

from kernel import check
from sprig import prove, SearchLimit


class SprigTests(unittest.TestCase):
    def test_search_agrees_with_truth_tables(self):
        # All non-tautological clauses on two atoms, including the empty clause.
        clauses = [list(filter(None, pair)) for pair in product(("", "P", "~P"), ("", "Q", "~Q"))]
        worlds = [{"P": p, "Q": q} for p, q in product((False, True), repeat=2)]

        def holds(row, world):
            return any(world[lit.lstrip("~")] != lit.startswith("~") for lit in row)

        for count in range(4):
            for premises in combinations(clauses, count):
                for goal in clauses + [["P", "~P"]]:
                    problem = {"premises": list(premises), "goal": goal}
                    entailed = all(holds(goal, w) for w in worlds if all(holds(c, w) for c in premises))
                    certificate = prove(problem)
                    self.assertEqual(certificate is not None, entailed, problem)
                    if certificate is not None:
                        check(problem, certificate)

    def test_checker_rejects_changed_target_and_invalid_inferences(self):
        problem = {"premises": [["P"]], "goal": ["P"]}
        certificate = prove(problem)
        with self.assertRaises(ValueError):
            check({**problem, "goal": ["Q"]}, certificate)
        for step in ([0, 1, "Q"], [-1, 1, "P"], [True, 1, "P"], [2, 1, "P"], [1, 0, "P"]):
            with self.subTest(step=step), self.assertRaises(ValueError):
                check(problem, {"steps": [step], "conclusion": 2})
        with self.assertRaises(ValueError):
            check(problem, {"steps": [], "conclusion": 0})

    def test_budget_exhaustion_is_distinct_from_saturation(self):
        with self.assertRaises(SearchLimit):
            prove({"premises": [["P"]], "goal": ["P"]}, max_inferences=0)
        self.assertIsNone(prove({"premises": [], "goal": ["P"]}, max_inferences=0))


if __name__ == "__main__":
    unittest.main()
