import json
import unittest

from check_native_rh_export import check_export


class TerminalExportTests(unittest.TestCase):
    def setUp(self):
        self.prefix = [
            {"in": 1, "str": {"pre": 0, "str": "native_riemannHypothesis"}},
            {"in": 2, "str": {"pre": 0, "str": "RiemannHypothesis"}},
            {"ie": 3, "const": {"name": 2, "us": []}},
        ]
        self.theorem = {"name": 1, "type": 3, "value": 8, "levelParams": []}

    def check(self, rows):
        check_export(map(json.dumps, rows))

    def test_literal_root(self):
        self.check([*self.prefix, {"thm": self.theorem}])

    def test_rejects_missing_duplicate_and_non_theorem(self):
        for tail in ([], [{"def": self.theorem}], [{"thm": self.theorem}] * 2):
            with self.subTest(tail=tail), self.assertRaises(ValueError):
                self.check(self.prefix + tail)

    def test_rejects_other_types_dependencies_and_binders(self):
        for changed in ({"name": 2}, {"type": 4}, {"value": None},
                        {"value": False}, {"levelParams": [9]}):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.check([*self.prefix, {"thm": {**self.theorem, **changed}}])

    def test_rejects_nested_name_and_universe_application(self):
        for ix, row in ((0, {"in": 1, "str": {"pre": 5, "str": "native_riemannHypothesis"}}),
                        (1, {"in": 2, "str": {"pre": 5, "str": "RiemannHypothesis"}}),
                        (2, {"ie": 3, "const": {"name": 2, "us": [0]}})):
            with self.subTest(ix=ix), self.assertRaises(ValueError):
                prefix = self.prefix.copy()
                prefix[ix] = row
                self.check([*prefix, {"thm": self.theorem}])
