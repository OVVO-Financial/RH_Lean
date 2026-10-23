#!/usr/bin/env python3
"""Fast regression checks for the CI cache contract."""
import sys
import tempfile
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "ci"))
from check_lean_cache_contract import audit


class CacheContractTest(unittest.TestCase):
    def check_text(self, body):
        with tempfile.TemporaryDirectory() as d:
            file = Path(d) / "test.yml"
            file.write_text(body)
            return audit(file)

    def test_mixed_uncached_fails(self):
        problems = self.check_text(
            "repository: openai/math\nlake build Foo\n"
            "python3 scripts/check_shared_lean_packages.py . oai-upstream/lean mathlib\n"
        )
        self.assertTrue(any("compiled DAG" in item for item in problems))
        self.assertTrue(any("unpatched-PNT" in item for item in problems))

    def test_mixed_pinned_passes(self):
        self.assertEqual([], self.check_text(
            "repository: openai/math\nlake build Foo\n"
            "python3 scripts/check_shared_lean_packages.py . oai-upstream/lean mathlib\n"
            "uses: ./.github/actions/lean-setup\n"
            "uses: ./.github/actions/oai-434-shared-cache\n"
        ))

    def test_new_native_pinned_passes(self):
        self.assertEqual([], self.check_text(
            "uses: ./.github/actions/lean-setup\n"
            "uses: ./.github/actions/research-compile\n"
        ))

    def test_new_native_ad_hoc_fails(self):
        self.assertTrue(self.check_text("lake build RHLean\n"))

    def test_python_only_not_lean(self):
        self.assertEqual([], self.check_text("run: python3 foo.py\n"))


if __name__ == "__main__":
    unittest.main()
