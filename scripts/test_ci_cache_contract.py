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

    def test_pr_full_oai_cold_rebuild_is_forbidden(self):
        problems = self.check_text(
            "on: pull_request:\nrepository: openai/math\n"
            "uses: ./.github/actions/lean-setup\n"
            "uses: ./.github/actions/oai-434-shared-cache\n"
            "lake build OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional\n"
        )
        self.assertTrue(any("complete-only" in problem for problem in problems))

    def test_heavy_oai_ci_no_longer_runs_on_every_alpoge_file(self):
        root = Path(__file__).resolve().parent.parent
        workflow_dir = root / ".github" / "workflows"
        for name in ("vf919-oai-certified-core-434.yml",
                     "vf919-openai-full-certified-seven-eighths-434.yml"):
            source = (workflow_dir / name).read_text()
            self.assertNotIn("      - 'RHLean/**'", source)
            self.assertIn("complete-only: 'true'", source)
            self.assertNotIn("lake build OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional", source)

    def test_amplification_concurrency_is_branch_scoped(self):
        root = Path(__file__).resolve().parent.parent
        source = (root / ".github" / "workflows" / "explicit-slot-amplification.yml").read_text()
        self.assertIn("group: explicit-amplification-${{ github.head_ref || github.ref_name }}", source)
        self.assertNotIn("group: explicit-amplification-${{ github.head_ref || github.ref_name }}-${{ github.event.pull_request.head.sha", source)
        self.assertNotIn("      - 'RHLean.lean'", source)
        self.assertIn("complete-only: 'true'", source)



    def test_legacy_openai_seven_eighths_workflows_are_manual_only(self):
        root = Path(__file__).resolve().parent.parent
        names = [
          "vf919-oai-certified-core-434.yml",
          "vf919-openai-full-certified-seven-eighths-434.yml",
          "explicit-slot-amplification.yml",
          "oai-compiled-cache-foundation-434.yml",
          "oai-gaussian-nns-typed-434.yml",
          "vf919-seven-eighths-signed-covariance.yml",
          "vf-mid-seven-eighths-analytic.yml",
          "vf919-total-mass-endpoint.yml",
          "quantitative-physical-tilt.yml"
]
        for name in names:
            path = root / ".github" / "workflows" / name
            content = path.read_text(encoding="utf-8")
            # CI logic remains preserved in these manual-only workflows.
            self.assertIn("on:\n", content, name)
            self.assertIn("  workflow_dispatch:", content, name)
            trigger = content.split("\non:\n", 1)[1].split("\npermissions:", 1)[0]
            for forbidden in ("  pull_request:", "  push:", "  schedule:"):
                self.assertNotIn(forbidden, trigger, name)


if __name__ == "__main__":
    unittest.main()
