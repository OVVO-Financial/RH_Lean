#!/usr/bin/env python3
"""Fast regression checks for the CI cache contract."""
from contextlib import redirect_stdout
import io
import os
import sys
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent / "ci"))
import check_lean_cache_contract as contract
from check_lean_cache_contract import audit, automatic_oai_jobs, yaml_block


def mixed_workflow(gate="", option_type="boolean", default="false", marker="openai/math"):
    """A native PR job beside an optional historical replay job."""
    return f"""on:
  pull_request:
  workflow_dispatch:
    inputs:
      run_original_oai:
        type: {option_type}
        default: {default}
jobs:
  native:
    runs-on: ubuntu-latest
    steps:
      - run: python3 native_check.py
  archive:
{gate}    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          repository: '{marker}'
"""


MANUAL_GATE = "    if: ${{ github.event_name == 'workflow_dispatch' && inputs.run_original_oai }}\n"


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
            "on: workflow_dispatch\nrepository: openai/math\nlake build Foo\n"
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
        self.assertTrue(any("explicit workflow_dispatch" in problem for problem in problems))

    def test_dispatch_trigger_alone_does_not_authorize_automatic_oai_job(self):
        self.assertEqual(["archive"], automatic_oai_jobs(mixed_workflow()))

    def test_dispatch_boolean_opt_in_allows_mixed_workflow(self):
        self.assertEqual([], automatic_oai_jobs(mixed_workflow(MANUAL_GATE)))

    def test_dispatch_event_without_boolean_opt_in_is_rejected(self):
        gate = "    if: ${{ github.event_name == 'workflow_dispatch' }}\n"
        self.assertEqual(["archive"], automatic_oai_jobs(mixed_workflow(gate)))

    def test_opt_in_must_be_a_default_false_boolean(self):
        for option_type, default in (("boolean", "true"), ("string", "'false'"),
                                     ("boolean", "'false'")):
            with self.subTest(option_type=option_type, default=default):
                self.assertEqual(["archive"], automatic_oai_jobs(
                    mixed_workflow(MANUAL_GATE, option_type, default)))

    def test_opt_in_cannot_allow_an_automatic_alternative(self):
        gate = MANUAL_GATE.replace(" && ", " || ")
        self.assertEqual(["archive"], automatic_oai_jobs(mixed_workflow(gate)))

    def test_gate_on_sibling_does_not_authorize_oai_job(self):
        source = mixed_workflow().replace("  native:\n", "  native:\n" + MANUAL_GATE)
        self.assertEqual(["archive"], automatic_oai_jobs(source))

    def test_checkout_quotes_spacing_and_case_do_not_bypass_policy(self):
        for repository in ("'openai/math'", '"openai/math"', '"OpenAI/Math"'):
            with self.subTest(repository=repository):
                source = mixed_workflow().replace("repository: 'openai/math'",
                                                  f"repository:    {repository}")
                self.assertEqual(["archive"], automatic_oai_jobs(source))

    def test_original_cache_or_build_without_checkout_is_detected(self):
        for marker in ("./.github/actions/oai-434-shared-cache",
                       "OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional",
                       "OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber"):
            with self.subTest(marker=marker):
                self.assertEqual(["archive"], automatic_oai_jobs(mixed_workflow(marker=marker)))

    def test_inline_automatic_triggers_are_rejected(self):
        source = mixed_workflow()
        source = "on: [push, pull_request]\n" + source[source.index("jobs:"):]
        self.assertEqual(["archive"], automatic_oai_jobs(source))

    def test_unknown_trigger_and_job_structure_fail_closed(self):
        for source in (
            mixed_workflow().replace("on:\n", "'on':\n", 1),
            mixed_workflow().replace("  archive:\n", "  'archive':\n"),
            "jobs: {archive: {uses: 'openai/math'}}\n",
            "repository: openai/math\n",
            "on:\n  workflow_dispatch:\n  'push':\njobs:\n  archive:\n    uses: openai/math\n",
        ):
            with self.subTest(source=source):
                self.assertTrue(automatic_oai_jobs(source))

    def test_manual_only_archive_remains_available(self):
        source = mixed_workflow().replace("  pull_request:\n", "")
        self.assertEqual([], automatic_oai_jobs(source))

    def test_reusable_archive_is_not_mistaken_for_manual_only(self):
        source = mixed_workflow().replace("  pull_request:\n", "  workflow_call:\n")
        self.assertEqual(["archive"], automatic_oai_jobs(source))

    def test_full_tree_audit_catches_unchanged_unsafe_workflow(self):
        with tempfile.TemporaryDirectory() as directory:
            workflow = Path(directory) / ".github/workflows/untouched.yml"
            workflow.parent.mkdir(parents=True)
            workflow.write_text(mixed_workflow())
            output = io.StringIO()
            previous = Path.cwd()
            try:
                os.chdir(directory)
                with patch.object(contract, "changed_workflows", return_value=[]), \
                     patch.object(sys, "argv", ["check", "--base", "main"]), \
                     redirect_stdout(output):
                    self.assertEqual(1, contract.main())
            finally:
                os.chdir(previous)
            self.assertIn("untouched.yml", output.getvalue())

    def test_every_original_oai_workflow_requires_manual_replay(self):
        root = Path(__file__).resolve().parent.parent
        paths = sorted((root / ".github/workflows").glob("*.y*ml"))
        self.assertTrue(paths)
        for path in paths:
            with self.subTest(workflow=path.name):
                self.assertEqual([], automatic_oai_jobs(path.read_text(encoding="utf-8")))

    def test_universal_keeps_native_gates_and_archives_fractional_replay(self):
        root = Path(__file__).resolve().parent.parent
        source = (root / ".github/workflows/universal-envelope-law.yml").read_text()
        jobs = yaml_block(source, "jobs")
        for name in ("numerical-smoke", "core-proof", "kernel-proof"):
            body = yaml_block(jobs, name, 2)
            self.assertTrue(body, name)
            self.assertNotIn("run_original_oai", body, name)
        self.assertIn(MANUAL_GATE.strip(), yaml_block(jobs, "fractional-owner-proof", 2))
        self.assertIn("group: universal-envelope-${{ github.head_ref || github.ref_name }}", source)
        self.assertNotIn("head.sha", yaml_block(source, "concurrency"))
        triggers = yaml_block(source, "on")
        self.assertIn("'!research/UNIVERSAL_ENVELOPE_OWNER_FRACTIONAL.lean'", triggers)
        self.assertIn("'!research/UNIVERSAL_ENVELOPE_FRACTIONAL_ACCEPTANCE.lean'", triggers)
        self.assertNotIn("VF919FractionalOwnerContraction.lean", triggers)
        self.assertNotIn("audit_euler_fractional_axioms.py", triggers)
        self.assertNotIn(".github/actions/oai-434-shared-cache", triggers)

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
