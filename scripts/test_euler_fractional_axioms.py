#!/usr/bin/env python3
"""Synthetic audit regressions; these tests never execute Lean locally."""

import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import audit_euler_fractional_axioms as audit


def record(name, values="propext, Classical.choice, Quot.sound"):
    return f"'{name}' depends on axioms: [{values}]\n"


def complete_log():
    return "".join(record(name) for name in audit.EXPECTED)


class LogTests(unittest.TestCase):
    def test_complete_standard_output(self):
        self.assertEqual(set(audit.audit_log(complete_log())), set(audit.EXPECTED))

    def test_multiline_standard_output(self):
        text = complete_log().replace("propext, Classical.choice", "propext,\n Classical.choice")
        self.assertEqual(len(audit.audit_log(text)), 8)

    def test_no_axioms_and_empty_list(self):
        text = complete_log().replace(record(audit.EXPECTED[0]),
            f"'{audit.EXPECTED[0]}' does not depend on any axioms\n")
        text = text.replace(record(audit.EXPECTED[1]), record(audit.EXPECTED[1], ""))
        result = audit.audit_log(text)
        self.assertEqual(result[audit.EXPECTED[0]], [])
        self.assertEqual(result[audit.EXPECTED[1]], [])

    def test_expected_type_output_is_allowed(self):
        text = f"{audit.EXPECTED[0]} (R : Nat) :\n  True\n" + complete_log()
        self.assertEqual(len(audit.audit_log(text)), 8)

    def test_empty_missing_duplicate_and_unexpected(self):
        cases = ["", "PASS standard axioms only\n",
            complete_log().replace(record(audit.EXPECTED[0]), ""),
            complete_log() + record(audit.EXPECTED[0]),
            complete_log() + record("Unrequested.theorem"),
            complete_log().replace(audit.EXPECTED[0], "Unrequested.theorem")]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(audit.AuditError):
                audit.audit_log(text)

    def test_diagnostics_rejected_even_with_all_records(self):
        for diagnostic in ["error: failure", "warning: unused variable",
                "audit.lean:2:14: error(lean.unknownIdentifier): Unknown constant",
                "\x1b[31merror:\x1b[0m failure"]:
            with self.subTest(diagnostic=diagnostic), self.assertRaises(audit.AuditError):
                audit.audit_log(complete_log() + diagnostic + "\n")

    def test_forbidden_axioms_single_and_multiline(self):
        for bad in ["sorryAx", "Lean.ofReduceBool", "Invented.bound"]:
            for separator in [" ", "\n "]:
                text = complete_log().replace("propext,", f"propext,{separator}{bad},", 1)
                with self.subTest(bad=bad, separator=separator), self.assertRaises(audit.AuditError):
                    audit.audit_log(text)

    def test_malformed_lists(self):
        for bad in ["[propext", "[propext] trailing", "[propext,,Quot.sound]",
                    "[propext,propext]", "[propext,[Classical.choice]]"]:
            text = complete_log().replace("[propext, Classical.choice, Quot.sound]", bad, 1)
            with self.subTest(bad=bad), self.assertRaises(audit.AuditError):
                audit.audit_log(text)

    def test_reject_empty_or_duplicate_expectations(self):
        for expected in [(), (audit.EXPECTED[0], audit.EXPECTED[0])]:
            with self.subTest(expected=expected), self.assertRaises(audit.AuditError):
                audit.audit_log(complete_log(), expected)

    def test_original_eight_unknown_constants_cannot_pass(self):
        text = "".join(f"audit.lean:{i + 2}:14: error(lean.unknownIdentifier): "
            f"Unknown constant `{name}`\n" for i, name in enumerate(audit.EXPECTED))
        with self.assertRaises(audit.AuditError):
            audit.audit_log(text + "PASS standard axioms only\n")

    def test_original_multiline_nonstandard_blind_spot(self):
        text = complete_log().replace("propext, Classical.choice, Quot.sound",
            "propext,\n Invented.bound, Quot.sound")
        with self.assertRaises(audit.AuditError):
            audit.audit_log(text)


class RunnerTests(unittest.TestCase):
    def test_harness_import_and_exact_commands(self):
        source = audit.audit_source()
        self.assertEqual(source.splitlines()[0], f"import \u00ab{audit.MODULE}\u00bb")
        for command in ["#check", "#print axioms"]:
            self.assertEqual([line.removeprefix(command + " ") for line in source.splitlines()
                if line.startswith(command + " ")], list(audit.EXPECTED))

    def run_fake(self, status, text, directory):
        with patch.object(audit.subprocess, "run", return_value=
                subprocess.CompletedProcess([], status, text)) as runner:
            with contextlib.redirect_stdout(io.StringIO()):
                result = audit.run_audit(directory)
        args, kwargs = runner.call_args
        self.assertIn("-DwarningAsError=true", args[0])
        self.assertNotIn("shell", kwargs)
        self.assertEqual(kwargs["stderr"], subprocess.STDOUT)
        return result

    def test_success_writes_real_evidence(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            self.assertEqual(len(self.run_fake(0, complete_log(), directory)), 8)
            self.assertEqual((directory / "audit.log").read_text(), complete_log())
            self.assertEqual((directory / "audit.lean").read_text(), audit.audit_source())

    def test_nonzero_exit_cannot_hide_behind_valid_output(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(audit.AuditError, "status 7"):
                self.run_fake(7, complete_log(), Path(temp))
            self.assertEqual((Path(temp) / "audit.log").read_text(), complete_log())

    def test_zero_exit_still_requires_valid_output(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(audit.AuditError):
                self.run_fake(0, "", Path(temp))

    def test_cli_failures_have_nonzero_status(self):
        for failure in [audit.AuditError("missing result"), OSError("missing compiler")]:
            with self.subTest(failure=failure):
                with patch.object(audit.sys, "argv", ["audit", "--output-dir", "unused"]):
                    with patch.object(audit, "run_audit", side_effect=failure):
                        with contextlib.redirect_stderr(io.StringIO()):
                            self.assertEqual(audit.main(), 1)

    def test_cli_success(self):
        with patch.object(audit.sys, "argv", ["audit", "--output-dir", "unused"]):
            with patch.object(audit, "run_audit", return_value={}):
                self.assertEqual(audit.main(), 0)


if __name__ == "__main__":
    unittest.main()
