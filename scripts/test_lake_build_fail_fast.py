"""Fail-fast process tests use only controlled Python children, never Lean."""

import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import lake_build_fail_fast as ff


class LakeFailFastTests(unittest.TestCase):
    def run_python(self, code, *args):
        output = io.BytesIO()
        command = [sys.executable, "-u", "-c", code, *map(str, args)]
        ff.run_fail_fast(command, output=output, diagnostic_grace=0.05, terminate_grace=0.15)
        return output.getvalue()

    def test_success_streams_bytes_without_false_positive(self):
        payload = (b"info: Example.lean:1:2: error: quoted example\n"
                   b"warning: this message mentions error: without failing\n"
                   b"\x1b[32m\xe2\x9c\x94 [1/1] Built Example\x1b[0m\n")
        output = self.run_python("import sys; sys.stdout.buffer.write(" + repr(payload) + ")")
        self.assertEqual(output, payload)

    def test_failed_job_marker_stops_later_work_and_keeps_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            later = Path(directory) / "later"
            output = io.BytesIO()
            code = ("import pathlib, sys, time\n"
                    "print('\\x1b[31m✖ [2/8] Building Broken\\x1b[0m', flush=True)\n"
                    "print('error: Broken.lean:2:4: type mismatch', flush=True)\n"
                    "print('expected goal details', flush=True)\n"
                    "time.sleep(10)\n"
                    "pathlib.Path(sys.argv[1]).write_text('must not run')\n")
            started = time.monotonic()
            with self.assertRaises(subprocess.CalledProcessError):
                ff.run_fail_fast([sys.executable, "-u", "-c", code, str(later)], output=output,
                                 diagnostic_grace=0.05, terminate_grace=0.15)
            self.assertLess(time.monotonic() - started, 3)
            self.assertFalse(later.exists())
            self.assertIn(b"expected goal details\n", output.getvalue())
            self.assertIn(b"\x1b[31m", output.getvalue())

    def test_anchored_compiler_error_fails_even_with_zero_exit(self):
        for diagnostic in ("error: build failed", "/tmp/Broken.lean:8:3: error: type mismatch"):
            with self.subTest(diagnostic=diagnostic), self.assertRaises(subprocess.CalledProcessError):
                self.run_python("print(" + repr(diagnostic) + ")")

    def test_failed_job_marker_alone_fails(self):
        with self.assertRaises(subprocess.CalledProcessError):
            self.run_python("print('✖ [3/10] Building Broken')")

    def test_optional_job_marker_does_not_fail(self):
        output = self.run_python("print('✖ [3/10] (Optional) Building Optional')")
        self.assertIn(b'(Optional)', output)

    def test_owned_warning_is_fatal_in_both_diagnostic_formats(self):
        for diagnostic in ("warning: RHLean/Example.lean:8:3: unused variable",
                           "./RHLean/Example.lean:8:3: warning: unused variable",
                           "warning: RHLean.lean:1:0: unused import"):
            with self.subTest(diagnostic=diagnostic), self.assertRaises(subprocess.CalledProcessError):
                self.run_python("print(" + repr(diagnostic) + ")")

    def test_dependency_warnings_and_info_quotes_remain_allowed(self):
        payload = (b"warning: Mathlib/Example.lean:8:3: upstream warning\n"
                   b"PrimeNumberTheoremAnd/StrongPNT.lean:2:1: warning: upstream warning\n"
                   b"warning: .lake/packages/mathlib/Mathlib/Example.lean:8:3: see RHLean/Example.lean\n"
                   b"info: RHLean/Example.lean:8:3: warning: quoted example\n"
                   b"info: RHLean/Example.lean:8:3: error: quoted example\n")
        output = self.run_python("import sys; sys.stdout.buffer.write(" + repr(payload) + ")")
        self.assertEqual(output, payload)

    def test_nonzero_exit_without_diagnostic_propagates(self):
        with self.assertRaises(subprocess.CalledProcessError) as failure:
            self.run_python("raise SystemExit(7)")
        self.assertEqual(failure.exception.returncode, 7)

    @unittest.skipUnless(os.name == "posix" and Path("/proc").is_dir(), "Linux process-group test")
    def check_term_ignoring_child(self, close_output=False):
        with tempfile.TemporaryDirectory() as directory:
            pid_file = Path(directory) / "child.pid"
            later = Path(directory) / "child-later"
            child = ("import os, pathlib, signal, sys, time\n"
                     "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                     + ("os.close(1); os.close(2)\n" if close_output else "") +
                     "pathlib.Path(sys.argv[1]).write_text(str(os.getpid()))\n"
                     "time.sleep(10)\n"
                     "pathlib.Path(sys.argv[2]).write_text('must not run')\n")
            parent = ("import pathlib, subprocess, sys, time\n"
                      "subprocess.Popen([sys.executable, '-u', '-c', sys.argv[1], sys.argv[2], sys.argv[3]])\n"
                      "while not pathlib.Path(sys.argv[2]).exists(): time.sleep(0.01)\n"
                      "print('error: Broken.lean:1:1: failed', flush=True)\n"
                      "time.sleep(10)\n")
            started = time.monotonic()
            with self.assertRaises(subprocess.CalledProcessError):
                self.run_python(parent, child, pid_file, later)
            self.assertLess(time.monotonic() - started, 3)
            self.assertFalse(later.exists())
            child_pid = int(pid_file.read_text())
            status = Path(f"/proc/{child_pid}/stat")
            # A killed orphan can briefly remain a zombie until PID 1 reaps it.
            try:
                state = status.read_text().rsplit(")", 1)[1].split()[0]
            except FileNotFoundError:
                state = "gone"
            self.assertIn(state, {"gone", "Z", "X"})

    @unittest.skipUnless(os.name == "posix" and Path("/proc").is_dir(), "Linux process-group test")
    def test_term_ignoring_child_is_killed_with_parent_group(self):
        self.check_term_ignoring_child()

    @unittest.skipUnless(os.name == "posix" and Path("/proc").is_dir(), "Linux process-group test")
    def test_closed_output_child_is_stopped_before_wrapper_returns(self):
        self.check_term_ignoring_child(close_output=True)

    def test_build_targets_are_arguments_without_shell_interpolation(self):
        with patch.object(ff, "run_fail_fast") as run:
            ff.run_lake_build(["RHLean.One", "RHLean.Two"], cwd=Path("/tmp/project"))
        run.assert_called_once_with(["lake", "build", "RHLean.One", "RHLean.Two"],
                                    cwd=Path("/tmp/project"))


if __name__ == "__main__":
    unittest.main()
