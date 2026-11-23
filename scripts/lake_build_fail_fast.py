#!/usr/bin/env python3
"""Stream a Lake build and stop its process group on the first reported failure.

Lake v4.34.1 has no fail-fast CLI option: its Build/Run.lean monitor records
failed jobs and continues draining the queue. This wrapper preserves Lake's
output, recognizes its failed-job marker, an anchored compiler error, or a
repository-owned warning, and terminates only the process group it created. A short diagnostic grace
lets the failed job's already-produced log flush before TERM, with bounded
KILL escalation for compiler children that do not exit.

Pinned parser/monitor source:
https://github.com/leanprover/lean4/tree/v4.34.1/src/lake/Lake
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import sys
import time
from typing import BinaryIO, Sequence


# Strip terminal controls for matching only; the original bytes are streamed.
ANSI = re.compile(rb"\x1b\[[0-?]*[ -/]*[@-~]|\x1b\][^\x07]*(?:\x07|\x1b\\)")
FAILED_JOB = re.compile(r"^✖ \[\d+/\d+\](?! \(Optional\))".encode())
COMPILER_ERROR = re.compile(
    rb"^(?:error:|(?!(?:info|warning|trace):)[^\r\n]*\.lean:\d+(?::\d+)?:\s*error:)"
)
# This is the existing lean.yml owned-source boundary. Match it against the
# diagnostic's source path, so a dependency warning quoting RHLean in its
# message does not become an owned warning.
OWNED_PATH = re.compile(rb"(?:^|[\s:])(?:\./)*RHLean(?:\.lean|/)")
WARNING_FIRST = re.compile(rb"^warning:\s*(?P<path>[^\s:]+\.lean):\d+(?::\d+)?:")
WARNING_LAST = re.compile(rb"^(?P<path>[^\s:]+\.lean):\d+(?::\d+)?:\s*warning:")


def is_failure_line(line: bytes) -> bool:
    """Recognize actual Lake/Lean diagnostics, not error words inside info."""
    clean = ANSI.sub(b"", line).lstrip(b"\r")
    warning = WARNING_FIRST.match(clean) or WARNING_LAST.match(clean)
    return bool(FAILED_JOB.match(clean) or COMPILER_ERROR.match(clean)
                or (warning and OWNED_PATH.search(warning.group("path"))))


def signal_group(process: subprocess.Popen, sig: signal.Signals) -> None:
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def group_exists(process: subprocess.Popen) -> bool:
    try:
        os.killpg(process.pid, 0)
        return True
    except ProcessLookupError:
        return False


def run_fail_fast(command: Sequence[str], *, cwd: Path | None = None,
                  output: BinaryIO | None = None, diagnostic_grace: float = 0.2,
                  terminate_grace: float = 2.0) -> None:
    """Run a command with Lake output; raise on failure and stop its process group.

    The command is passed directly to Popen, never through a shell. The caller
    gets CalledProcessError even if a misbehaving process prints an error and
    exits zero. Successful output and ordinary nonzero exits are unchanged.
    """
    if diagnostic_grace < 0 or terminate_grace < 0:
        raise ValueError("termination grace intervals must be nonnegative")
    stream = output if output is not None else sys.stdout.buffer
    process = subprocess.Popen(list(command), cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    assert process.stdout is not None
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    os.set_blocking(process.stdout.fileno(), False)
    pending = b""
    failed_at = term_at = kill_at = None
    try:
        while True:
            now = time.monotonic()
            if failed_at is not None and term_at is None and now >= failed_at + diagnostic_grace:
                signal_group(process, signal.SIGTERM)
                term_at = now
            if term_at is not None and kill_at is None and now >= term_at + terminate_grace:
                signal_group(process, signal.SIGKILL)
                kill_at = now
            for key, _ in selector.select(timeout=0.05):
                chunk = os.read(key.fd, 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    if pending and is_failure_line(pending) and failed_at is None:
                        failed_at = time.monotonic()
                    pending = b""
                    continue
                stream.write(chunk)
                stream.flush()
                pending += chunk
                lines = pending.split(b"\n")
                pending = lines.pop()
                if failed_at is None and any(is_failure_line(line) for line in lines):
                    failed_at = time.monotonic()
            returncode = process.poll()
            if not selector.get_map() and returncode is not None:
                if failed_at is None:
                    break
                # Descendants can close stdout while ignoring TERM. Finish
                # escalation for the group even if the parent has exited.
                if kill_at is not None or (term_at is not None and not group_exists(process)):
                    break
            if kill_at is not None and time.monotonic() >= kill_at + 1.0:
                # An escaped process must not keep our pipe open indefinitely.
                break
        returncode = process.wait(timeout=max(1.0, terminate_grace))
    except BaseException:
        signal_group(process, signal.SIGTERM)
        try:
            process.wait(timeout=terminate_grace)
        except subprocess.TimeoutExpired:
            pass
        signal_group(process, signal.SIGKILL)
        process.wait()
        raise
    finally:
        selector.close()
        process.stdout.close()
    if failed_at is not None:
        raise subprocess.CalledProcessError(returncode if returncode > 0 else 1, list(command))
    if returncode:
        raise subprocess.CalledProcessError(returncode, list(command))


def run_lake_build(targets: Sequence[str], *, cwd: Path | None = None) -> None:
    run_fail_fast(["lake", "build", *targets], cwd=cwd)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+", help="Lake build targets")
    args = parser.parse_args()
    try:
        run_lake_build(args.targets)
    except subprocess.CalledProcessError as error:
        return error.returncode if error.returncode > 0 else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
