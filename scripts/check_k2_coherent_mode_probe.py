#!/usr/bin/env python3
"""Check finite K2 diagnostics; this is not a Lean certificate or RH estimate."""

import math
from pathlib import Path
import re
import subprocess
import sys


def run(binary, *args):
    return subprocess.check_output([str(binary), *map(str, args)], text=True)


def main():
    binary = Path(sys.argv[1]).resolve()
    limit = 2000
    # Independent definition: prime-power Lambda, then all divisor pairs.
    lam = [0.0] * (limit + 1)
    for p in range(2, limit + 1):
        if all(p % d for d in range(2, math.isqrt(p) + 1)):
            power = p
            while power <= limit:
                lam[power] = math.log(p)
                power *= p
    conv = [0.0] * (limit + 1)
    for a in range(1, limit + 1):
        for b in range(1, limit // a + 1):
            conv[a * b] += lam[a] * lam[b]
    prefixes = [0.0] * (limit + 1)
    for n in range(1, limit + 1):
        prefixes[n] = prefixes[n - 1] + conv[n] - lam[n] * math.log(n)
    rows = [line.split() for line in run(binary, limit, 2).splitlines()
            if line and not line.startswith("#")]
    assert [int(row[0]) for row in rows] == list(range(2, limit + 1))
    for row in rows:
        n, actual = int(row[0]), float(row[1])
        assert math.isclose(actual, prefixes[n], rel_tol=0, abs_tol=1e-6), (n, actual, prefixes[n])
    print("Every K2 prefix through 2000 agrees with direct divisor convolution.")

    output = run(binary)
    match = re.search(r"samples=(\d+)\s+pearson.* = ([\d.]+)", output)
    assert match, "Missing regression summary"
    assert int(match[1]) == 2000, match[0]
    assert abs(float(match[2]) - 0.99833) < 0.00005, match[0]
    match = re.search(r"# last x=(\d+).* = (-?[\d.]+)", output)
    assert match and int(match[1]) == 20000000, "Missing endpoint"
    assert abs(float(match[2]) + 1.1544) < 0.0001, match[0]
    print("\n".join(line for line in output.splitlines() if line.startswith("# samples=") or line.startswith("# last x=")))
    print("Finite regression reproduced; no uniform bound is certified.")


if __name__ == "__main__":
    main()
