"""Check frozen, finite moving-window evidence; not an asymptotic proof."""
import csv
import math
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def table(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


rows = table(HERE / "data" / "window_results_H8192.csv")
assert len(rows) == 37, f"expected 37 census rows; got {len(rows)}"
lookup = {}
for a in rows:
    H, T = int(a["H"]), int(a["T"])
    assert H & (H - 1) == 0 and 64 <= H <= 8192
    assert 1 <= T <= H // 2
    assert (H, T) not in lookup
    lookup[(H, T)] = a
    E, W, D = (int(a[k]) for k in ("E", "W", "diagonal"))
    assert int(a["window_count"]) == H * (2 * T + 1)
    assert W - D == int(a["offdiag_twice"])
    assert W == sum(int(a[k]) for k in ("core_sq", "cross_core_edges", "edges_sq"))
    assert int(a["failed_inequalities"]) == 0
    assert 3 * T * E <= 3 * W + 4 * H * T * (T * T - 1)
    mean, variance = float(a["mean_mode"]), float(a["variance_mode"])
    assert math.isclose(mean + variance, W, rel_tol=1e-12, abs_tol=0.1)
    assert math.isclose(mean / W, float(a["mean_mode_fraction"]), rel_tol=1e-12)

known = {
    (64, 22): (7137, 324610),
    (256, 64): (110216, 13947713),
    (4096, 512): (30291950, 30892995718),
    (8192, 861): (126589560, 218434508977),
}
for key, expected in known.items():
    a = lookup[key]
    assert (int(a["E"]), int(a["W"])) == expected
assert int(lookup[(4096, 512)]["offdiag_twice"]) < 0
assert int(lookup[(8192, 861)]["offdiag_twice"]) > 0

optimal = table(HERE / "data" / "window_optimal_T.csv")
assert len(optimal) == 8
assert [int(a["H"]) for a in optimal] == [64, 128, 256, 512, 1024, 2048, 4096, 8192]
assert [(int(a["H"]), int(a["optimal_T"])) for a in optimal][-2:] == [(4096, 14), (8192, 18)]
null = table(HERE / "data" / "squarefree_null_H4096.csv")
assert len(null) == 49 and null[0]["kind"] == "mobius"
assert all(a["kind"] == "random_support" for a in null[1:])
assert int(null[0]["W"]) == int(lookup[(4096, 512)]["W"])

# Optional smoke run; the full 8192 run requires about 2.3 GiB of RAM.
if len(sys.argv) == 3 and sys.argv[1] == "--binary":
    binary = sys.argv[2]
    for H, T in [(64, 22), (256, 64)]:
        output = subprocess.check_output([binary, str(H), str(T)], text=True)
        metrics = dict(part.split("=", 1) for part in output.split())
        assert int(metrics["E"]) == int(lookup[(H, T)]["E"])
        assert int(metrics["W"]) == int(lookup[(H, T)]["W"])
        assert int(metrics["D"]) == int(lookup[(H, T)]["diagonal"])
    print("C++ smoke reproduction: PASS")
else:
    assert len(sys.argv) == 1, "usage: check_data.py [--binary /path/to/mw_census]"
print("Frozen data, exact arithmetic identities, null-control metadata: PASS")
