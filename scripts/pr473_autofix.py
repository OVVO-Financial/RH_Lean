#!/usr/bin/env python3
"""Apply the deterministic Lean and root-manifest repairs required by PR #473."""

from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count == 0 and new in text:
        return
    if count != 1:
        raise SystemExit(f"expected one anchor in {path}, found {count}: {old!r}")
    p.write_text(text.replace(old, new, 1))


def replace_count(path: str, old: str, new: str, expected: int) -> None:
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count == 0 and text.count(new) >= expected:
        return
    if count != expected:
        raise SystemExit(
            f"expected {expected} anchors in {path}, found {count}: {old!r}"
        )
    p.write_text(text.replace(old, new))


saturation = "RHLean/Proof/SquareRootLowPrimeMatchingFrontierSaturation.lean"
replace_once(
    saturation,
    """      · exact ih (squareRootLowPrimeResponseFrontierStep S q)
          hTail hn hnot
""",
    """      · exact ih (squareRootLowPrimeResponseFrontierStep S q)
          hTail hn
""",
)

real_cancellation = "RHLean/Proof/CreationResponseFrontierCancellationReal.lean"
replace_count(real_cancellation, "abs_add _ _", "abs_add_le _ _", 1)

rough = "RHLean/Proof/SquareRootLowPrimeRoughBaseResidual.lean"
replace_once(
    rough,
    """  have h := Finset.sum_fiberwise_eq_sum_filter
    (squareRootLowPrimeOwnedResponseChildren R K U)
    (squareRootLowPrimeOwnedResponseRoughBases R K U)
    (squareRootLowPrimeResponseRoughBase K U)
    (fun n : ℕ => μ n)
  simpa [hmaps] using h
""",
    """  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := squareRootLowPrimeOwnedResponseChildren R K U)
      (t := squareRootLowPrimeOwnedResponseRoughBases R K U)
      (g := squareRootLowPrimeResponseRoughBase K U)
      hmaps
      (fun n : ℕ => μ n))
""",
)

running = "RHLean/Proof/SquareRootLowPrimeRunningTelescope.lean"
replace_count(
    running,
    "rw [canonicalLargestPrimeFactor_le_composite_iff_le_pred hp hnot]",
    "simp only [canonicalLargestPrimeFactor_le_composite_iff_le_pred hp hnot]",
    2,
)
replace_once(
    running,
    "(∑ p ∈ Finset.Ioc K (K + n), T (p - 1) - T p) =",
    "(∑ p ∈ Finset.Ioc K (K + n), (T (p - 1) - T p)) =",
)
replace_once(
    running,
    "(∑ p ∈ Finset.Ioc K U, T (p - 1) - T p) = T K - T U := by",
    "(∑ p ∈ Finset.Ioc K U, (T (p - 1) - T p)) = T K - T U := by",
)

manifest = Path("RHLean.lean")
targets = {
    "import RHLean.Proof.SquareRootLowPrimeCanonicalFrontierBridge",
    "import RHLean.Proof.SquareRootLowPrimeCreationResponseCarriers",
    "import RHLean.Proof.SquareRootLowPrimeDeepResponseAtoms",
    "import RHLean.Proof.SquareRootLowPrimePostRootTransform",
    "import RHLean.Proof.SquareRootLowPrimeProcessedSeatCarrier",
    "import RHLean.Proof.SquareRootLowPrimeProcessedSeatMatching",
    "import RHLean.Proof.SquareRootLowPrimeResponseForest",
    "import RHLean.Proof.SquareRootLowPrimeResponseFrontier",
    "import RHLean.Proof.SquareRootLowPrimeSignedResponseChildren",
    "import RHLean.Proof.SquareRootLowPrimeSignedResponseEnergy",
}
lines = [line.strip() for line in manifest.read_text().splitlines() if line.strip()]
for target in targets:
    if target not in lines:
        lines.append(target)
manifest.write_text("\n".join(sorted(lines)) + "\n")
