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


replace_once(
    "RHLean/Proof/SquareRootLowPrimeSignedResponseMatching.lean",
    """  intro a _ha b _hb hab
  omega
""",
    """  intro a _ha b _hb hab
  exact Nat.mul_left_cancel hell.pos hab
""",
)

creation = "RHLean/Proof/CreationResponseFrontierCancellation.lean"
replace_once(
    creation,
    """    unfold creationResponseMatchedImage
    symm
    apply Finset.sum_image
""",
    """    unfold creationResponseMatchedImage
    apply Finset.sum_image
""",
)
replace_once(
    creation,
    """  rw [← hCsplit, ← hRsplit, himageSum]
  abel
""",
    """  rw [← hCsplit, ← hRsplit, himageSum]
  calc
    _ = (∑ c ∈ C \ M, wC c) +
          (∑ r ∈ R \ creationResponseMatchedImage M φ, wR r) +
          ((∑ c ∈ M, wC c) + ∑ c ∈ M, wR (φ c)) := by
      abel
    _ = _ := by rw [hpair, add_zero]
""",
)
replace_count(creation, "abs_add _ _", "abs_add_le _ _", 1)
replace_once(
    creation,
    "    cases haz.symm.trans hbz\n",
    "    cases haz.trans hbz.symm\n",
)

energy = "RHLean/Proof/SquareRootLowPrimeQuantitativeEnergyReduction.lean"
replace_once(
    energy,
    """  have hstep :=
    squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
      R K j p hp
  nlinarith
""",
    """  have hstep :=
    squareRootLowPrimeRunningImbalanceReal_step_eq_freshIncrementReal
      R K j p hp
  rw [← hstep]
  ring
""",
)
replace_count(energy, "abs_add _ _", "abs_add_le _ _", 2)

postroot = "RHLean/Proof/SquareRootLowPrimePostRootTransform.lean"
replace_once(
    postroot,
    """  classical
  rw [squareRootLowPrimePostRootResponseAtoms_eq_product_filter]
  unfold squareRootLowPrimePostRootParentMass
    squareRootLowPrimePostRootCofactorTransform
  rw [Finset.sum_filter]
""",
    """  classical
  unfold squareRootLowPrimePostRootParentMass
    squareRootLowPrimePostRootCofactorTransform
  rw [squareRootLowPrimePostRootResponseAtoms_eq_product_filter,
    Finset.sum_filter]
""",
)
replace_once(
    postroot,
    """  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    positivity
""",
    """  have hXltSquare : squareRootEndpoint R < R ^ 2 := by
    unfold squareRootEndpoint
    have hsqpos : 0 < R ^ 2 := by positivity
    exact Nat.sub_lt hsqpos (by norm_num)
""",
)

rough = "RHLean/Proof/SquareRootLowPrimeRoughBaseResidual.lean"
replace_once(
    rough,
    """  unfold squareRootLowPrimeOwnedResponseRoughBaseResidual
    squareRootLowPrimeOwnedResponseRoughBaseFiber
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to'
      (s := squareRootLowPrimeOwnedResponseChildren R K U)
      (t := squareRootLowPrimeOwnedResponseRoughBases R K U)
      (g := squareRootLowPrimeResponseRoughBase K U)
      hmaps
      (fun n : ℕ => μ n))
""",
    """  unfold squareRootLowPrimeOwnedResponseRoughBaseResidual
    squareRootLowPrimeOwnedResponseRoughBaseFiber
  symm
  have h := Finset.sum_fiberwise_eq_sum_filter
    (squareRootLowPrimeOwnedResponseChildren R K U)
    (squareRootLowPrimeOwnedResponseRoughBases R K U)
    (squareRootLowPrimeResponseRoughBase K U)
    (fun n : ℕ => μ n)
  simpa [hmaps] using h
""",
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
