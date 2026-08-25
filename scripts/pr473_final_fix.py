#!/usr/bin/env python3
"""Apply the final literal creation-carrier repairs required by PR #473."""

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


channel = "RHLean/Proof/SquareRootLowPrimeChannelCreationCarrier.lean"
replace_once(
    channel,
    """  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowBornSeatFiber, eq_comm]
""",
    """  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowBornSeatFiber, eq_comm, and_comm]
""",
)
replace_once(
    channel,
    """  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowHighSeatFiber, eq_comm]
""",
    """  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowHighSeatFiber, eq_comm, and_comm]
""",
)
replace_once(
    channel,
    """  intro a _ha b _hb hab
  exact Sum.inl_injective (Option.some_injective hab)
""",
    """  intro a _ha b _hb hab
  simpa using hab
""",
)
replace_once(
    channel,
    """  intro a _ha b _hb hab
  exact Sum.inr_injective (Option.some_injective hab)
""",
    """  intro a _ha b _hb hab
  simpa using hab
""",
)

creation = "RHLean/Proof/SquareRootLowPrimeCreationResponseCarriers.lean"
replace_once(
    creation,
    """      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  simp [squareRootLowPrimeCreationSeatFiber]
""",
    """      z.1 = c ∧
        z.2 < squareRootLowPrimeCombinedFreshResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeCreationSeatFiber, eq_comm, and_comm]
""",
)
replace_once(
    creation,
    """  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hcEq := (mem_squareRootLowPrimeCreationSeatFiber.mp hzc).1
""",
    """  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeCreationSeatFiber R K j c)
    (squareRootLowPrimeCreationSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hcEq := (mem_squareRootLowPrimeCreationSeatFiber.mp hzc).1
""",
)
replace_once(
    creation,
    """  unfold squareRootLowPrimeCreationCarrier
  rw [Finset.sum_insert
    (none_not_mem_creationSeatAtoms_image_some R K j)]
  simp only [squareRootLowPrimeCreationWeight]
  have himage :
      (∑ x ∈ (squareRootLowPrimeCreationSeatAtoms R K j).image some,
        squareRootLowPrimeCreationWeight x) =
        ∑ z ∈ squareRootLowPrimeCreationSeatAtoms R K j, -μ z.1 := by
    symm
    apply Finset.sum_image
    intro a _ha b _hb hab
    exact Option.some_injective hab
  rw [himage, squareRootLowPrimeCreationSeatAtoms_weight_sum]
""",
    """  unfold squareRootLowPrimeCreationCarrier
  rw [Finset.sum_insert
    (none_not_mem_creationSeatAtoms_image_some R K j)]
  have himage :
      (∑ x ∈ (squareRootLowPrimeCreationSeatAtoms R K j).image some,
        squareRootLowPrimeCreationWeight x) =
        ∑ z ∈ squareRootLowPrimeCreationSeatAtoms R K j, -μ z.1 := by
    apply Finset.sum_image
    intro a _ha b _hb hab
    simpa using hab
  rw [himage, squareRootLowPrimeCreationSeatAtoms_weight_sum]
  simp [squareRootLowPrimeCreationWeight]
""",
)
replace_once(
    creation,
    """  simpa [squareRootLowPrimeResponseAtomWeight,
    canonicalMoebiusWeight, squareRootLowPrimeBadAtomChild] using hcast
""",
    """  simpa [squareRootLowPrimeResponseAtomWeight,
    canonicalMoebiusWeight, squareRootLowPrimeBadAtomChild] using hcast.symm
""",
)
replace_once(
    creation,
    """  rw [hweight]
  simpa using hresponse.symm.trans (by simpa using hatomsRe)
""",
    """  calc
    ((∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
      squareRootLowPrimeResponseAtomWeight z : ℤ) : ℝ) =
        ∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
          (canonicalMoebiusWeight
            (squareRootLowPrimeBadAtomChild z)).re := hweight
    _ = ∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
          (canonicalMoebiusWeight n).re := by
      simpa using hatomsRe.symm
    _ = -(∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
          squareRootLowPrimeFreshIncrementReal R K j p) := by
      linarith [hresponse]
""",
)
