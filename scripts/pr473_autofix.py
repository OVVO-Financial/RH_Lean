#!/usr/bin/env python3
"""Apply the remaining deterministic Lean repairs required by PR #473."""

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
    """      z.1 = c ∧ z.2 < squareRootBornPartnerCount R c := by
  simp [squareRootLowPrimeShallowBornSeatFiber]
""",
    """      z.1 = c ∧ z.2 < squareRootBornPartnerCount R c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowBornSeatFiber, eq_comm]
""",
)
replace_once(
    channel,
    """      z.1 = c ∧ z.2 < squareRootBornPostTailHighResponse R K j c := by
  simp [squareRootLowPrimeShallowHighSeatFiber]
""",
    """      z.1 = c ∧ z.2 < squareRootBornPostTailHighResponse R K j c := by
  rcases z with ⟨z1, z2⟩
  simp [squareRootLowPrimeShallowHighSeatFiber, eq_comm]
""",
)
replace_once(
    channel,
    """  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowBornSeatFiber.mp hzc).1.symm.trans
""",
    """  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeShallowBornSeatFiber R c)
    (squareRootLowPrimeShallowBornSeatFiber R d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowBornSeatFiber.mp hzc).1.symm.trans
""",
)
replace_once(
    channel,
    """  intro c _hc d _hd hcd
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowHighSeatFiber.mp hzc).1.symm.trans
""",
    """  intro c _hc d _hd hcd
  change Disjoint
    (squareRootLowPrimeShallowHighSeatFiber R K j c)
    (squareRootLowPrimeShallowHighSeatFiber R K j d)
  rw [Finset.disjoint_left]
  intro z hzc hzd
  exact hcd
    ((mem_squareRootLowPrimeShallowHighSeatFiber.mp hzc).1.symm.trans
""",
)
replace_once(
    channel,
    """  unfold squareRootLowPrimeShallowBornCreationStates
  symm
  apply Finset.sum_image
""",
    """  unfold squareRootLowPrimeShallowBornCreationStates
  apply Finset.sum_image
""",
)
replace_once(
    channel,
    """  unfold squareRootLowPrimeShallowHighCreationStates
  symm
  apply Finset.sum_image
""",
    """  unfold squareRootLowPrimeShallowHighCreationStates
  apply Finset.sum_image
""",
)
replace_once(
    channel,
    """  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  simpa [squareRootLowPrimeResponseAtomWeightReal,
    squareRootLowPrimeFreshIncrementReal] using h.symm
""",
    """  have h := congrArg Complex.re
    (squareRootLowPrimeFreshIncrement_sum_eq_neg_ownedResponseAtomChildMass
      (R := R) (K := K) (j := j) (U := U) hR hUR)
  have hre :
      (∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
        squareRootLowPrimeFreshIncrementReal R K j p) =
        -(∑ z ∈ squareRootLowPrimeOwnedResponseAtoms R K U,
          squareRootLowPrimeResponseAtomWeightReal z) := by
    simpa [squareRootLowPrimeResponseAtomWeightReal,
      squareRootLowPrimeFreshIncrementReal] using h
  linarith
""",
)

energy_gate = "RHLean/Proof/SquareRootLowPrimeCreationResponseEnergyGate.lean"
replace_once(
    energy_gate,
    """  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  rw [hcreation]
  linarith
""",
    """  have htelescope :=
    squareRootLowPrimeRunningImbalanceReal_sub_eq_freshIncrement_sum
      (R := R) (K := K) (j := j) (U := U) hK hKU
  rw [hcreation] at htelescope
  linarith [hresponse]
""",
)
replace_once(
    energy_gate,
    """  have hcancelReal := congrArg (fun z : ℤ => (z : ℝ)) hcancelInt
  unfold intMassReal at hterminal ⊢
  push_cast at hcancelReal
  rw [hterminal]
  exact hcancelReal
""",
    """  calc
    squareRootLowPrimeRunningImbalanceReal R K j U =
        intMassReal C wC + intMassReal Resp wR := hterminal
    _ = intMassReal (C \\ M) wC +
        intMassReal
          (Resp \\ creationResponseMatchedImage M φ) wR := by
      unfold intMassReal
      exact_mod_cast hcancelInt
""",
)
replace_once(
    energy_gate,
    """  unfold intMassReal at hterminal
  rw [hterminal, card_squareRootLowPrimeRootSeatBox] at hbound
  exact_mod_cast hbound
""",
    """  unfold intMassReal at hterminal
  rw [hterminal]
  rw [card_squareRootLowPrimeRootSeatBox] at hbound
  exact_mod_cast hbound
""",
)

child_root = "RHLean/Proof/SquareRootLowPrimeChildToRootBridge.lean"
replace_once(
    child_root,
    """  convert hfar using 1 <;> ring
""",
    """  convert hfar using 1
  all_goals ring_nf
""",
)
