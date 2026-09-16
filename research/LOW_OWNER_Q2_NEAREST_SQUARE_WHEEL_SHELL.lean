import Mathlib
import RHLean.Analysis.SquareWheelNesting
import «research.LOW_OWNER_Q2_ENDPOINT_ARC_FUBINI»

/-!
# Physical nearest-square shells as finite wheel frequency arcs

The nearest-square reduction leaves one oriented Mertens shell per reciprocal
q² daughter.  This file identifies that shell with the *actual finite wheel
response*, not with an abstract surrogate.

Inside one synchronized primorial block, a Mertens difference over a forward
arc of length `d`, starting after prefix length `A`, is exactly

  sum_r pinnedCoeff(r) * chi(r)^A * D_d(r).

Combining this with the square-block midpoint choice gives two exact cases:

* left half: `M(Y)-M(E)` is a forward arc from the lower completed square `E`;
* right half: `M(Y)-M(E)` is the negative forward arc from `Y` to the upper
  completed square `E`.

For every nonzero frequency the short arc is already reduced modulo its additive
conductor by `LOW_OWNER_Q2_ENDPOINT_ARC_FUBINI`.  The zero frequency remains the
explicit length-coupled endpoint mode.  No norm or asymptotic estimate enters
this dictionary.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- **Physical forward-arc Fourier identity.**  Within one primorial block, the
Mertens mass of a forward integer arc is exactly the finite sum of its
endpoint-phased wheel frequency atoms. -/
theorem primorialWheel_mertensForwardArc_eq_sum_frequencyArcs
    (k A d : ℕ) (hA : 0 < A)
    (hupper : primorialBlockLower k + (A + d) ≤ primorialBlockUpper k) :
    mertensSummatory (primorialBlockLower k + (A + d)) -
        mertensSummatory (primorialBlockLower k + A) =
      ∑ r : ZMod (primorialWheelSystem k).modulus,
        primeWheelForwardArcFrequencyAtom (primorialWheelSystem k) A d r := by
  have hAd : 0 < A + d := by omega
  have hupperA :
      primorialBlockLower k + A ≤ primorialBlockUpper k := by omega
  have hlong := primorialWheel_dirichletPrefix_eq_mertens_sub
    k (A + d) hAd hupper
  have hshort := primorialWheel_dirichletPrefix_eq_mertens_sub
    k A hA hupperA
  have harc := primeWheelDirichletPrefix_add_sub_eq_sum_forwardArc
    (primorialWheelSystem k) A d
  calc
    mertensSummatory (primorialBlockLower k + (A + d)) -
        mertensSummatory (primorialBlockLower k + A) =
      (mertensSummatory (primorialBlockLower k + (A + d)) -
          mertensSummatory (primorialBlockLower k)) -
        (mertensSummatory (primorialBlockLower k + A) -
          mertensSummatory (primorialBlockLower k)) := by ring
    _ = primeWheelDirichletPrefix (primorialWheelSystem k) (A + d) -
          primeWheelDirichletPrefix (primorialWheelSystem k) A := by
      rw [hlong, hshort]
    _ = ∑ r : ZMod (primorialWheelSystem k).modulus,
          primeWheelForwardArcFrequencyAtom (primorialWheelSystem k) A d r := harc

/-- Same physical arc with zero frequency separated and every nonzero frequency
already reduced to its residual conductor distance. -/
theorem primorialWheel_mertensForwardArc_eq_zero_add_reducedNonzero
    (k A d : ℕ) (hA : 0 < A)
    (hupper : primorialBlockLower k + (A + d) ≤ primorialBlockUpper k) :
    mertensSummatory (primorialBlockLower k + (A + d)) -
        mertensSummatory (primorialBlockLower k + A) =
      primeWheelForwardArcFrequencyAtom (primorialWheelSystem k) A d 0 +
        ∑ r : ZMod (primorialWheelSystem k).modulus,
          if r = 0 then 0 else
            primeWheelPinnedCoefficient (primorialWheelSystem k) r *
              ZMod.stdAddChar r ^ A *
                primeWheelDirichletKernel (primorialWheelSystem k)
                  (d % reducedAdditiveConductor r) r := by
  have hAd : 0 < A + d := by omega
  have hupperA :
      primorialBlockLower k + A ≤ primorialBlockUpper k := by omega
  have hlong := primorialWheel_dirichletPrefix_eq_mertens_sub
    k (A + d) hAd hupper
  have hshort := primorialWheel_dirichletPrefix_eq_mertens_sub
    k A hA hupperA
  have harc := primeWheelDirichletPrefix_add_sub_eq_zero_add_reducedNonzero
    (primorialWheelSystem k) A d
  calc
    mertensSummatory (primorialBlockLower k + (A + d)) -
        mertensSummatory (primorialBlockLower k + A) =
      (mertensSummatory (primorialBlockLower k + (A + d)) -
          mertensSummatory (primorialBlockLower k)) -
        (mertensSummatory (primorialBlockLower k + A) -
          mertensSummatory (primorialBlockLower k)) := by ring
    _ = primeWheelDirichletPrefix (primorialWheelSystem k) (A + d) -
          primeWheelDirichletPrefix (primorialWheelSystem k) A := by
      rw [hlong, hshort]
    _ = _ := harc

end RHLean.Analysis

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

/-- The arithmetic q² shell atom is literally the Mertens difference from the
selected nearest completed-square endpoint. -/
theorem lowOwnerNearestSquareShellAtom_eq_mertensDifference
    (R q : ℕ) :
    lowOwnerNearestSquareShellAtom R q =
      mertensSummatory (rawQ2ChildCutoff R q) -
        mertensSummatory
          (q2NearestSquareEndpoint (rawQ2ChildCutoff R q)) := by
  unfold lowOwnerNearestSquareShellAtom lowOwnerRawMertensAmplitude
    lowOwnerNearestSquareMertensAmplitude
  rw [mertensSummatoryInt_cast, mertensSummatoryInt_cast]

/-- **Left-half shell.**  If the literal daughter lies below the half-integer
midpoint, its shell is the forward finite wheel arc from the lower completed
square endpoint. -/
theorem lowOwnerNearestSquareShellAtom_eq_lower_frequencyArc
    {R q k : ℕ}
    (hmid : rawQ2ChildCutoff R q <
      (Nat.sqrt (rawQ2ChildCutoff R q)) ^ 2 +
        Nat.sqrt (rawQ2ChildCutoff R q))
    (hblockLower : primorialBlockLower k <
      squareRootEndpoint (Nat.sqrt (rawQ2ChildCutoff R q)))
    (hblockUpper : rawQ2ChildCutoff R q ≤ primorialBlockUpper k) :
    lowOwnerNearestSquareShellAtom R q =
      ∑ r : ZMod (primorialWheelSystem k).modulus,
        primeWheelForwardArcFrequencyAtom (primorialWheelSystem k)
          (squareRootEndpoint (Nat.sqrt (rawQ2ChildCutoff R q)) -
            primorialBlockLower k)
          (rawQ2ChildCutoff R q -
            squareRootEndpoint (Nat.sqrt (rawQ2ChildCutoff R q))) r := by
  let Y : ℕ := rawQ2ChildCutoff R q
  let s : ℕ := Nat.sqrt Y
  let E : ℕ := squareRootEndpoint s
  have hmid' : Y < s ^ 2 + s := by simpa [Y, s] using hmid
  have hendpoint : q2NearestSquareEndpoint Y = E := by
    dsimp [E]
    exact q2NearestSquareEndpoint_eq_lower hmid'
  have hs2 : s ^ 2 ≤ Y := by
    dsimp [s]
    exact Nat.sqrt_le' Y
  have hEY : E ≤ Y := by
    dsimp [E]
    unfold squareRootEndpoint
    exact (Nat.sub_le _ _).trans hs2
  have hLE : primorialBlockLower k < E := by
    simpa [Y, s, E] using hblockLower
  have hA : 0 < E - primorialBlockLower k := Nat.sub_pos_of_lt hLE
  have hupper :
      primorialBlockLower k +
          ((E - primorialBlockLower k) + (Y - E)) ≤
        primorialBlockUpper k := by
    have hYU : Y ≤ primorialBlockUpper k := by simpa [Y] using hblockUpper
    omega
  have harc := primorialWheel_mertensForwardArc_eq_sum_frequencyArcs
    k (E - primorialBlockLower k) (Y - E) hA hupper
  have hstart : primorialBlockLower k + (E - primorialBlockLower k) = E := by
    omega
  have hend : primorialBlockLower k +
      ((E - primorialBlockLower k) + (Y - E)) = Y := by omega
  rw [lowOwnerNearestSquareShellAtom_eq_mertensDifference, hendpoint]
  calc
    mertensSummatory Y - mertensSummatory E =
      mertensSummatory
          (primorialBlockLower k +
            ((E - primorialBlockLower k) + (Y - E))) -
        mertensSummatory
          (primorialBlockLower k + (E - primorialBlockLower k)) := by
      rw [hend, hstart]
    _ = ∑ r : ZMod (primorialWheelSystem k).modulus,
        primeWheelForwardArcFrequencyAtom (primorialWheelSystem k)
          (E - primorialBlockLower k) (Y - E) r := harc
    _ = _ := by simp [Y, s, E]

/-- **Right-half shell.**  If the literal daughter is at or above the first
integer after the midpoint, its shell is the negative finite wheel arc from the
daughter into the upper completed-square endpoint. -/
theorem lowOwnerNearestSquareShellAtom_eq_neg_upper_frequencyArc
    {R q k : ℕ}
    (hmid :
      (Nat.sqrt (rawQ2ChildCutoff R q)) ^ 2 +
          Nat.sqrt (rawQ2ChildCutoff R q) ≤ rawQ2ChildCutoff R q)
    (hblockLower : primorialBlockLower k < rawQ2ChildCutoff R q)
    (hblockUpper :
      squareRootEndpoint (Nat.sqrt (rawQ2ChildCutoff R q) + 1) ≤
        primorialBlockUpper k) :
    lowOwnerNearestSquareShellAtom R q =
      -(∑ r : ZMod (primorialWheelSystem k).modulus,
        primeWheelForwardArcFrequencyAtom (primorialWheelSystem k)
          (rawQ2ChildCutoff R q - primorialBlockLower k)
          (squareRootEndpoint (Nat.sqrt (rawQ2ChildCutoff R q) + 1) -
            rawQ2ChildCutoff R q) r) := by
  let Y : ℕ := rawQ2ChildCutoff R q
  let s : ℕ := Nat.sqrt Y
  let E : ℕ := squareRootEndpoint (s + 1)
  have hmid' : s ^ 2 + s ≤ Y := by simpa [Y, s] using hmid
  have hendpoint : q2NearestSquareEndpoint Y = E := by
    dsimp [E]
    exact q2NearestSquareEndpoint_eq_upper hmid'
  have hlt : Y < (s + 1) ^ 2 := by
    dsimp [s]
    exact Nat.lt_succ_sqrt' Y
  have hYE : Y ≤ E := by
    dsimp [E]
    unfold squareRootEndpoint
    omega
  have hLY : primorialBlockLower k < Y := by
    simpa [Y] using hblockLower
  have hA : 0 < Y - primorialBlockLower k := Nat.sub_pos_of_lt hLY
  have hupper :
      primorialBlockLower k +
          ((Y - primorialBlockLower k) + (E - Y)) ≤
        primorialBlockUpper k := by
    have hEU : E ≤ primorialBlockUpper k := by simpa [Y, s, E] using hblockUpper
    omega
  have harc := primorialWheel_mertensForwardArc_eq_sum_frequencyArcs
    k (Y - primorialBlockLower k) (E - Y) hA hupper
  have hstart : primorialBlockLower k + (Y - primorialBlockLower k) = Y := by
    omega
  have hend : primorialBlockLower k +
      ((Y - primorialBlockLower k) + (E - Y)) = E := by omega
  rw [lowOwnerNearestSquareShellAtom_eq_mertensDifference, hendpoint]
  calc
    mertensSummatory Y - mertensSummatory E =
      -(mertensSummatory E - mertensSummatory Y) := by ring
    _ = -(mertensSummatory
          (primorialBlockLower k +
            ((Y - primorialBlockLower k) + (E - Y))) -
        mertensSummatory
          (primorialBlockLower k + (Y - primorialBlockLower k))) := by
      rw [hend, hstart]
    _ = -(∑ r : ZMod (primorialWheelSystem k).modulus,
        primeWheelForwardArcFrequencyAtom (primorialWheelSystem k)
          (Y - primorialBlockLower k) (E - Y) r) := by rw [harc]
    _ = _ := by simp [Y, s, E]

end RHLean.Proof
