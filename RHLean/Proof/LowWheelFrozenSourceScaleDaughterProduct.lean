import RHLean.Proof.LowWheelFrozenSquareResidualQ2Telescope
import RHLean.Proof.LowWheelFrozenSecondContactScaleFlux

/-!
# Absorbing source-scale parity into the q^2 daughter integer

After the global square-residual telescope, one summand still appears as

`mu(A) * mu(d)`

with `A` a represented root-crossing source scale and `d` in the interval-prime
q^2 daughter window.  This file proves that this is already the ordinary
Möbius weight of the single descended integer `A*d`.

The proof uses no cancellation.  Choose the actual source-scale witness
`y=(t,(c,p))` for `A`.  Replacing its high cofactor by `d` gives another valid
`OrderedEulerCutShape`: every face prime is below `p`, while `d` is squarefree
and rough above `p`.  The existing ordered-cut coprimality theorem therefore
makes `d` coprime to the old low face, and roughness makes it coprime to `p`.
Since `A=p*P(t)`, Möbius multiplicativity absorbs the outer parity factor.

The same arithmetic also carries the true daughter scale:

`q^2*d <= floor(X_R/A)` implies `q^2*(A*d) <= X_R`.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- A represented source scale together with one q^2 daughter gives a genuine
coprime product coordinate.  The source-scale parity is exactly the Möbius
parity of that product, and the square-dilated scale survives multiplication by
`A`. -/
theorem lowWheelFrozenSourceScale_daughterProduct_data
    {R A q d : ℕ}
    (hA : A ∈ lowWheelFrozenSecondContactSourceScaleSet R)
    (hqO : q ∈ lowWheelFrozenSourceSquareResidualOwners
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A))
    (hd : d ∈ lowWheelFrozenSourceSquareResidualDaughterWindow
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q) :
    Nat.Coprime A d ∧
      canonicalMoebiusWeight A * canonicalMoebiusWeight d =
        canonicalMoebiusWeight (A * d) ∧
      q * q * (A * d) ≤ squareRootEndpoint R ∧
      R < A * d := by
  rcases Finset.mem_image.mp hA with ⟨y, hy, hyA⟩
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hfrozen := (Finset.mem_filter.mp hyFrozen).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
  have hpA : canonicalLargestPrimeFactor A =
      lowWheelTaggedDowncrossPivot y := by
    rw [← hyA]
    exact lowWheelFrozenSecondContact_sourceScale_largestPrime hy

  rcases Finset.mem_filter.mp hd with ⟨hdIcc, hdSq, hdRoughA, _hdLt⟩
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
  have hdRough : RoughAbove (lowWheelTaggedDowncrossPivot y) d := by
    simpa [hpA] using hdRoughA
  have hpNotD : ¬ lowWheelTaggedDowncrossPivot y ∣ d :=
    RoughAbove.not_dvd hsource.2.1 hd1 hdRough

  let z : OrderedEulerCutTaggedState :=
    (y.1, (d, lowWheelTaggedDowncrossPivot y))
  have hzShape : OrderedEulerCutShape z := by
    change (lowWheelTaggedDowncrossPivot y).Prime ∧
      1 ≤ d ∧ Squarefree d ∧
      ¬ lowWheelTaggedDowncrossPivot y ∣ d ∧
      (∀ r ∈ y.1, r.Prime ∧ r < lowWheelTaggedDowncrossPivot y) ∧
      RoughAbove (lowWheelTaggedDowncrossPivot y) d
    refine ⟨hsource.2.1, hd1, hdSq, hpNotD, ?_, hdRough⟩
    intro r hr
    exact ⟨
      prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hr),
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hr⟩

  have hhighLow := orderedEulerCut_highCofactor_coprime_lowProduct hzShape
  change Nat.Coprime d (primeFaceProduct y.1) at hhighLow
  have hdp : Nat.Coprime d (lowWheelTaggedDowncrossPivot y) :=
    ((hsource.2.1.coprime_iff_not_dvd).2 hpNotD).symm
  have hdA0 :
      Nat.Coprime d
        (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) :=
    Nat.Coprime.mul_right hdp hhighLow
  have hAeq :
      A = lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := by
    calc
      A = lowWheelFrozenSecondContactSourceScale y := hyA.symm
      _ = lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 := rfl
  have hcop : Nat.Coprime A d := by
    rw [hAeq]
    exact hdA0.symm

  have hmu : μ (A * d) = μ A * μ d :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hweight :
      canonicalMoebiusWeight A * canonicalMoebiusWeight d =
        canonicalMoebiusWeight (A * d) := by
    unfold canonicalMoebiusWeight
    rw [hmu]
    norm_cast

  rcases Finset.mem_image.mp hqO with ⟨c, hcResidual, howner⟩
  have hcFiber : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber
      (canonicalLargestPrimeFactor A) (squareRootEndpoint R / A) q :=
    mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mpr
      ⟨hcResidual, howner⟩
  have hqPrime :=
    (lowWheelFrozenSourceSquareResidualOwnerFiber_data hcFiber).1
  have hqqPos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hdUpper : d ≤ (squareRootEndpoint R / A) / (q * q) :=
    (Finset.mem_Icc.mp hdIcc).2
  have hq2d : q * q * d ≤ squareRootEndpoint R / A :=
    (Nat.le_div_iff_mul_le hqqPos).1 hdUpper
  have hAroot : R < A := lowWheelFrozenSourceScale_root_lt hA
  have hApos : 0 < A := by omega
  have hscaled0 : (q * q * d) * A ≤ squareRootEndpoint R :=
    (Nat.le_div_iff_mul_le hApos).1 hq2d
  have hscaled : q * q * (A * d) ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hscaled0
  have hAAd : A ≤ A * d := by
    calc
      A = A * 1 := by simp
      _ ≤ A * d := Nat.mul_le_mul_left A hd1
  exact ⟨hcop, hweight, hscaled, hAroot.trans_le hAAd⟩

end RHLean.Proof
