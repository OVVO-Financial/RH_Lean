import Mathlib
import RHLean.Proof.LowWheelFrozenSecondContactGlobalTelescope
import RHLean.Arithmetic.PrimeFaceMoebius

/-!
# Signed source-scale reassembly for frozen second contacts

The pointwise strict descent in `LowWheelFrozenSecondContactGlobalTelescope`
associates to every frozen second-contact source `y=(t,(c,p))` the scale

`A = p * P(t)`

and the strictly smaller cutoff

`B = floor(X_R / A) < R`.

This file performs the missing signed reassembly before any norm is taken.
At fixed `A`, the Boolean face sign is frozen by the arithmetic integer `A`:
`A` is the prime-face product of `insert p t`, so `mu(A) = -sign(t)`.
The only varying signed factor is therefore `mu(c)`.

The cofactor map is injective on a fixed-`A` fibre: the physical child integer
is exactly `c*A`, and active ordered Euler cuts are already injective by that
integer.  Hence there is no multiplicity loss when the fibre is reindexed by
its cofactors.

The result is an exact global identity

`source mass = - sum_A mu(A) * cofactorMass(R,A)`

where every cofactor in the `A`-fibre lies in the strict lower-scale
second-contact shell at `B=X_R/A<R`.

No absolute value, density estimate, PNT input, Mertens hypothesis, or
asymptotic estimate appears.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Root-crossing/death scale carried by a frozen second-contact source. -/
def lowWheelFrozenSecondContactSourceScale
    (y : LowWheelTaggedDowncrossState) : ℕ :=
  lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1

/-- Source scales actually represented at root `R`. -/
def lowWheelFrozenSecondContactSourceScaleSet (R : ℕ) : Finset ℕ :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).image
    lowWheelFrozenSecondContactSourceScale

/-- Exact source fibre at one represented scale `A`. -/
def lowWheelFrozenSecondContactSourceScaleFiber
    (R A : ℕ) : Finset LowWheelTaggedDowncrossState :=
  (lowWheelCanonicalRepeatedFrozenSecondContactPart R).filter fun y =>
    lowWheelFrozenSecondContactSourceScale y = A

@[simp] theorem mem_lowWheelFrozenSecondContactSourceScaleFiber
    {R A : ℕ} {y : LowWheelTaggedDowncrossState} :
    y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A ↔
      y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R ∧
        lowWheelFrozenSecondContactSourceScale y = A := by
  simp [lowWheelFrozenSecondContactSourceScaleFiber]

/-- Cofactors represented in one fixed source-scale fibre. -/
def lowWheelFrozenSecondContactSourceScaleCofactors
    (R A : ℕ) : Finset ℕ :=
  (lowWheelFrozenSecondContactSourceScaleFiber R A).image fun y => y.2.1

/-- Signed Möbius mass of the fixed-scale cofactor image. -/
def lowWheelFrozenSecondContactSourceScaleCofactorMass
    (R A : ℕ) : ℂ :=
  ∑ c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A,
    canonicalMoebiusWeight c

/-- The source scale is literally the prime-face product obtained by adjoining
the frozen pivot to the old Boolean face. -/
theorem lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    lowWheelFrozenSecondContactSourceScale y =
      primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    have hlt :=
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hp
    exact (Nat.lt_irrefl _) hlt
  simp [lowWheelFrozenSecondContactSourceScale, primeFaceProduct, hpNot]

/-- **Fixed-scale sign law.**  The old Boolean-face sign is determined by the
single arithmetic integer `A=p*P(t)`: `mu(A)=-sign(t)`. -/
theorem lowWheelFrozenSecondContactSourceScale_moebius_eq_neg_faceSign
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) =
      -(booleanCubeSign y.1 : ℂ) := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  have hfrozen := (Finset.mem_filter.mp hyFrozen).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have ht := (mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged).1
  have hpNot : lowWheelTaggedDowncrossPivot y ∉ y.1 := by
    intro hp
    have hlt :=
      lowWheelCanonicalRepeatedFrozenCofactor_facePrime_lt_pivot hyFrozen hp
    exact (Nat.lt_irrefl _) hlt
  have hprime :
      ∀ r ∈ insert (lowWheelTaggedDowncrossPivot y) y.1, r.Prime := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r
      exact hsource.2.1
    · exact prime_of_mem_primesUpTo ((Finset.mem_powerset.mp ht) hr)
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign
    (insert (lowWheelTaggedDowncrossPivot y) y.1) hprime
  have hsign :
      booleanCubeSign (insert (lowWheelTaggedDowncrossPivot y) y.1) =
        -booleanCubeSign y.1 := by
    unfold booleanCubeSign
    rw [Finset.card_insert_of_notMem hpNot, pow_succ]
    ring
  have hmuZ :
      μ (lowWheelFrozenSecondContactSourceScale y) =
        -booleanCubeSign y.1 := by
    calc
      μ (lowWheelFrozenSecondContactSourceScale y) =
          μ (primeFaceProduct (insert (lowWheelTaggedDowncrossPivot y) y.1)) := by
        rw [lowWheelFrozenSecondContactSourceScale_eq_insertPivotFaceProduct hy]
      _ = booleanCubeSign (insert (lowWheelTaggedDowncrossPivot y) y.1) := hmu
      _ = -booleanCubeSign y.1 := hsign
  simpa [canonicalMoebiusWeight] using
    congrArg (fun z : ℤ => (z : ℂ)) hmuZ

/-- The complete source charge at fixed scale is the cofactor Möbius weight
multiplied by the fixed arithmetic sign `-mu(A)`. -/
theorem lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
      -(canonicalMoebiusWeight (lowWheelFrozenSecondContactSourceScale y) *
        canonicalMoebiusWeight y.2.1) := by
  rw [lowWheelFrozenSecondContactSourceScale_moebius_eq_neg_faceSign hy]
  ring

/-- The physical child integer factors exactly as cofactor times source scale. -/
theorem lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale
    {R : ℕ} {y : LowWheelTaggedDowncrossState}
    (hy : y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R) :
    orderedEulerCutChildInteger y =
      y.2.1 * lowWheelFrozenSecondContactSourceScale y := by
  have hyFrozen := (Finset.mem_filter.mp hy).1
  have hsource := lowWheelCanonicalRepeatedFrozenCofactor_source_data hyFrozen
  calc
    orderedEulerCutChildInteger y =
        y.2.1 *
          (lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1) := by
      simp only [orderedEulerCutChildInteger, orderedEulerCutHighCofactor,
        orderedEulerCutPivot, orderedEulerCutLowProduct]
      rw [hsource.1]
    _ = y.2.1 * lowWheelFrozenSecondContactSourceScale y := by
      rfl

/-- **No multiplicity at fixed source scale.**  If two sources have the same
`A` and the same cofactor `c`, then their physical child integers are both
`c*A`, so ordered-Euler uniqueness recovers the source itself. -/
theorem lowWheelFrozenSecondContactSourceScaleFiber_cofactor_injOn
    (R A : ℕ) :
    Set.InjOn (fun y : LowWheelTaggedDowncrossState => y.2.1)
      (lowWheelFrozenSecondContactSourceScaleFiber R A :
        Set LowWheelTaggedDowncrossState) := by
  intro y hy z hz hcofactor
  have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hy
  have hzd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hz
  have hchild : orderedEulerCutChildInteger y = orderedEulerCutChildInteger z := by
    calc
      orderedEulerCutChildInteger y =
          y.2.1 * lowWheelFrozenSecondContactSourceScale y :=
        lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale hyd.1
      _ = y.2.1 * A := by rw [hyd.2]
      _ = z.2.1 * A := by rw [hcofactor]
      _ = z.2.1 * lowWheelFrozenSecondContactSourceScale z := by rw [hzd.2]
      _ = orderedEulerCutChildInteger z :=
        (lowWheelFrozenSecondContact_child_eq_cofactor_mul_sourceScale hzd.1).symm
  have hyFrozen := (Finset.mem_filter.mp hyd.1).1
  have hzFrozen := (Finset.mem_filter.mp hzd.1).1
  exact orderedEulerCutChildInteger_injective_on_carrier
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hyFrozen)
    (lowWheelCanonicalRepeatedFrozenCofactor_mem_orderedEulerCutCarrier hzFrozen)
    hchild

/-- Reindexing one fixed-`A` fibre by its cofactor loses no multiplicity. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactorMass_eq_source_sum
    (R A : ℕ) :
    lowWheelFrozenSecondContactSourceScaleCofactorMass R A =
      ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight y.2.1 := by
  unfold lowWheelFrozenSecondContactSourceScaleCofactorMass
    lowWheelFrozenSecondContactSourceScaleCofactors
  rw [Finset.sum_image]
  intro y hy z hz heq
  exact lowWheelFrozenSecondContactSourceScaleFiber_cofactor_injOn R A hy hz heq

/-- **Exact signed fixed-scale recurrence.**  Every source in the `A` fibre has
the same outer sign `-mu(A)`, and the inner object is the ordinary signed
Möbius mass of its cofactor image. -/
theorem lowWheelFrozenSecondContactSourceScaleFiber_sum_eq
    (R A : ℕ) :
    (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -(canonicalMoebiusWeight A *
        lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
  calc
    (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hy
      calc
        canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) =
            -(canonicalMoebiusWeight
                (lowWheelFrozenSecondContactSourceScale y) *
              canonicalMoebiusWeight y.2.1) :=
          lowWheelFrozenSecondContactSource_weight_eq_neg_scale_mul_cofactor hyd.1
        _ = -(canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
          rw [hyd.2]
    _ = -(∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
        canonicalMoebiusWeight A * canonicalMoebiusWeight y.2.1) := by
      rw [Finset.sum_neg_distrib]
    _ = -(canonicalMoebiusWeight A *
        (∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1)) := by
      rw [Finset.mul_sum]
    _ = -(canonicalMoebiusWeight A *
        lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      rw [lowWheelFrozenSecondContactSourceScaleCofactorMass_eq_source_sum]

/-- The complete source ledger is the sum of its exact source-scale fibres. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_sourceScaleFibers
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ) := by
  have hmaps :
      ∀ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
        lowWheelFrozenSecondContactSourceScale y ∈
          lowWheelFrozenSecondContactSourceScaleSet R := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun y => canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ))
  simpa [lowWheelFrozenSecondContactSourceScaleFiber] using hfib.symm

/-- **Global strict-scale signed reassembly.**  The entire frozen second-contact
source ledger is a signed sum of cofactor masses indexed by the arithmetic
source scale `A`.  No absolute value has been taken. -/
theorem lowWheelFrozenSecondContactSource_sum_eq_neg_sourceScaleCofactorMass
    (R : ℕ) :
    (∑ y ∈ lowWheelCanonicalRepeatedFrozenSecondContactPart R,
      canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      -(∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
  rw [lowWheelFrozenSecondContactSource_sum_eq_sourceScaleFibers]
  calc
    (∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        ∑ y ∈ lowWheelFrozenSecondContactSourceScaleFiber R A,
          canonicalMoebiusWeight y.2.1 * (booleanCubeSign y.1 : ℂ)) =
      ∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        -(canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      exact lowWheelFrozenSecondContactSourceScaleFiber_sum_eq R A
    _ = -(∑ A ∈ lowWheelFrozenSecondContactSourceScaleSet R,
        canonicalMoebiusWeight A *
          lowWheelFrozenSecondContactSourceScaleCofactorMass R A) := by
      rw [Finset.sum_neg_distrib]

/-- **Every fixed-scale cofactor is a strict lower-scale second contact.**
For `c` represented in the `A` fibre, put `B=floor(X_R/A)`, `q=P+(c)`, and
`d=c/q`.  Then `q*d <= B < q^2*d`, `P+(d)<q`, and crucially `B<R`. -/
theorem lowWheelFrozenSecondContactSourceScaleCofactor_lowerScaleSecondContact
    {R A c : ℕ}
    (hc : c ∈ lowWheelFrozenSecondContactSourceScaleCofactors R A) :
    let B := squareRootEndpoint R / A
    let q := canonicalLargestPrimeFactor c
    let d := canonicalCofactor c
    q.Prime ∧ Squarefree d ∧ canonicalLargestPrimeFactor d < q ∧
      q * d = c ∧ q * d ≤ B ∧ B < q * q * d ∧ B < R := by
  rcases Finset.mem_image.mp hc with ⟨y, hyFiber, rfl⟩
  have hyd := mem_lowWheelFrozenSecondContactSourceScaleFiber.mp hyFiber
  have hscale :
      lowWheelTaggedDowncrossPivot y * primeFaceProduct y.1 = A := by
    simpa [lowWheelFrozenSecondContactSourceScale] using hyd.2
  have h := lowWheelFrozenSecondContact_source_lowerScaleSecondContact hyd.1
  simpa [lowWheelFrozenCofactorTopPrime, hscale] using h

end RHLean.Proof
