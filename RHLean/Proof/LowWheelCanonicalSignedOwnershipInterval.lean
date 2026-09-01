import Mathlib
import RHLean.Proof.LowWheelCanonicalDowncrossBoundaryMultiplicity
import RHLean.Arithmetic.SquarefreePrimeFaceSurjectivity

/-!
# Signed ownership intervals for canonical downcross states

`LowWheelCanonicalDowncrossBoundaryMultiplicity` proves that the Boolean faces
charging one fixed canonical downcross state inject by `primeFaceProduct` into a
single integer ownership window.  This file keeps the signs instead of taking
cardinalities.

For a fixed state `(c,k)`, write `p = minFac(c*k)`.  If the state is charged at
all, its charging-face products are exactly the squarefree integers

`R / k < a <= min (R / (k/p)) ((R^2-1) / (c*k))`.

Thus the alternating face mass is exactly the Mobius mass of that physical
integer interval.  This is an exact finite reindexing; no independence,
probability, norm, PNT estimate, or RH input is used.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

namespace SignedOwnershipInterval

/-- The exact upper endpoint of the face-product ownership interval for one
fixed physical state.  The first term is the root-side parent constraint; the
second is the physical square-endpoint product ceiling. -/
def lowWheelCanonicalDowncrossOwnershipUpper
    (R c k : ℕ) : ℕ :=
  min
    (R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k)))
    (squareRootEndpoint R / (c * k))

/-- Squarefree integer products in the exact ownership interval of `(c,k)`. -/
def lowWheelCanonicalDowncrossOwnershipProducts
    (R c k : ℕ) : Finset ℕ :=
  (Finset.Ioc (R / k)
      (lowWheelCanonicalDowncrossOwnershipUpper R c k)).filter Squarefree

@[simp] theorem mem_lowWheelCanonicalDowncrossOwnershipProducts
    {R c k a : ℕ} :
    a ∈ lowWheelCanonicalDowncrossOwnershipProducts R c k ↔
      R / k < a ∧
        a ≤ lowWheelCanonicalDowncrossOwnershipUpper R c k ∧
        Squarefree a := by
  simp [lowWheelCanonicalDowncrossOwnershipProducts, and_assoc]

/-- Every charging face also satisfies the physical product ceiling, so its
product lies in the *exact* state-dependent ownership interval. -/
theorem primeFaceProduct_mem_exactOwnershipInterval
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k)) :
    primeFaceProduct t ∈
      Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k) := by
  have hwindow := primeFaceProduct_mem_Ioc_of_mem_chargingFaces ht
  obtain ⟨htPow, hx⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht
  have hmem := mem_lowWheelCanonicalDowncrossPart.mp hx
  have hphys := mem_lowWheelCanonicalPhysicalStateSet.mp hmem.1
  obtain ⟨_hcRange, hkRange, _hsq, hcarrier⟩ := hphys
  obtain ⟨hc1, _hcR, _hhigh, htop⟩ := hcarrier
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkRange).1
  have hcpos : 0 < c := by omega
  have hckpos : 0 < c * k := Nat.mul_pos hcpos hkpos
  have htop' : primeFaceProduct t * (c * k) ≤ squareRootEndpoint R := by
    calc
      primeFaceProduct t * (c * k) =
          (c * primeFaceProduct t) * k := by ring
      _ ≤ squareRootEndpoint R := htop
  have htopDiv :
      primeFaceProduct t ≤ squareRootEndpoint R / (c * k) :=
    (Nat.le_div_iff_mul_le hckpos).mpr htop'
  refine Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hwindow).1, ?_⟩
  exact le_min (Finset.mem_Ioc.mp hwindow).2 htopDiv

/-- A charging-face product is squarefree.  This is read through its nonzero
Mobius value, whose sign is the Boolean face sign. -/
theorem squarefree_primeFaceProduct_of_mem_chargingFaces
    {R c k : ℕ} {t : Finset ℕ}
    (ht : t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k)) :
    Squarefree (primeFaceProduct t) := by
  obtain ⟨htPow, _hx⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht
  have htSub := Finset.mem_powerset.mp htPow
  have hmu := moebius_primeFaceProduct_eq_booleanCubeSign t
    (fun q hq => prime_of_mem_primesUpTo (htSub hq))
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  rw [hmu]
  simp [booleanCubeSign]

/-- **Exact ownership image.**  If `(c,k)` is charged at least once, the image
of all of its charging Boolean faces under `primeFaceProduct` is exactly the
squarefree population in its physical ownership interval. -/
theorem image_primeFaceProduct_chargingFaces_eq_ownershipProducts
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty) :
    (lowWheelCanonicalDowncrossChargingFaces R (c, k)).image primeFaceProduct =
      lowWheelCanonicalDowncrossOwnershipProducts R c k := by
  classical
  obtain ⟨t0, ht0⟩ := hne
  obtain ⟨_ht0Pow, hx0⟩ := mem_lowWheelCanonicalDowncrossChargingFaces.mp ht0
  have hdown0 := mem_lowWheelCanonicalDowncrossPart.mp hx0
  have hphys0 := mem_lowWheelCanonicalPhysicalStateSet.mp hdown0.1
  obtain ⟨hcRange, hkRange, hsqc, hcarrier0⟩ := hphys0
  obtain ⟨hc1, hcR, _hhigh0, _htop0⟩ := hcarrier0
  obtain ⟨hp, hpc, hpk, _hparent0, _hchild0⟩ :=
    lowWheelCanonicalDowncrossPart_adjacent_shell hx0
  have hkpos : 0 < k := (Finset.mem_Icc.mp hkRange).1
  have hcpos : 0 < c := by omega
  have hjpos :
      0 < k / lowWheelCanonicalCofactorQuotientPivot (c, k) :=
    Nat.div_pos (Nat.le_of_dvd hkpos hpk) hp.pos
  have hckpos : 0 < c * k := Nat.mul_pos hcpos hkpos
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
    apply mem_lowWheelCanonicalDowncrossOwnershipProducts.mpr
    have hI := primeFaceProduct_mem_exactOwnershipInterval ht
    exact ⟨(Finset.mem_Ioc.mp hI).1, (Finset.mem_Ioc.mp hI).2,
      squarefree_primeFaceProduct_of_mem_chargingFaces ht⟩
  · intro ha
    obtain ⟨hlo, hupper, hsqa⟩ :=
      mem_lowWheelCanonicalDowncrossOwnershipProducts.mp ha
    have hparent :
        a ≤ R / (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) :=
      hupper.trans (min_le_left _ _)
    have htopDiv : a ≤ squareRootEndpoint R / (c * k) :=
      hupper.trans (min_le_right _ _)
    have haR : a ≤ R :=
      hparent.trans (Nat.div_le_self _ _)
    let t : Finset ℕ := squarefreePrimeFace a
    have htSub : t ⊆ primesUpTo R := by
      simpa [t] using squarefreePrimeFace_subset_primesUpTo hsqa haR
    have htPow : t ∈ (primesUpTo R).powerset :=
      Finset.mem_powerset.mpr htSub
    have hprod : primeFaceProduct t = a := by
      simpa [t] using primeFaceProduct_squarefreePrimeFace hsqa
    have hhigh : R < a * k :=
      (Nat.div_lt_iff_lt_mul hkpos).mp hlo
    have htopMul : a * (c * k) ≤ squareRootEndpoint R :=
      (Nat.le_div_iff_mul_le hckpos).mp htopDiv
    have htop : (c * a) * k ≤ squareRootEndpoint R := by
      calc
        (c * a) * k = a * (c * k) := by ring
        _ ≤ squareRootEndpoint R := htopMul
    have hparentMul :
        a * (k / lowWheelCanonicalCofactorQuotientPivot (c, k)) ≤ R :=
      (Nat.le_div_iff_mul_le hjpos).mp hparent
    have hphysical : (c, k) ∈ lowWheelCanonicalPhysicalStateSet R t := by
      apply mem_lowWheelCanonicalPhysicalStateSet.mpr
      refine ⟨hcRange, hkRange, hsqc, ?_⟩
      rw [show primeFaceProduct t = a from hprod]
      exact ⟨hc1, hcR, hhigh, htop⟩
    have hx : (c, k) ∈ lowWheelCanonicalDowncrossPart R t := by
      apply mem_lowWheelCanonicalDowncrossPart.mpr
      refine ⟨hphysical, hpc, ?_⟩
      rw [hprod]
      exact hparentMul
    apply Finset.mem_image.mpr
    exact ⟨t,
      mem_lowWheelCanonicalDowncrossChargingFaces.mpr ⟨htPow, hx⟩,
      hprod⟩

/-- **Signed ownership interval.**  The Boolean alternating mass of all faces
charging one fixed physical state is exactly the Mobius mass of its integer
ownership interval.  Nonsquarefree integers may be inserted freely because
their Mobius weight is zero. -/
theorem sum_booleanCubeSign_chargingFaces_eq_moebiusOwnershipInterval
    {R c k : ℕ}
    (hne : (lowWheelCanonicalDowncrossChargingFaces R (c, k)).Nonempty) :
    (∑ t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k),
        booleanCubeSign t) =
      ∑ a ∈ Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k), μ a := by
  classical
  let F := lowWheelCanonicalDowncrossChargingFaces R (c, k)
  let I := Finset.Ioc (R / k)
    (lowWheelCanonicalDowncrossOwnershipUpper R c k)
  have hface :
      (∑ t ∈ F, booleanCubeSign t) =
        ∑ t ∈ F, μ (primeFaceProduct t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htData := mem_lowWheelCanonicalDowncrossChargingFaces.mp (by simpa [F] using ht)
    have htSub := Finset.mem_powerset.mp htData.1
    symm
    exact moebius_primeFaceProduct_eq_booleanCubeSign t
      (fun q hq => prime_of_mem_primesUpTo (htSub hq))
  have himage : F.image primeFaceProduct =
      lowWheelCanonicalDowncrossOwnershipProducts R c k := by
    simpa [F] using
      image_primeFaceProduct_chargingFaces_eq_ownershipProducts hne
  have hinj :
      ∀ a ∈ F, ∀ b ∈ F, primeFaceProduct a = primeFaceProduct b → a = b := by
    intro a ha b hb hab
    exact primeFaceProduct_injOn_chargingFaces R (c, k)
      (by simpa [F] using ha) (by simpa [F] using hb) hab
  calc
    (∑ t ∈ lowWheelCanonicalDowncrossChargingFaces R (c, k),
        booleanCubeSign t) = ∑ t ∈ F, booleanCubeSign t := by rfl
    _ = ∑ t ∈ F, μ (primeFaceProduct t) := hface
    _ = ∑ a ∈ F.image primeFaceProduct, μ a := by
      symm
      rw [Finset.sum_image]
      exact hinj
    _ = ∑ a ∈ lowWheelCanonicalDowncrossOwnershipProducts R c k, μ a := by
      rw [himage]
    _ = ∑ a ∈ I, μ a := by
      unfold lowWheelCanonicalDowncrossOwnershipProducts
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hsq : Squarefree a
      · simp [hsq]
      · simp [hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    _ = ∑ a ∈ Finset.Ioc (R / k)
        (lowWheelCanonicalDowncrossOwnershipUpper R c k), μ a := by rfl

end SignedOwnershipInterval

end RHLean.Proof
