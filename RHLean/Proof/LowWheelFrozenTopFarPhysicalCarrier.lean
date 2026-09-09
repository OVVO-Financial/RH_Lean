import Mathlib
import RHLean.Proof.LowWheelCanonicalRepeatedTerminalInternalMate
import RHLean.Proof.LowWheelFullFaceQuotientOthello

/-!
# Frozen/top/far residual on one tagged physical carrier

The post-#618 residual is

`FarTransport - InternalTerminalMate - FrozenTopImage`.

Before comparing that signed combination with the Go crossing coordinates, the
three terms must live on one literal physical carrier.  This file performs the
carrier bookkeeping without taking a norm.

The complete face/quotient Othello coordinate has invariant high product
`P(t) * k`.  We therefore define its far region by the same cutoff used by the
far-prime transport, `R + 8 <= P(t) * k`.  The frozen top image is automatically
far: its top/bottom move multiplies an already post-root high product by a prime
at least two.  The internal-terminal mate is split exactly into its far part
and the complementary seven-integer root strip.

No root-equality assumption is made.  In particular this construction remains
valid when the Go root-equality carrier is empty (for example at prime roots).
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open FrozenCofactorTopBottom

attribute [local instance] Classical.propDecidable

/-- High product represented by one tagged physical occurrence. -/
def lowWheelTaggedHighProduct (z : LowWheelFullTaggedPhysicalState) : ℕ :=
  primeFaceProduct z.1 * z.2.2

/-- The literal far part of the complete tagged physical transport carrier. -/
def lowWheelFarTaggedPhysicalCarrier (R : ℕ) :
    Finset LowWheelFullTaggedPhysicalState :=
  (lowWheelFullTaggedPhysicalCarrier R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

@[simp] theorem mem_lowWheelFarTaggedPhysicalCarrier
    {R : ℕ} {z : LowWheelFullTaggedPhysicalState} :
    z ∈ lowWheelFarTaggedPhysicalCarrier R ↔
      z ∈ lowWheelFullTaggedPhysicalCarrier R ∧
        R + 8 ≤ lowWheelTaggedHighProduct z := by
  simp [lowWheelFarTaggedPhysicalCarrier]

/-- The internal-terminal mate image already lies on the same complete tagged
physical carrier used by the face/quotient Othello move. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R ⊆
      lowWheelFullTaggedPhysicalCarrier R := by
  intro z hz
  have hz' :=
    lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_transport R hz
  rcases mem_lowWheelCanonicalTaggedPhysicalCarrier.mp hz' with ⟨ht, hx⟩
  exact mem_lowWheelFullTaggedPhysicalCarrier.mpr ⟨ht, hx⟩

/-- The frozen top image also consists of literal occurrences of the complete
tagged physical carrier. -/
theorem lowWheelFrozenCofactorTopImage_subset_fullPhysical
    (R : ℕ) :
    lowWheelFrozenCofactorTopImage R ⊆ lowWheelFullTaggedPhysicalCarrier R := by
  intro z hz
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  apply mem_lowWheelFullTaggedPhysicalCarrier.mpr
  exact ⟨htag.1, lowWheelFrozenCofactorTopToggle_mem_physical hy⟩

/-- The frozen top relocation is automatically in the far region.  The source
already has `R < P(t) * k`; the top move multiplies that high product by the
largest cofactor prime, which is at least two. -/
theorem lowWheelFrozenCofactorTopImage_highProduct_ge_far
    {R : ℕ} (hR : 6 ≤ R) {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    R + 8 ≤ lowWheelTaggedHighProduct z := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  let q := lowWheelFrozenCofactorTopPrime y
  have hqPrime : q.Prime := by
    simpa [q] using (lowWheelFrozenCofactorTopPrime_data hy).1
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hcarrier := (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.2.2
  have hhigh : R < primeFaceProduct y.1 * y.2.2 := hcarrier.2.2.1
  have hbase : R + 1 ≤ primeFaceProduct y.1 * y.2.2 := by omega
  have hdouble :
      2 * (primeFaceProduct y.1 * y.2.2) ≤
        q * (primeFaceProduct y.1 * y.2.2) := by
    exact Nat.mul_le_mul_right (primeFaceProduct y.1 * y.2.2) hqTwo
  have hfar :
      R + 8 ≤ q * (primeFaceProduct y.1 * y.2.2) := by
    have hfirst :
        R + 8 ≤ 2 * (primeFaceProduct y.1 * y.2.2) := by omega
    exact hfirst.trans hdouble
  rw [lowWheelFrozenCofactorTopToggle_eq hy]
  simpa [lowWheelTaggedHighProduct, q, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hfar

/-- Hence the complete frozen top image is a subcarrier of the far physical
region. -/
theorem lowWheelFrozenCofactorTopImage_subset_farPhysical
    (R : ℕ) (hR : 6 ≤ R) :
    lowWheelFrozenCofactorTopImage R ⊆ lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨lowWheelFrozenCofactorTopImage_subset_fullPhysical R hz,
      lowWheelFrozenCofactorTopImage_highProduct_ge_far hR hz⟩

/-- The internal-terminal mate image below the far cutoff.  Since every such
mate is already post-root, this is exactly the seven-integer strip
`R < P(t) <= R+7`. -/
def lowWheelCanonicalRepeatedTerminalInternalMateNearImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalMateImage R).filter fun z =>
    lowWheelTaggedHighProduct z < R + 8

/-- The complementary far part of the internal-terminal mate image. -/
def lowWheelCanonicalRepeatedTerminalInternalMateFarImage
    (R : ℕ) : Finset LowWheelTaggedCofactorQuotientState :=
  (lowWheelCanonicalRepeatedTerminalInternalMateImage R).filter fun z =>
    R + 8 ≤ lowWheelTaggedHighProduct z

/-- Exact cutoff partition of the internal-terminal mate image. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_eq_near_union_far
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateImage R =
      lowWheelCanonicalRepeatedTerminalInternalMateNearImage R ∪
        lowWheelCanonicalRepeatedTerminalInternalMateFarImage R := by
  ext z
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hz
    by_cases hfar : R + 8 ≤ lowWheelTaggedHighProduct z
    · exact Or.inr ⟨hz, hfar⟩
    · exact Or.inl ⟨hz, by omega⟩
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
    · exact hz
    · exact hz

/-- The near and far internal-terminal mate pieces are disjoint. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateNear_disjoint_far
    (R : ℕ) :
    Disjoint
      (lowWheelCanonicalRepeatedTerminalInternalMateNearImage R)
      (lowWheelCanonicalRepeatedTerminalInternalMateFarImage R) := by
  rw [Finset.disjoint_left]
  intro z hnear hfar
  have hlt := (Finset.mem_filter.mp hnear).2
  have hge := (Finset.mem_filter.mp hfar).2
  omega

/-- The far internal-terminal mate image is a literal subcarrier of the same far
physical region as the frozen top image. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateFarImage_subset_farPhysical
    (R : ℕ) :
    lowWheelCanonicalRepeatedTerminalInternalMateFarImage R ⊆
      lowWheelFarTaggedPhysicalCarrier R := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨himage, hfar⟩
  exact mem_lowWheelFarTaggedPhysicalCarrier.mpr
    ⟨lowWheelCanonicalRepeatedTerminalInternalMateImage_subset_fullPhysical R himage,
      hfar⟩

/-- Every internal-terminal mate has state `(1,1)`; all of its arithmetic data
is carried by the Boolean face. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one
    {R : ℕ} {z : LowWheelTaggedCofactorQuotientState}
    (hz : z ∈ lowWheelCanonicalRepeatedTerminalInternalMateImage R) :
    z.2 = (1, 1) := by
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  rfl

/-- A frozen top image has quotient at least two, so it cannot coincide with an
internal-terminal mate occurrence. -/
theorem lowWheelFrozenCofactorTopImage_quotient_two_le
    {R : ℕ} {z : LowWheelTaggedDowncrossState}
    (hz : z ∈ lowWheelFrozenCofactorTopImage R) :
    2 ≤ z.2.2 := by
  rcases mem_lowWheelFrozenCofactorTopImage.mp hz with ⟨y, hy, rfl⟩
  let q := lowWheelFrozenCofactorTopPrime y
  have hqPrime : q.Prime := by
    simpa [q] using (lowWheelFrozenCofactorTopPrime_data hy).1
  have hfrozen := (Finset.mem_filter.mp hy).1
  have hrepeated := (Finset.mem_filter.mp hfrozen).1
  have htagged := (Finset.mem_filter.mp hrepeated).1
  have htag := mem_lowWheelCanonicalTaggedDowncrossCarrier.mp htagged
  have hphys := (mem_lowWheelCanonicalDowncrossPart.mp htag.2).1
  have hkOne : 1 ≤ y.2.2 :=
    (Finset.mem_Icc.mp (mem_lowWheelCanonicalPhysicalStateSet.mp hphys).2.1).1
  rw [lowWheelFrozenCofactorTopToggle_eq hy]
  dsimp only
  have hqTwo : 2 ≤ q := hqPrime.two_le
  have hmul : q ≤ q * y.2.2 := by
    simpa using Nat.le_mul_of_pos_right q (by omega : 0 < y.2.2)
  exact hqTwo.trans hmul

/-- The two already-subtracted physical image populations are genuinely
disjoint. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateImage_disjoint_topImage
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalMateImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  rw [Finset.disjoint_left]
  intro z hint htop
  have hone := lowWheelCanonicalRepeatedTerminalInternalMateImage_state_eq_one hint
  have htwo := lowWheelFrozenCofactorTopImage_quotient_two_le htop
  have hquot : z.2.2 = 1 := congrArg Prod.snd hone
  omega

/-- In particular the far internal image and the top image are disjoint
subcarriers of the far physical region. -/
theorem lowWheelCanonicalRepeatedTerminalInternalMateFarImage_disjoint_topImage
    (R : ℕ) :
    Disjoint (lowWheelCanonicalRepeatedTerminalInternalMateFarImage R)
      (lowWheelFrozenCofactorTopImage R) := by
  apply Finset.disjoint_left.mpr
  intro z hfar htop
  exact Finset.disjoint_left.mp
    (lowWheelCanonicalRepeatedTerminalInternalMateImage_disjoint_topImage R)
    z (Finset.mem_filter.mp hfar).1 htop

end RHLean.Proof
