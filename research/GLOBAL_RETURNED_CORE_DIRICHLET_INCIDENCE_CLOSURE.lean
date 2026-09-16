import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING»

/-!
# Dirichlet closure of the finite threshold incidence

The threshold potential `F_R = w_R - 1` is the right coordinate on complete
owner edges because the constant mode cancels.  At a physical clipped edge,
however, the missing child is not an `F_R`-zero mode of the actual AMP site:
the physical coefficient is extended by zero outside `X_R`.

This file therefore introduces the literal Dirichlet extension

  wD_R(n) = w_R(n)   for n <= X_R,
           = 0       for n > X_R.

Its owner incidence closes the current first-owner cell exactly:

* on an admitted p-edge, `Delta_p wD = w(a)-w(pa)`, hence the compensated
  `L-J` site;
* on a clipped p-edge, `Delta_p wD = w(a)`, hence the literal clipped `C` site.

Thus the whole p-free base-cell incidence amplitude is

  (L-J) + C = Base + Child,

and the ordinary polarization identity becomes the already-compiled signed
cell telescope without ever introducing a standalone `C^2` estimate.

The key carrier theorem is also proved: if an admitted p-parent `a` is moved by
a larger fresh prime `r`, and `r*a` remains physical while `p*r*a` leaves the
physical clock, then `r*a` is literally in the named clipped p-base fibre of
the same lower-signature cell.  Hence the incomplete next-owner corner is not
a new residual coordinate.

No norm, Cauchy--Schwarz estimate, spectral approximation, or RH input is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Actual AMP site coefficient with Dirichlet zero extension outside the
physical square-root endpoint. -/
def lowOwnerPhysicalDirichletWeight (R n : ℕ) : ℝ :=
  if n ≤ squareRootEndpoint R then
    lowOwnerZeroFrequencyMobiusWeight R n
  else 0

/-- Owner incidence of the Dirichlet-extended AMP coefficient. -/
def lowOwnerPhysicalDirichletIncidenceWeight
    (R p n : ℕ) : ℝ :=
  lowOwnerPhysicalDirichletWeight R n -
    lowOwnerPhysicalDirichletWeight R (p * n)

/-- Inside the physical clock, the Dirichlet extension is the actual AMP
coefficient. -/
theorem lowOwnerPhysicalDirichletWeight_eq_weight_of_le
    {R n : ℕ} (hn : n ≤ squareRootEndpoint R) :
    lowOwnerPhysicalDirichletWeight R n =
      lowOwnerZeroFrequencyMobiusWeight R n := by
  simp [lowOwnerPhysicalDirichletWeight, hn]

/-- Outside the physical clock, the Dirichlet extension vanishes. -/
theorem lowOwnerPhysicalDirichletWeight_eq_zero_of_lt
    {R n : ℕ} (hn : squareRootEndpoint R < n) :
    lowOwnerPhysicalDirichletWeight R n = 0 := by
  simp [lowOwnerPhysicalDirichletWeight, Nat.not_le_of_gt hn]

/-- **Admitted edge dictionary.**  On an admitted p-parent, Dirichlet incidence
is exactly the compensated AMP signed site. -/
theorem lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_compensatedSite
    {R p a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig) :
    lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a =
      lowOwnerFirstOwnerCompensatedSite R p a := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, _hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, _hmu⟩
  have haX : a ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  unfold lowOwnerPhysicalDirichletIncidenceWeight
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX,
    lowOwnerPhysicalDirichletWeight_eq_weight_of_le hpaX]
  rw [lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le]
  unfold lowOwnerFirstOwnerCompensatedSite
  ring

/-- **Clipped edge dictionary.**  On a clipped p-parent, Dirichlet incidence is
exactly the literal clipped AMP site. -/
theorem lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_clippedSite
    {R p a : ℕ} {sig : Finset ℕ}
    (ha : a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig) :
    lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a =
      lowOwnerZeroFrequencyMobiusSite R a := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, _hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, _hmu⟩
  have haX : a ≤ squareRootEndpoint R := (Finset.mem_Icc.mp haIcc).2
  unfold lowOwnerPhysicalDirichletIncidenceWeight
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX,
    lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hpaX]
  unfold lowOwnerZeroFrequencyMobiusSite
  ring

/-- Dirichlet incidence amplitude on the whole p-free base branch of one cell. -/
def lowOwnerFirstOwnerDirichletIncidenceAmplitude
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerBaseFiber R p sig,
    lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a

/-- The whole base fibre splits into admitted and clipped parts for the
Dirichlet incidence weight. -/
theorem lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_admitted_add_clipped
    (R p : ℕ) (sig : Finset ℕ) :
    lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig =
      (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig,
        lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a) +
      ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig,
        lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a := by
  unfold lowOwnerFirstOwnerDirichletIncidenceAmplitude
    lowOwnerFirstOwnerAdmittedBaseFiber lowOwnerFirstOwnerClippedBaseFiber
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerBaseFiber R p sig)
      (p := fun a => p * a ≤ squareRootEndpoint R)
      (f := fun a =>
        lowOwnerPhysicalDirichletIncidenceWeight R p a * realMoebiusStep a)).symm

/-- **Exact Dirichlet cell closure.**  The one incidence amplitude on the whole
p-free base branch is the compensated interior plus the literal clipped exit. -/
theorem lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_compensated_add_clipped
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig =
      lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig +
        lowOwnerFirstOwnerClippedAmplitude R p sig := by
  rw [lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_admitted_add_clipped]
  unfold lowOwnerFirstOwnerCompensatedInteriorAmplitude
    lowOwnerFirstOwnerClippedAmplitude
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    exact lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_compensatedSite hp ha
  · apply Finset.sum_congr rfl
    intro a ha
    exact lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_clippedSite ha

/-- The same amplitude is exactly the full base branch plus the actual child
branch. -/
theorem lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_base_add_child
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig =
      lowOwnerFirstOwnerBaseAmplitude R p sig +
        lowOwnerFirstOwnerChildAmplitude R p sig := by
  calc
    lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig =
        lowOwnerFirstOwnerCompensatedInteriorAmplitude R p sig +
          lowOwnerFirstOwnerClippedAmplitude R p sig :=
      lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_compensated_add_clipped hp
    _ = lowOwnerFirstOwnerBaseAmplitude R p sig +
          lowOwnerFirstOwnerChildAmplitude R p sig :=
      (lowOwnerFirstOwnerBase_add_child_eq_compensated_add_clipped hp).symm

/-- **Dirichlet polarization form of the signed cell telescope.**  The clipped
population is inside the single incidence amplitude; no standalone clipped
square is introduced. -/
theorem two_mul_lowOwnerFirstOwnerCellGram_eq_dirichletIncidence_sq_sub_branches
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    2 * lowOwnerFirstOwnerCellGram R p sig =
      lowOwnerFirstOwnerDirichletIncidenceAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerBaseAmplitude R p sig ^ 2 -
        lowOwnerFirstOwnerChildAmplitude R p sig ^ 2 := by
  rw [lowOwnerFirstOwnerDirichletIncidenceAmplitude_eq_base_add_child hp]
  unfold lowOwnerFirstOwnerCellGram
  ring

/-- Multiplying by a fresh prime strictly above `p` does not change any prime
coordinate below `p`. -/
theorem squarefreeLowerPrimeSignature_mul_larger_prime
    {p r a : ℕ} (hr : r.Prime) (hpr : p < r) (ha : 0 < a) :
    squarefreeLowerPrimeSignature p (r * a) =
      squarefreeLowerPrimeSignature p a := by
  unfold squarefreeLowerPrimeSignature squarefreePrimeFace
  rw [primeFactors_prime_mul hr (Nat.ne_of_gt ha)]
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hq | hqa, hqp⟩
    · subst q
      omega
    · exact ⟨hqa, hqp⟩
  · rintro ⟨hqa, hqp⟩
    exact ⟨Or.inr hqa, hqp⟩

/-- **Exact next-owner clipped carrier.**  Start from an admitted p-parent `a`.
If a larger fresh prime `r` keeps `r*a` physical but makes the p-child of that
new site leave the physical clock, then `r*a` is literally in the named clipped
p-base fibre of the same lower-signature cell. -/
theorem lowOwnerFirstOwner_mul_larger_prime_mem_clippedBase
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hraX : r * a ≤ squareRootEndpoint R)
    (hclip : squareRootEndpoint R < p * (r * a)) :
    r * a ∈ lowOwnerFirstOwnerClippedBaseFiber R p sig := by
  rcases Finset.mem_filter.mp ha with ⟨haBase, _hpaX⟩
  rcases Finset.mem_filter.mp haBase with ⟨haCar, hbase⟩
  rcases Finset.mem_filter.mp haCar with ⟨haIcc, hmu⟩
  have haOne : 1 ≤ a := (Finset.mem_Icc.mp haIcc).1
  have haPos : 0 < a := by omega
  have hraPos : 0 < r * a := Nat.mul_pos hr.pos haPos
  have hraOne : 1 ≤ r * a := by omega
  have hmuRA : realMoebiusStep (r * a) ≠ 0 := by
    rw [realMoebiusStep_mul_prime_eq_neg hr hra]
    exact neg_ne_zero.mpr hmu
  have hcarRA : r * a ∈ lowOwnerNonzeroMobiusCarrier R := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hraOne, hraX⟩, hmuRA⟩
  have hsigRA : squarefreeLowerPrimeSignature p (r * a) = sig := by
    rw [squarefreeLowerPrimeSignature_mul_larger_prime hr hpr haPos, hbase.1]
  have hpnr : ¬ p ∣ r := by
    intro hdiv
    have heq : p = r :=
      (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv
    omega
  have hpra : ¬ p ∣ r * a := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h | h
    · exact hpnr h
    · exact hbase.2 h
  have hbaseRA : r * a ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
    exact Finset.mem_filter.mpr ⟨hcarRA, ⟨hsigRA, hpra⟩⟩
  exact Finset.mem_filter.mpr ⟨hbaseRA, hclip⟩

/-- The incomplete next-owner corner therefore carries exactly the already-named
clipped AMP site coefficient, with no new residual coordinate. -/
theorem lowOwnerFirstOwner_largerPrimeBoundary_incidence_eq_clippedSite
    {R p r a : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a)
    (ha : a ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig)
    (hraX : r * a ≤ squareRootEndpoint R)
    (hclip : squareRootEndpoint R < p * (r * a)) :
    lowOwnerPhysicalDirichletIncidenceWeight R p (r * a) *
        realMoebiusStep (r * a) =
      lowOwnerZeroFrequencyMobiusSite R (r * a) := by
  exact lowOwnerPhysicalDirichletIncidence_mul_moebius_eq_clippedSite
    (lowOwnerFirstOwner_mul_larger_prime_mem_clippedBase
      hp hr hpr hra ha hraX hclip)

end RHLean.Proof
