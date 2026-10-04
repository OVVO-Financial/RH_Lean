import Mathlib
import «research.VF_MID_SUBDOUBLING_SURVIVOR_TO_OWNER_GATE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»

/-!
# VF final raw clipped telescope entry

This file pushes the merged #886 restricted survivor packet one exact step
farther into the returned-core first-owner geometry.

For a genuine subdoubling frozen run `A <= R < B <= 2A`, every nonzero
restricted survivor site is already known to be clipped at every live first
owner `p > A`.  Therefore the admitted base part of every arbitrary-site
first-owner cell vanishes identically.

The result below is an exact signed identity: each live first-owner cell of the
#885/#886 restricted site is pure

  clipped-base amplitude * restricted-child amplitude.

No norm, reciprocal reweighting, or cancellation estimate is used.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Subdoubling rank-two normal form: the 317 pattern at every scale -/

/-- **Global rank-two survivor classification.**

On an entire frozen subdoubling run, every surviving site is exactly one of the
two types seen in the hand computations:

* an actual prime, carrying Mobius sign `-1`;
* a product `q*r` of two primes strictly above the frozen cutoff `A`,
  carrying Mobius sign `+1`.

There are no degree-three-or-higher survivor faces. -/
theorem vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
    {A B n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    n.Prime ∨
      ∃ q r : ℕ,
        q.Prime ∧ r.Prime ∧ A < q ∧ q ≤ r ∧ n = q * r := by
  rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
  rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
  have hR2 : 2 ≤ R := by omega
  have hRlt : R < 2 * A := hRB.trans_le hBA
  have hsplit :=
    vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
      (A := A) (R := R) hR2 hAR
  have hmem :
      n ∈ vfMidSquareWheelPrimes R ∪
        vfMidSquareBandPrefixCompositeSurvivors A R := by
    rw [← hsplit]
    exact hnSurv
  rcases Finset.mem_union.mp hmem with hnPrime | hnComp
  · exact Or.inl (Finset.mem_filter.mp hnPrime).2
  · exact Or.inr
      (vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_subdoubling
        hA hAR hRlt hnComp)

/-- The rank-two classification carries the exact signs used in the 210/317
hand ledgers: prime survivors are `-1`, nonprime survivors are `+1`. -/
theorem vfMidDyadicPrefixSurvivor_realMoebiusStep_eq
    {A B n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    realMoebiusStep n = if n.Prime then -1 else 1 := by
  by_cases hnPrime : n.Prime
  · rw [if_pos hnPrime, realMoebiusStep,
      ArithmeticFunction.moebius_apply_prime hnPrime]
    norm_num
  · rw [if_neg hnPrime]
    rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
    rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
    have hR2 : 2 ≤ R := by omega
    have hRlt : R < 2 * A := hRB.trans_le hBA
    have hsplit :=
      vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
        (A := A) (R := R) hR2 hAR
    have hmem :
        n ∈ vfMidSquareWheelPrimes R ∪
          vfMidSquareBandPrefixCompositeSurvivors A R := by
      rw [← hsplit]
      exact hnSurv
    have hnComp :
        n ∈ vfMidSquareBandPrefixCompositeSurvivors A R := by
      rcases Finset.mem_union.mp hmem with hp | hc
      · exact False.elim (hnPrime (Finset.mem_filter.mp hp).2)
      · exact hc
    have hmu :=
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling
        hA hAR hRlt hnComp
    rw [realMoebiusStep, hmu]
    norm_num

/-- **A live owner strips every survivor to degree at most one.**

If a prime owner `p` divides a frozen-run survivor `n`, the returned parent
`n/p` is either `1` (when `n` itself is prime) or another prime.  This is
the exact general form of the 317 computation `323 = 17*19 -> 19`; after the
first live owner there is no hidden composite returned parent. -/
theorem vfMidDyadicPrefixSurvivor_div_prime_eq_one_or_prime
    {A B p n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hpn : p ∣ n) :
    n / p = 1 ∨ (n / p).Prime := by
  rcases
      vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
        hA hAB hBA hn with hnPrime | ⟨q, r, hq, hr, _hAq, _hqr, rfl⟩
  · have hpeq : p = n := by
      rcases (Nat.dvd_prime hnPrime).mp hpn with hp1 | hpnEq
      · exact False.elim (hp.ne_one hp1)
      · exact hpnEq
    left
    subst p
    exact Nat.div_self hnPrime.ne_zero
  · have hpqr : p ∣ q ∨ p ∣ r := hp.dvd_mul.mp hpn
    rcases hpqr with hpq | hpr
    · have hpEqQ : p = q := by
        rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqEq
        · exact False.elim (hp.ne_one hp1)
        · exact hpqEq
      right
      subst p
      simpa [hq.ne_zero] using hr
    · have hpEqR : p = r := by
        rcases (Nat.dvd_prime hr).mp hpr with hp1 | hprEq
        · exact False.elim (hp.ne_one hp1)
        · exact hprEq
      right
      subst p
      simpa [hr.ne_zero] using hq

/-- Restricted #886 signed mass on the clipped p-free base side of one
first-owner/signature cell. -/
def vfMidSurvivorClippedBaseAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B a

/-- Restricted #886 signed mass on the p-divisible child side of one
first-owner/signature cell. -/
def vfMidSurvivorChildAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B b

/-- Returned admitted parents whose p-child is still on the frozen #886
survivor carrier.  This is the exact lower-coordinate image of the restricted
child fibre under b |-> b / p. -/
def vfMidSurvivorReturnedParentFiber
    (A B p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerAdmittedBaseFiber B p sig).filter fun c =>
    p * c ∈ vfMidDyadicPrefixSurvivorCarrier A B

/-- **Exact child-to-returned-parent reindexing on the frozen carrier.**

A restricted p-child returns uniquely to an admitted p-free parent.  Fresh
prime multiplication reverses the Mobius sign, so the whole restricted child
amplitude is the negative signed mass of this literal returned-parent fibre. -/
theorem vfMidSurvivorChildAmplitude_eq_neg_returnedParents
    {A B p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidSurvivorChildAmplitude A B p sig =
      ∑ c ∈ vfMidSurvivorReturnedParentFiber A B p sig,
        -realMoebiusStep c := by
  unfold vfMidSurvivorChildAmplitude
    vfMidDyadicPrefixSurvivorSignedSite
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun b _hb => b / p)
    ?_ ?_ ?_ ?_
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbChild, hbCar⟩
    have hcAdm :=
      lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hcancel : p * (b / p) = b :=
      Nat.mul_div_cancel' hbDvd
    unfold vfMidSurvivorReturnedParentFiber
    exact Finset.mem_filter.mpr
      ⟨hcAdm, by simpa [hcancel] using hbCar⟩
  · intro b hb d hd heq
    have hbChild := (Finset.mem_filter.mp hb).1
    have hdChild := (Finset.mem_filter.mp hd).1
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hdDvd : p ∣ d :=
      (Finset.mem_filter.mp hdChild).2.2
    calc
      b = p * (b / p) := (Nat.mul_div_cancel' hbDvd).symm
      _ = p * (d / p) := by rw [heq]
      _ = d := Nat.mul_div_cancel' hdDvd
  · intro c hc
    have hcData := Finset.mem_filter.mp hc
    have hcAdm := hcData.1
    have hpcCar := hcData.2
    have hpcChild :=
      lowOwnerFirstOwner_mul_mem_child_of_admitted hp hcAdm
    refine ⟨p * c, Finset.mem_filter.mpr ⟨hpcChild, hpcCar⟩, ?_⟩
    simpa [Nat.mul_comm] using Nat.mul_div_left c hp.pos
  · intro b hb
    have hbChild := (Finset.mem_filter.mp hb).1
    have hcBase :=
      lowOwnerFirstOwner_div_mem_base_of_child hp hbChild
    have hnot : ¬ p ∣ b / p :=
      (Finset.mem_filter.mp hcBase).2.2
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hcancel : p * (b / p) = b :=
      Nat.mul_div_cancel' hbDvd
    calc
      realMoebiusStep b =
          realMoebiusStep (p * (b / p)) := by rw [hcancel]
      _ = -realMoebiusStep (b / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hnot

/-- Every live post-frozen owner has zero restricted survivor mass on the
admitted p-free base fibre. -/
theorem sum_admitted_vfMidSurvivorSignedSite_eq_zero
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  exact
    vfMidDyadicPrefixSurvivorSignedSite_eq_zero_on_admitted_liveOwner
      hA hAB hBA hpA ha

/-- Hence the complete restricted p-free base sum is literally its clipped
part.  This is the raw signed carrier statement needed before any energy
conversion. -/
theorem sum_base_vfMidSurvivorSignedSite_eq_clipped
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) =
      vfMidSurvivorClippedBaseAmplitude A B p sig := by
  have hsplit :
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) =
        (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a) +
        ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a := by
    unfold lowOwnerFirstOwnerAdmittedBaseFiber
      lowOwnerFirstOwnerClippedBaseFiber
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := lowOwnerFirstOwnerBaseFiber B p sig)
        (p := fun a => p * a ≤ squareRootEndpoint B)
        (f := vfMidDyadicPrefixSurvivorSignedSite A B)).symm
  rw [hsplit, sum_admitted_vfMidSurvivorSignedSite_eq_zero
    hA hAB hBA hpA]
  simp [vfMidSurvivorClippedBaseAmplitude]

/-- **Pure clipped-cell form of every live #886 first-owner cell.**

Because the restricted site vanishes on admitted parents, its arbitrary-site
base x child Gram has no admitted-base contribution left. -/
theorem lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    lowOwnerFirstOwnerCellGramWith B p sig
        (vfMidDyadicPrefixSurvivorSignedSite A B) =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
  unfold lowOwnerFirstOwnerCellGramWith
  calc
    (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber B p sig).product
        (lowOwnerFirstOwnerChildFiber B p sig),
      vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
        vfMidDyadicPrefixSurvivorSignedSite A B ab.2) =
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a *
            vfMidDyadicPrefixSurvivorSignedSite A B b := by
          simpa only using
            (Finset.sum_product
              (s := lowOwnerFirstOwnerBaseFiber B p sig)
              (t := lowOwnerFirstOwnerChildFiber B p sig)
              (f := fun ab : ℕ × ℕ =>
                vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
                  vfMidDyadicPrefixSurvivorSignedSite A B ab.2))
    _ =
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) *
      (∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
          rw [sum_base_vfMidSurvivorSignedSite_eq_clipped
            hA hAB hBA hpA]
          rfl

/-- **Pointwise raw-survivor to Dirichlet-polarization weld.**

Let `a` be a clipped p-free survivor and `b` a p-divisible survivor in the
same first-owner/signature cell.  Returning `b` to the admitted parent
`b / p`, the raw #886 pair product is exactly the repository's signed
Dirichlet mixed-polarization atom.

This is the weight-preserving bridge into the existing signed owner telescope:
no norm, reciprocal factor, or ownerwise estimate is introduced. -/
theorem vfMidSurvivorPair_eq_dirichletPolarizationAtom
    {A B p a b : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (haCar : a ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hbCar : b ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (haClip : a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig)
    (hbChild : b ∈ lowOwnerFirstOwnerChildFiber B p sig) :
    vfMidDyadicPrefixSurvivorSignedSite A B a *
        vfMidDyadicPrefixSurvivorSignedSite A B b =
      lowOwnerFirstOwnerDirichletPolarizationAtom B p (a, b / p) := by
  have hcAdm :
      b / p ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig :=
    lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
  have haBase := (Finset.mem_filter.mp haClip).1
  have haClock := (Finset.mem_filter.mp haBase).1
  have haIcc := (Finset.mem_filter.mp haClock).1
  have haX : a ≤ squareRootEndpoint B :=
    (Finset.mem_Icc.mp haIcc).2
  have hbaseSite :
      lowOwnerFirstOwnerDirichletBaseSite B a =
        realMoebiusStep a := by
    unfold lowOwnerFirstOwnerDirichletBaseSite
    rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX]
    rw [lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
      hA hAB hBA haCar]
    ring
  have hbDvd : p ∣ b :=
    (Finset.mem_filter.mp hbChild).2.2
  have hcancel : p * (b / p) = b :=
    Nat.mul_div_cancel' hbDvd
  have hretSite :
      lowOwnerFirstOwnerDirichletReturnedChildSite B p (b / p) =
        realMoebiusStep (b / p) := by
    rw [lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted
      hcAdm]
    rw [hcancel]
    rw [lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
      hA hAB hBA hbCar]
    ring
  have hcBase := (Finset.mem_filter.mp hcAdm).1
  have hpc : ¬ p ∣ b / p :=
    (Finset.mem_filter.mp hcBase).2.2
  have hmu :
      realMoebiusStep b = -realMoebiusStep (b / p) := by
    calc
      realMoebiusStep b =
          realMoebiusStep (p * (b / p)) := by rw [hcancel]
      _ = -realMoebiusStep (b / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hpc
  have hatom :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_left
      haClip hcAdm
  calc
    vfMidDyadicPrefixSurvivorSignedSite A B a *
        vfMidDyadicPrefixSurvivorSignedSite A B b =
      realMoebiusStep a * realMoebiusStep b := by
        simp [vfMidDyadicPrefixSurvivorSignedSite, haCar, hbCar]
    _ = -(realMoebiusStep a * realMoebiusStep (b / p)) := by
        rw [hmu]
        ring
    _ = lowOwnerFirstOwnerDirichletPolarizationAtom B p (a, b / p) := by
        rw [hatom, hbaseSite, hretSite]
        ring


/-- **Global raw clipped entrance.**

After removing the diagonal, the complete #885/#886 survivor square is a sum
only of clipped-base x restricted-child first-owner cells with live owners
strictly above the frozen cutoff. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveClippedCells
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            (vfMidSurvivorClippedBaseAmplitude A B p sig *
              vfMidSurvivorChildAmplitude A B p sig) := by
  rw [vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveFirstOwners
    hA hAB hBA]
  apply congrArg
    (fun x : ℝ =>
      lowOwnerGlobalDiagonalPairMassWith B
        (vfMidDyadicPrefixSurvivorSignedSite A B) + x)
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : A < p :=
    (Finset.mem_filter.mp hp).2
  have hpPrime : p.Prime :=
    (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
      hpPrime (vfMidDyadicPrefixSurvivorSignedSite A B)]
  congr 1
  apply Finset.sum_congr rfl
  intro sig _hsig
  rw [lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    hA hAB hBA hpA]

end RHLean.Analysis
