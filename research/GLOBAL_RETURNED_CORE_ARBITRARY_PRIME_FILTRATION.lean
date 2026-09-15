import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_PAIR_ENERGY»

/-!
# Order-independent prime-coordinate Gram filtration

The lower-signature filtration is one ordering of a more elementary finite
Boolean-cube construction.  For any finite revealed prime set `S`, record only
which primes in `S` divide a nonzero AMP site:

  Sigma_S(n) = squarefreePrimeFace(n) ∩ S.

The associated pair carrier consists of ordered physical sites having the same
revealed signature.  If a fresh prime `p ∉ S` is revealed, that pair carrier
splits *exactly* into

* pairs agreeing on p-divisibility, which are the carrier for `insert p S`;
* pairs disagreeing on p-divisibility, the p-crossing packet at revealed state S.

Therefore the Gram energy satisfies the exact one-step identity

  E(S) = E(insert p S) + Cross(S,p).

This is independent of the order in which prime coordinates are revealed.  It
is the finite kernel/order-swap theorem needed to compare the least-owner
filtration with a descending physical chronology.

No norm or estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime-face information retained on an arbitrary revealed coordinate set. -/
def lowOwnerRevealedPrimeSignature (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  squarefreePrimeFace n ∩ S

/-- Ordered nonzero AMP pairs indistinguishable on the revealed prime set. -/
def lowOwnerRevealedPairCarrier
    (R : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
      lowOwnerRevealedPrimeSignature S mn.2

/-- Pairs still indistinguishable on S and agreeing on the new p-coordinate. -/
def lowOwnerRevealedSameBranchPairCarrier
    (R : ℕ) (S : Finset ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
        lowOwnerRevealedPrimeSignature S mn.2 ∧
      (p ∣ mn.1 ↔ p ∣ mn.2)

/-- Pairs still indistinguishable on S but separated by the new p-coordinate. -/
def lowOwnerRevealedCrossPairCarrier
    (R : ℕ) (S : Finset ℕ) (p : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerNonzeroMobiusCarrier R).product
      (lowOwnerNonzeroMobiusCarrier R)).filter fun mn =>
    lowOwnerRevealedPrimeSignature S mn.1 =
        lowOwnerRevealedPrimeSignature S mn.2 ∧
      ((p ∣ mn.1 ∧ ¬ p ∣ mn.2) ∨ (p ∣ mn.2 ∧ ¬ p ∣ mn.1))

/-- Ordered Gram energy at revealed coordinate set S. -/
def lowOwnerRevealedPairEnergy (R : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerRevealedPairCarrier R S,
    lowOwnerZeroFrequencyMobiusSite R mn.1 *
      lowOwnerZeroFrequencyMobiusSite R mn.2

/-- Ordered p-crossing mass at revealed state S. -/
def lowOwnerRevealedCrossPairMass
    (R : ℕ) (S : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ mn ∈ lowOwnerRevealedCrossPairCarrier R S p,
    lowOwnerZeroFrequencyMobiusSite R mn.1 *
      lowOwnerZeroFrequencyMobiusSite R mn.2

/-- On positive support, membership of a prime in the canonical face is exactly
divisibility. -/
theorem prime_mem_squarefreePrimeFace_iff_dvd_public
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    p ∈ squarefreePrimeFace n ↔ p ∣ n := by
  constructor
  · intro hmem
    have hpf : p ∈ n.primeFactors := by
      simpa [squarefreePrimeFace] using hmem
    exact Nat.dvd_of_mem_primeFactors hpf
  · intro hdiv
    have hpf : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn.ne'⟩
    simpa [squarefreePrimeFace] using hpf

/-- Revealing a fresh coordinate either inserts p into the old signature or
leaves the old signature unchanged. -/
theorem lowOwnerRevealedPrimeSignature_insert
    {S : Finset ℕ} {p n : ℕ} (hpS : p ∉ S) :
    lowOwnerRevealedPrimeSignature (insert p S) n =
      if p ∈ squarefreePrimeFace n then
        insert p (lowOwnerRevealedPrimeSignature S n)
      else lowOwnerRevealedPrimeSignature S n := by
  ext q
  by_cases hqp : q = p
  · subst q
    by_cases hpFace : p ∈ squarefreePrimeFace n
    · simp [lowOwnerRevealedPrimeSignature, hpFace]
    · simp [lowOwnerRevealedPrimeSignature, hpFace]
  · by_cases hpFace : p ∈ squarefreePrimeFace n
    · simp [lowOwnerRevealedPrimeSignature, hpFace, hqp]
    · simp [lowOwnerRevealedPrimeSignature, hpFace, hqp]

/-- Since p is fresh for S, it cannot already lie in the old revealed
signature. -/
theorem owner_not_mem_revealedSignature_of_not_mem
    {S : Finset ℕ} {p n : ℕ} (hpS : p ∉ S) :
    p ∉ lowOwnerRevealedPrimeSignature S n := by
  simp [lowOwnerRevealedPrimeSignature, hpS]

/-- Insertion of a fresh coordinate is cancellable on old revealed signatures. -/
theorem insert_owner_revealedSignature_inj
    {S : Finset ℕ} {p m n : ℕ} (hpS : p ∉ S)
    (h : insert p (lowOwnerRevealedPrimeSignature S m) =
      insert p (lowOwnerRevealedPrimeSignature S n)) :
    lowOwnerRevealedPrimeSignature S m =
      lowOwnerRevealedPrimeSignature S n := by
  ext q
  by_cases hqp : q = p
  · subst q
    simp [owner_not_mem_revealedSignature_of_not_mem hpS]
  · have hmem := congrArg (fun T : Finset ℕ => q ∈ T) h
    simpa [hqp] using hmem

/-- **Fresh-coordinate equality criterion.**  Equality after revealing p is
exactly old-signature equality plus agreement on p-divisibility. -/
theorem lowOwnerRevealedPrimeSignature_insert_eq_iff
    {S : Finset ℕ} {p m n : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) (hm : 0 < m) (hn : 0 < n) :
    lowOwnerRevealedPrimeSignature (insert p S) m =
        lowOwnerRevealedPrimeSignature (insert p S) n ↔
      lowOwnerRevealedPrimeSignature S m =
          lowOwnerRevealedPrimeSignature S n ∧
        (p ∣ m ↔ p ∣ n) := by
  rw [lowOwnerRevealedPrimeSignature_insert hpS,
    lowOwnerRevealedPrimeSignature_insert hpS]
  have hpmem : p ∈ squarefreePrimeFace m ↔ p ∣ m :=
    prime_mem_squarefreePrimeFace_iff_dvd_public hp hm
  have hpnmem : p ∈ squarefreePrimeFace n ↔ p ∣ n :=
    prime_mem_squarefreePrimeFace_iff_dvd_public hp hn
  by_cases hpm : p ∣ m
  · have hpFaceM := hpmem.mpr hpm
    by_cases hpn : p ∣ n
    · have hpFaceN := hpnmem.mpr hpn
      simp only [hpFaceM, hpFaceN, if_true]
      constructor
      · intro h
        exact ⟨insert_owner_revealedSignature_inj hpS h, by simp [hpm, hpn]⟩
      · rintro ⟨hsig, _⟩
        rw [hsig]
    · have hpFaceN : p ∉ squarefreePrimeFace n := by
        intro h
        exact hpn (hpnmem.mp h)
      simp only [hpFaceM, hpFaceN, if_true, if_false]
      constructor
      · intro h
        have hpMem : p ∈ lowOwnerRevealedPrimeSignature S n := by
          have : p ∈ insert p (lowOwnerRevealedPrimeSignature S m) := by simp
          rw [h] at this
          exact this
        exact False.elim ((owner_not_mem_revealedSignature_of_not_mem hpS) hpMem)
      · rintro ⟨_hsig, hiff⟩
        exact False.elim (hpn (hiff.mp hpm))
  · have hpFaceM : p ∉ squarefreePrimeFace m := by
      intro h
      exact hpm (hpmem.mp h)
    by_cases hpn : p ∣ n
    · have hpFaceN := hpnmem.mpr hpn
      simp only [hpFaceM, hpFaceN, if_false, if_true]
      constructor
      · intro h
        have hpMem : p ∈ lowOwnerRevealedPrimeSignature S m := by
          have : p ∈ insert p (lowOwnerRevealedPrimeSignature S n) := by simp
          rw [← h] at this
          exact this
        exact False.elim ((owner_not_mem_revealedSignature_of_not_mem hpS) hpMem)
      · rintro ⟨_hsig, hiff⟩
        exact False.elim (hpm (hiff.mpr hpn))
    · have hpFaceN : p ∉ squarefreePrimeFace n := by
        intro h
        exact hpn (hpnmem.mp h)
      simp only [hpFaceM, hpFaceN, if_false]
      constructor
      · intro h
        exact ⟨h, by simp [hpm, hpn]⟩
      · rintro ⟨h, _⟩
        exact h

/-- **Pair carrier after revealing p.** -/
theorem lowOwnerRevealedPairCarrier_insert_eq_sameBranch
    {R : ℕ} {S : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) :
    lowOwnerRevealedPairCarrier R (insert p S) =
      lowOwnerRevealedSameBranchPairCarrier R S p := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
    have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
        (lowOwnerRevealedPrimeSignature_insert_eq_iff
          hp hpS hmPos hnPos).1 hsig⟩
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
    have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
    have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩,
        (lowOwnerRevealedPrimeSignature_insert_eq_iff
          hp hpS hmPos hnPos).2 hdata⟩

/-- Same-branch and crossing packets are disjoint. -/
theorem lowOwnerRevealedSameBranch_disjoint_cross
    (R : ℕ) (S : Finset ℕ) (p : ℕ) :
    Disjoint
      (lowOwnerRevealedSameBranchPairCarrier R S p)
      (lowOwnerRevealedCrossPairCarrier R S p) := by
  rw [Finset.disjoint_left]
  intro mn hsame hcross
  have hs := (Finset.mem_filter.mp hsame).2.2
  have hc := (Finset.mem_filter.mp hcross).2.2
  rcases hc with hc | hc
  · exact hc.2 (hs.mp hc.1)
  · exact hc.2 (hs.mpr hc.1)

/-- **Carrier partition before revealing p.**  Every pair agreeing on S either
agrees or disagrees on p-divisibility. -/
theorem lowOwnerRevealedPairCarrier_eq_sameBranch_union_cross
    (R : ℕ) (S : Finset ℕ) (p : ℕ) :
    lowOwnerRevealedPairCarrier R S =
      lowOwnerRevealedSameBranchPairCarrier R S p ∪
        lowOwnerRevealedCrossPairCarrier R S p := by
  ext mn
  rcases mn with ⟨m, n⟩
  constructor
  · intro hmn
    rcases Finset.mem_filter.mp hmn with ⟨hprod, hsig⟩
    by_cases hpm : p ∣ m
    · by_cases hpn : p ∣ n
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, by simp [hpm, hpn]⟩⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, Or.inl ⟨hpm, hpn⟩⟩⟩)
    · by_cases hpn : p ∣ n
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, Or.inr ⟨hpn, hpm⟩⟩⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr
            ⟨hprod, ⟨hsig, by simp [hpm, hpn]⟩⟩)
  · intro hmn
    rcases Finset.mem_union.mp hmn with hsame | hcross
    · rcases Finset.mem_filter.mp hsame with ⟨hprod, hdata⟩
      exact Finset.mem_filter.mpr ⟨hprod, hdata.1⟩
    · rcases Finset.mem_filter.mp hcross with ⟨hprod, hdata⟩
      exact Finset.mem_filter.mpr ⟨hprod, hdata.1⟩

/-- **Order-independent one-coordinate energy telescope.** -/
theorem lowOwnerRevealedPairEnergy_eq_insert_add_cross
    {R : ℕ} {S : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpS : p ∉ S) :
    lowOwnerRevealedPairEnergy R S =
      lowOwnerRevealedPairEnergy R (insert p S) +
        lowOwnerRevealedCrossPairMass R S p := by
  unfold lowOwnerRevealedPairEnergy lowOwnerRevealedCrossPairMass
  rw [lowOwnerRevealedPairCarrier_eq_sameBranch_union_cross,
    Finset.sum_union (lowOwnerRevealedSameBranch_disjoint_cross R S p),
    lowOwnerRevealedPairCarrier_insert_eq_sameBranch hp hpS]

end RHLean.Proof
