import RHLean.Proof.LowWheelFrozenSecondContactRoughPrefix

/-!
# Exact q^2 reindex of the frozen square residual

The source/transport cancellation in `LowWheelFrozenSecondContactRoughPrefix`
leaves, at each fixed source scale `A`, a signed square residual

`sum_{c squarefree, rough above p, P+(c)*c <= B} mu(c)`.

This file performs only the next exact arithmetic reindex.  Every residual
cofactor has the unique owner `q = P+(c)`.  Writing `d = c/q` gives

`p < q`, `q*d = c`, `q^2*d <= B`, `P+(d) < q`,

with `d` still squarefree and rough above `p`; moreover the Möbius sign flips.
No norm, estimate, selected-prime tensor, or identification with an ordinary
Mertens prefix is made here.  In particular the fixed-`A` daughter remains an
interval-prime object; completion to ordinary Mertens can only occur after the
outer signed source-scale sum is reassembled.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic
open CanonicalGapAncestryBridge

attribute [local instance] Classical.propDecidable

/-- Owners actually represented in one frozen square-residual fibre. -/
def lowWheelFrozenSourceSquareResidualOwners (p B : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceSquareResidual p B).image canonicalLargestPrimeFactor

/-- The square-residual fibre having canonical largest-prime owner `q`. -/
def lowWheelFrozenSourceSquareResidualOwnerFiber
    (p B q : ℕ) : Finset ℕ :=
  (lowWheelFrozenSourceSquareResidual p B).filter fun c =>
    canonicalLargestPrimeFactor c = q

@[simp] theorem mem_lowWheelFrozenSourceSquareResidualOwnerFiber
    {p B q c : ℕ} :
    c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q ↔
      c ∈ lowWheelFrozenSourceSquareResidual p B ∧
        canonicalLargestPrimeFactor c = q := by
  simp [lowWheelFrozenSourceSquareResidualOwnerFiber]

/-- The residual is a disjoint fibrewise sum over its canonical largest-prime
owners.  The observable is arbitrary: this is pure reindexing. -/
theorem lowWheelFrozenSourceSquareResidual_sum_eq_sum_ownerFibers
    {M : Type*} [AddCommMonoid M]
    (p B : ℕ) (f : ℕ → M) :
    (∑ c ∈ lowWheelFrozenSourceSquareResidual p B, f c) =
      ∑ q ∈ lowWheelFrozenSourceSquareResidualOwners p B,
        ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q, f c := by
  let S : Finset ℕ := lowWheelFrozenSourceSquareResidual p B
  let O : Finset ℕ := lowWheelFrozenSourceSquareResidualOwners p B
  let owner : ℕ → ℕ := canonicalLargestPrimeFactor
  have hmaps : ∀ c ∈ S, owner c ∈ O := by
    intro c hc
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps f
  have hraw :
      (∑ c ∈ S, f c) =
        ∑ q ∈ O, ∑ c ∈ S with owner c = q, f c := hfiber.symm
  change (∑ c ∈ S, f c) =
    ∑ q ∈ O,
      ∑ c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q, f c
  rw [hraw]
  apply Finset.sum_congr rfl
  intro q hq
  rfl

/-- **Local SR-q^2 kernel.**  A square-residual cofactor with owner `q` strips
canonically as `c=q*d`.  The daughter `d` is still squarefree and rough above
the old source pivot, has all prime factors below `q`, and lies at the genuine
square-dilated cutoff `q^2*d <= B`.  The Möbius sign flips exactly. -/
theorem lowWheelFrozenSourceSquareResidualOwnerFiber_data
    {p B q c : ℕ}
    (hc : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q) :
    q.Prime ∧ p < q ∧
      Squarefree (canonicalCofactor c) ∧
      RoughAbove p (canonicalCofactor c) ∧
      canonicalLargestPrimeFactor (canonicalCofactor c) < q ∧
      q * canonicalCofactor c = c ∧
      q * q * canonicalCofactor c ≤ B ∧
      canonicalMoebiusWeight c =
        -canonicalMoebiusWeight (canonicalCofactor c) := by
  rcases mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hc with
    ⟨hcResidual, howner⟩
  rcases Finset.mem_filter.mp hcResidual with ⟨hcRoughPrefix, hcontact⟩
  rcases Finset.mem_filter.mp hcRoughPrefix with
    ⟨hcIcc, hsq, hrough⟩
  have hcBounds := Finset.mem_Icc.mp hcIcc
  have hcgt : 1 < c := by omega
  have hc0 : c ≠ 0 := by omega
  have hqPrime : q.Prime := by
    simpa [howner] using canonicalLargestPrimeFactor_prime hcgt
  have hqDvd : q ∣ c := by
    simpa [howner] using canonicalLargestPrimeFactor_dvd hcgt
  have hqPF : q ∈ c.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hc0⟩
  have hpq : p < q := hrough q hqPF
  have hfactor0 :
      canonicalCofactor c * canonicalLargestPrimeFactor c = c :=
    canonicalCofactor_mul_largestPrimeFactor hcgt
  have hfactor : q * canonicalCofactor c = c := by
    simpa [howner, Nat.mul_comm] using hfactor0
  have hdDvd : canonicalCofactor c ∣ c := canonicalCofactor_dvd hcgt
  have hdSq : Squarefree (canonicalCofactor c) :=
    hsq.squarefree_of_dvd hdDvd
  have hdRough : RoughAbove p (canonicalCofactor c) := by
    intro r hr
    have hrPrime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrDvdD : r ∣ canonicalCofactor c := Nat.dvd_of_mem_primeFactors hr
    have hrDvdC : r ∣ c := dvd_trans hrDvdD hdDvd
    have hrC : r ∈ c.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrPrime, hrDvdC, hc0⟩
    exact hrough r hrC
  have hdLt : canonicalLargestPrimeFactor (canonicalCofactor c) < q := by
    have hlt :=
      canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree hcgt hsq
    simpa [howner] using hlt
  have hq2 : q * q * canonicalCofactor c ≤ B := by
    have hqmul : q * (q * canonicalCofactor c) = q * c :=
      congrArg (fun n : ℕ => q * n) hfactor
    calc
      q * q * canonicalCofactor c = q * (q * canonicalCofactor c) := by ring
      _ = q * c := hqmul
      _ = canonicalLargestPrimeFactor c * c := by rw [howner]
      _ ≤ B := hcontact
  have hweightD :
      canonicalMoebiusWeight (canonicalCofactor c) =
        -canonicalMoebiusWeight c := by
    simpa [canonicalCofactor, howner] using
      (canonicalMoebiusWeight_div_prime hqPrime hsq hqDvd)
  have hweight :
      canonicalMoebiusWeight c =
        -canonicalMoebiusWeight (canonicalCofactor c) := by
    rw [hweightD]
    ring
  exact ⟨hqPrime, hpq, hdSq, hdRough, hdLt, hfactor, hq2, hweight⟩

/-- Canonical stripped daughters live in the expected interval-prime q^2
window.  Surjectivity onto this window is intentionally deferred to the next
carrier theorem. -/
def lowWheelFrozenSourceSquareResidualDaughterWindow
    (p B q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (B / (q * q))).filter fun d =>
    Squarefree d ∧ RoughAbove p d ∧ canonicalLargestPrimeFactor d < q

/-- Every owner-`q` residual maps into the literal q^2 daughter window. -/
theorem canonicalCofactor_mem_lowWheelFrozenSourceSquareResidualDaughterWindow
    {p B q c : ℕ}
    (hc : c ∈ lowWheelFrozenSourceSquareResidualOwnerFiber p B q) :
    canonicalCofactor c ∈
      lowWheelFrozenSourceSquareResidualDaughterWindow p B q := by
  rcases lowWheelFrozenSourceSquareResidualOwnerFiber_data hc with
    ⟨hqPrime, _hpq, hdSq, hdRough, hdLt, _hfactor, hq2, _hweight⟩
  have hcgt : 1 < c := by
    have hres := (mem_lowWheelFrozenSourceSquareResidualOwnerFiber.mp hc).1
    have hrough := (Finset.mem_filter.mp hres).1
    have hIcc := (Finset.mem_filter.mp hrough).1
    have hbounds := Finset.mem_Icc.mp hIcc
    omega
  have hdPos : 1 ≤ canonicalCofactor c := canonicalCofactor_pos hcgt
  have hqqPos : 0 < q * q := Nat.mul_pos hqPrime.pos hqPrime.pos
  have hdUpper : canonicalCofactor c ≤ B / (q * q) := by
    apply (Nat.le_div_iff_mul_le hqqPos).2
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hdPos, hdUpper⟩, hdSq, hdRough, hdLt⟩

end RHLean.Proof
