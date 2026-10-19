import «research.VF_919_EULER_RANK_ONE_GPF_FIBERS_20261019»

/-!
# Exact 3-dipole finite density defect and the physical cofactor hyperbola split

These are UNCONDITIONAL FINITE IDENTITIES, not an analytic 7/8 theorem.
The 3-adic weight is defined on a pair-complete finite carrier, not on
an arbitrary "active" shell carrier, which need not be closed under d -> 3*d.

Important: alpha(d)=alpha(3*d)=1/d makes the signed defect zero, but does
NOT make alpha(3*d) a valid 1/(3*d) prime-density approximation. A centered
second-moment estimate remains necessary.

The high half is dualized by the TRUE greatest prime owner P+(n), retaining
P+(cofactor(n)) < P+(n) and all squarefree signs. No unit-width or PNT
assumption is inserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis
attribute [local instance] Classical.propDecidable

/-- Odd, squarefree, 3-free parents. Includes d=1 when M>=1. -/
def vf919ThreeDipoleParents (M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun d => Odd d ∧ Squarefree d ∧ ¬ 3 ∣ d)

def vf919ThreeDipoleChildren (M : ℕ) : Finset ℕ :=
  (vf919ThreeDipoleParents M).image (fun d => 3 * d)

/-- Pair-complete supporting carrier; NOT the possibly clipped active carrier. -/
def vf919ThreeDipoleCarrier (M : ℕ) : Finset ℕ :=
  vf919ThreeDipoleParents M ∪ vf919ThreeDipoleChildren M

theorem vf919ThreeDipole_disjoint (M : ℕ) :
    Disjoint (vf919ThreeDipoleParents M)
      (vf919ThreeDipoleChildren M) := by
  apply Finset.disjoint_left.mpr
  intro n hnParent hnChild
  rcases Finset.mem_image.mp hnChild with ⟨d, _hd, rfl⟩
  have hnnot : ¬ (3 : ℕ) ∣ 3 * d :=
    (Finset.mem_filter.mp hnParent).2.2.2
  exact hnnot ⟨d, rfl⟩

/-- Exact paired 3-adic weight. The child has the SAME 1/d coefficient
as the parent (not the natural 1/(3*d) prime-density coefficient). -/
def vf919ThreeDipoleAlpha (M m : ℕ) : ℝ :=
  if m ∈ vf919ThreeDipoleParents M then (m : ℝ)⁻¹
  else if m ∈ vf919ThreeDipoleChildren M
    then ((m / 3 : ℕ) : ℝ)⁻¹ else 0

theorem vf919ThreeDipoleAlpha_parent {M d : ℕ}
    (hd : d ∈ vf919ThreeDipoleParents M) :
    vf919ThreeDipoleAlpha M d = (d : ℝ)⁻¹ := by
  simp [vf919ThreeDipoleAlpha, hd]

theorem vf919ThreeDipoleAlpha_child {M d : ℕ}
    (hd : d ∈ vf919ThreeDipoleParents M) :
    vf919ThreeDipoleAlpha M (3 * d) = (d : ℝ)⁻¹ := by
  have hnot : 3 * d ∉ vf919ThreeDipoleParents M := by
    intro hbad
    have hno : ¬ (3 : ℕ) ∣ 3 * d :=
      (Finset.mem_filter.mp hbad).2.2.2
    exact hno ⟨d, rfl⟩
  have hyes : 3 * d ∈ vf919ThreeDipoleChildren M :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hdiv : 3 * d / 3 = d := by omega
  simp [vf919ThreeDipoleAlpha, hnot, hyes, hdiv]

/-- The exact rational finite paired cancellation, as the ACTUAL
gpf-defect functional used by the double-difference kernel. -/
theorem three_adic_dipole_defect_eq_zero (M : ℕ) :
    vf919EulerGpfDefect (vf919ThreeDipoleCarrier M)
      (vf919ThreeDipoleAlpha M) = 0 := by
  unfold vf919EulerGpfDefect vf919ThreeDipoleCarrier
  rw [Finset.sum_union (vf919ThreeDipole_disjoint M)]
  have hparent :
      (∑ d ∈ vf919ThreeDipoleParents M,
        realMoebiusStep d * vf919ThreeDipoleAlpha M d) =
      ∑ d ∈ vf919ThreeDipoleParents M,
        realMoebiusStep d * (d : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [vf919ThreeDipoleAlpha_parent hd]
  have hchild :
      (∑ m ∈ vf919ThreeDipoleChildren M,
        realMoebiusStep m * vf919ThreeDipoleAlpha M m) =
      ∑ d ∈ vf919ThreeDipoleParents M,
        realMoebiusStep (3 * d) * (d : ℝ)⁻¹ := by
    unfold vf919ThreeDipoleChildren
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [vf919ThreeDipoleAlpha_child hd]
    · intro a _ha b _hb hab
      omega
  rw [hparent, hchild, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro d hd
  have hfresh : ¬ (3 : ℕ) ∣ d :=
    (Finset.mem_filter.mp hd).2.2.2
  have hsign : realMoebiusStep (3 * d) = -realMoebiusStep d :=
    vf919EulerGpfDipole_moebius (by norm_num : (3 : ℕ).Prime) hfresh
  rw [hsign]
  ring

/-- Substitution in the existing exact compensated kernel: the two drift
error terms vanish, but no second moment of K^Delta is bounded. -/
theorem three_adic_dipole_kernel_exact (H M : ℕ) :
    (∑ m ∈ vf919ThreeDipoleCarrier M,
      ∑ n ∈ vf919ThreeDipoleCarrier M,
        realMoebiusStep m * realMoebiusStep n *
          vf919EulerGpfKernel H m n) =
      ∑ m ∈ vf919ThreeDipoleCarrier M,
        ∑ n ∈ vf919ThreeDipoleCarrier M,
          realMoebiusStep m * realMoebiusStep n *
            vf919EulerGpfDeltaKernel H m n (vf919ThreeDipoleAlpha M) := by
  exact dyadic_kernel_double_difference_of_zero_defect
    H (vf919ThreeDipoleCarrier M) (vf919ThreeDipoleAlpha M)
    (three_adic_dipole_defect_eq_zero M)

/-! ## The real low-cofactor interval has no largest-prime truncation -/

/-- If a positive cofactor fits strictly below H, a prime q whose product
m*q is >=R^2 (R>=H) must be GREATER THAN m, hence also P+(m).
The stronger hypothesis 3*M < H is explicit, avoiding a hidden
sieve or PNT assumption. -/
theorem gpf_lt_prime_of_le_cutoff
    {H R M m q : ℕ}
    (hM : 3 * M < H) (hHR : H ≤ R)
    (hm : 0 < m) (hmM : m ≤ 3 * M)
    (hq : q.Prime) (hprod : R ^ 2 ≤ m * q) :
    RHLean.Proof.canonicalLargestPrimeFactor m < q := by
  have hmH : m < H := lt_of_le_of_lt hmM hM
  have hmq : m < q := by
    by_contra hnot
    have hqm : q ≤ m := Nat.le_of_not_gt hnot
    have hmul : m * q ≤ m * m := Nat.mul_le_mul_left m hqm
    nlinarith
  by_cases hmone : m = 1
  · subst m
    have hgp : RHLean.Proof.canonicalLargestPrimeFactor 1 = 1 := by
      simp [RHLean.Proof.canonicalLargestPrimeFactor]
    rw [hgp]
    exact hq.one_lt
  · have hmgt : 1 < m := by omega
    have hgpfle : RHLean.Proof.canonicalLargestPrimeFactor m ≤ m :=
      Nat.le_of_dvd hm (RHLean.Proof.canonicalLargestPrimeFactor_dvd hmgt)
    exact lt_of_le_of_lt hgpfle hmq

/-- On the low side, any shell prime q above the lower physical endpoint
automatically passes the *true* canonical greatest-prime cutoff. -/
theorem gpf_small_cofactor_unrestricted_prime_window
    {H R M m q : ℕ}
    (hM : 3 * M < H) (hHR : H ≤ R)
    (hm : 0 < m) (hmM : m ≤ 3 * M)
    (hq : q.Prime)
    (hlo : R ^ 2 ≤ m * q)
    (_hhi : m * q < (R + 1) ^ 2) :
    RHLean.Proof.canonicalLargestPrimeFactor (m * q) = q := by
  exact RHLean.Proof.canonicalLargestPrimeFactor_mul_prime_eq
    hm (by
      have hrough := gpf_lt_prime_of_le_cutoff
        hM hHR hm hmM hq hlo
      have hmq : m < q := by
        by_contra hnot
        have hqm : q ≤ m := Nat.le_of_not_gt hnot
        have hmH : m < H := lt_of_le_of_lt hmM hM
        nlinarith [Nat.mul_le_mul_left m hqm]
      exact hmq) hq

/-! ## Exact square-shell hyperbola decomposition (no tail norm assertion) -/

def vf919EulerOddLowSites (R M : ℕ) : Finset ℕ :=
  (vf919EulerOddSquarefreeCarrier R).filter
    (fun n => RHLean.Proof.canonicalCofactor n ≤ 3 * M)

def vf919EulerOddHighSites (R M : ℕ) : Finset ℕ :=
  (vf919EulerOddSquarefreeCarrier R).filter
    (fun n => 3 * M < RHLean.Proof.canonicalCofactor n)

def vf919EulerOddLowMass (R M : ℕ) : ℝ :=
  ∑ n ∈ vf919EulerOddLowSites R M, realMoebiusStep n

def vf919EulerOddHighMass (R M : ℕ) : ℝ :=
  ∑ n ∈ vf919EulerOddHighSites R M, realMoebiusStep n

/-- The physical odd shell decomposes EXACTLY at 3*M.
No squarefree cofactor is lost and no 'large q' claim is needed. -/
theorem odd_shell_hyperbola_split_eq (R M : ℕ) :
    vf919EulerOddBlockS R ((R + 1) ^ 2) =
      vf919EulerOddLowMass R M + vf919EulerOddHighMass R M := by
  rw [vf919EulerOddSquarefreeCarrier_mass]
  unfold vf919EulerOddLowMass vf919EulerOddHighMass
    vf919EulerOddLowSites vf919EulerOddHighSites
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := vf919EulerOddSquarefreeCarrier R)
      (p := fun n => RHLean.Proof.canonicalCofactor n ≤ 3 * M)
      (f := realMoebiusStep)).symm

/-- Unique greatest-prime q reindex of the high-cofactor subcarrier. -/
def vf919EulerOddHighOwnerSites (R M q : ℕ) : Finset ℕ :=
  (vf919EulerOddHighSites R M).filter
    (fun n => RHLean.Proof.canonicalLargestPrimeFactor n = q)

/-- Signed q-smooth cofactor source: each n=m*q obeys P+(m)<q.
The q-bucket itself is finite, with no analytic estimate. -/
def vf919EulerOddHighOwnerCofactorMass (R M q : ℕ) : ℝ :=
  ∑ n ∈ vf919EulerOddHighOwnerSites R M q,
    realMoebiusStep (RHLean.Proof.canonicalCofactor n)

/-- Exact high-tail Fubini by actual greatest prime owners and their signed
cofactors. Distinct from treating every q as an unrestricted prime interval. -/
theorem odd_shell_high_tail_dual_by_gpf (R M : ℕ) (hR : 2 ≤ R) :
    vf919EulerOddHighMass R M =
      -∑ q ∈ Finset.range ((R + 1) ^ 2),
        vf919EulerOddHighOwnerCofactorMass R M q := by
  let S := vf919EulerOddHighSites R M
  let T := Finset.range ((R + 1) ^ 2)
  have hmaps :
      ∀ n ∈ S, RHLean.Proof.canonicalLargestPrimeFactor n ∈ T := by
    intro n hn
    have hcarrier := (Finset.mem_filter.mp hn).1
    have hnI := (Finset.mem_filter.mp hcarrier).1
    have hnhi := (Finset.mem_Ico.mp hnI).2
    have hnlo := (Finset.mem_Ico.mp hnI).1
    have hn1 : 1 < n := by nlinarith
    have hgle : RHLean.Proof.canonicalLargestPrimeFactor n ≤ n :=
      Nat.le_of_dvd (by omega)
        (RHLean.Proof.canonicalLargestPrimeFactor_dvd hn1)
    exact Finset.mem_range.mpr (lt_of_le_of_lt hgle hnhi)
  have hsign : ∀ n ∈ S,
      realMoebiusStep n =
        -realMoebiusStep (RHLean.Proof.canonicalCofactor n) := by
    intro n hn
    have hcarrier := (Finset.mem_filter.mp hn).1
    rcases Finset.mem_filter.mp hcarrier with ⟨hnI, _hodd, hsq⟩
    have hnlo := (Finset.mem_Ico.mp hnI).1
    have hn1 : 1 < n := by nlinarith
    have hmu := RHLean.Proof.canonicalSignedParent_moebius hsq hn1
    simpa [realMoebiusStep] using
      congrArg (fun z : ℤ => (z : ℝ)) hmu
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := RHLean.Proof.canonicalLargestPrimeFactor)
    hmaps (fun n => realMoebiusStep (RHLean.Proof.canonicalCofactor n))
  calc
    vf919EulerOddHighMass R M =
      ∑ n ∈ S, realMoebiusStep n := rfl
    _ = ∑ n ∈ S,
      -realMoebiusStep (RHLean.Proof.canonicalCofactor n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hsign n hn
    _ = -(∑ n ∈ S,
      realMoebiusStep (RHLean.Proof.canonicalCofactor n)) := by
        rw [Finset.sum_neg_distrib]
    _ = -(∑ q ∈ T,
        ∑ n ∈ S with RHLean.Proof.canonicalLargestPrimeFactor n = q,
          realMoebiusStep (RHLean.Proof.canonicalCofactor n)) := by
        rw [hfiber]
    _ = -(∑ q ∈ Finset.range ((R + 1) ^ 2),
        vf919EulerOddHighOwnerCofactorMass R M q) := by
          dsimp [T]
          congr 1
          apply Finset.sum_congr rfl
          intro q _
          rfl

#print axioms vf919ThreeDipole_disjoint
#print axioms vf919ThreeDipoleAlpha_parent
#print axioms vf919ThreeDipoleAlpha_child
#print axioms three_adic_dipole_defect_eq_zero
#print axioms three_adic_dipole_kernel_exact
#print axioms gpf_lt_prime_of_le_cutoff
#print axioms gpf_small_cofactor_unrestricted_prime_window
#print axioms odd_shell_hyperbola_split_eq
#print axioms odd_shell_high_tail_dual_by_gpf

end RHLean.Analysis
