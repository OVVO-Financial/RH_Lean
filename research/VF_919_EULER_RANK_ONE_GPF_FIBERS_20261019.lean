import «research.VF_919_EULER_ODD_CARRIER_PRIME_ROW_20261019»
import RHLean.Proof.ReplacementFibreCofactorWindows

/-!
# Centered signed covariance and canonical greatest-prime-factor fibers

For every deterministic real baseline L_R, centering the signed composite
mass T_R and the actual odd prime count Q_R by the SAME baseline cancels
identically inside S_R=T_R-Q_R. No PNT input is required.

The odd squarefree carrier has an exact finite Fubini by the canonical
cofactor m=n/P+(n). The repository already proves canonicalSignedParent_moebius
and the strict greatest-prime cofactor cutoff P+(m)<P+(n). We reuse both.
The fibers are distinct genuine greatest-prime-owner prime occurrences,
not unrestricted pairs (m,q) with mq in the shell.

Nothing here proves a quantitative 7/8 signed moment bound.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

def vf919EulerOddShellComposite (R : ℕ) : ℝ :=
  vf919EulerOddBlockA R ((R + 1) ^ 2) +
    vf919EulerOddBlockH R ((R + 1) ^ 2)

def vf919EulerOddShellPrimes (R : ℕ) : ℝ :=
  vf919EulerOddBlockQ R ((R + 1) ^ 2)

def vf919EulerOddShellEnergy (R : ℕ) : ℝ :=
  (vf919EulerOddShellComposite R - vf919EulerOddShellPrimes R) ^ 2

def vf919EulerOddDyadicEnergy (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H), vf919EulerOddShellEnergy R

def vf919EulerOddDyadicCenteredEnergy (H : ℕ) (L : ℕ → ℝ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    ((vf919EulerOddShellComposite R - L R) -
      (vf919EulerOddShellPrimes R - L R)) ^ 2

/-- A shared rank-one drift cancels exactly, with no asymptotic assumption. -/
theorem vf919EulerOddDyadic_centeredEnergy_exact
    (H : ℕ) (L : ℕ → ℝ) :
    vf919EulerOddDyadicEnergy H =
      vf919EulerOddDyadicCenteredEnergy H L := by
  unfold vf919EulerOddDyadicEnergy
    vf919EulerOddDyadicCenteredEnergy vf919EulerOddShellEnergy
  apply Finset.sum_congr rfl
  intro R _
  ring

/-- The complete centered cross-energy bill retains all drift/fluctuation
terms; the mixed terms cannot be thrown away without a further estimate. -/
theorem vf919EulerOddDyadic_crossEnergy_rankOne
    (H : ℕ) (L : ℕ → ℝ) :
    2 * ∑ R ∈ Finset.Ico H (2 * H),
      vf919EulerOddShellComposite R * vf919EulerOddShellPrimes R =
      2 * ∑ R ∈ Finset.Ico H (2 * H), L R ^ 2 +
      2 * ∑ R ∈ Finset.Ico H (2 * H),
        L R * (vf919EulerOddShellComposite R - L R) +
      2 * ∑ R ∈ Finset.Ico H (2 * H),
        L R * (vf919EulerOddShellPrimes R - L R) +
      2 * ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerOddShellComposite R - L R) *
          (vf919EulerOddShellPrimes R - L R) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  ring

/-- The square-difference identity after drift extraction, without
separate absolute values for the prime/composite interaction. -/
theorem vf919EulerOddDyadic_squareDifference_centered
    (H : ℕ) (L : ℕ → ℝ) :
    vf919EulerOddDyadicEnergy H =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerOddShellComposite R - L R) ^ 2 +
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerOddShellPrimes R - L R) ^ 2 -
      2 * ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerOddShellComposite R - L R) *
          (vf919EulerOddShellPrimes R - L R) := by
  rw [vf919EulerOddDyadic_centeredEnergy_exact H L]
  unfold vf919EulerOddDyadicCenteredEnergy
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R _
  ring

/-! ## Actual odd squarefree greatest-prime-factor fibers -/

/-- The full, exact odd squarefree square shell (Möbius-zero sites excluded). -/
def vf919EulerOddSquarefreeCarrier (R : ℕ) : Finset ℕ :=
  (Finset.Ico (R ^ 2) ((R + 1) ^ 2)).filter
    (fun n => Odd n ∧ Squarefree n)

/-- Unique canonical-cofactor m fiber in the odd squarefree shell.
Every occurrence has prime q=P+(n) and n=m*q; this is a prime count,
with no unrestricted m*q overcounting. -/
def vf919EulerOddGpfFiber (R m : ℕ) : Finset ℕ :=
  (vf919EulerOddSquarefreeCarrier R).filter
    (fun n => RHLean.Proof.canonicalCofactor n = m)

def vf919EulerOddGpfPrimeCount (R m : ℕ) : ℝ :=
  ((vf919EulerOddGpfFiber R m).card : ℝ)

/-- Every fiber site has a *genuine* unique greatest prime q and the crucial
P+(m)<q cutoff, even when the numerical cofactor m is larger than q. -/
theorem vf919EulerOddGpfFiber_prime_owner
    {R m n : ℕ} (hR : 2 ≤ R)
    (hn : n ∈ vf919EulerOddGpfFiber R m) :
    ∃ q : ℕ, q.Prime ∧
      RHLean.Proof.canonicalLargestPrimeFactor m < q ∧
      m * q = n ∧ R ^ 2 ≤ n ∧ n < (R + 1) ^ 2 := by
  rcases Finset.mem_filter.mp hn with ⟨hcarrier, hm⟩
  rcases Finset.mem_filter.mp hcarrier with ⟨hnI, _hodd, hsq⟩
  rcases Finset.mem_Ico.mp hnI with ⟨hnlo, hnhi⟩
  have hn1 : 1 < n := by nlinarith
  let q := RHLean.Proof.canonicalLargestPrimeFactor n
  have hq : q.Prime := RHLean.Proof.canonicalLargestPrimeFactor_prime hn1
  have hrough := RHLean.Proof.canonicalLargestPrimeFactor_canonicalCofactor_lt_of_squarefree
    hn1 hsq
  have hprod := RHLean.Proof.canonicalCofactor_mul_largestPrimeFactor hn1
  rw [hm] at hrough hprod
  exact ⟨q, hq, hrough, hprod, hnlo, hnhi⟩

/-- The greatest-prime coordinate is injective on a fixed cofactor fiber.
Thus fiber cardinality really counts distinct prime arrivals q. -/
theorem vf919EulerOddGpfFiber_unique_prime
    {R m n₁ n₂ : ℕ} (hR : 2 ≤ R)
    (h₁ : n₁ ∈ vf919EulerOddGpfFiber R m)
    (h₂ : n₂ ∈ vf919EulerOddGpfFiber R m)
    (hq : RHLean.Proof.canonicalLargestPrimeFactor n₁ =
      RHLean.Proof.canonicalLargestPrimeFactor n₂) :
    n₁ = n₂ := by
  have hmem₁ := Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1
  have hmem₂ := Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1
  have hlow₁ := (Finset.mem_Ico.mp hmem₁.1).1
  have hlow₂ := (Finset.mem_Ico.mp hmem₂.1).1
  have hn₁ : 1 < n₁ := by nlinarith
  have hn₂ : 1 < n₂ := by nlinarith
  have hp₁ := RHLean.Proof.canonicalCofactor_mul_largestPrimeFactor hn₁
  have hp₂ := RHLean.Proof.canonicalCofactor_mul_largestPrimeFactor hn₂
  rw [(Finset.mem_filter.mp h₁).2] at hp₁
  rw [(Finset.mem_filter.mp h₂).2] at hp₂
  calc
    n₁ = m * RHLean.Proof.canonicalLargestPrimeFactor n₁ := hp₁.symm
    _ = m * RHLean.Proof.canonicalLargestPrimeFactor n₂ := by rw [hq]
    _ = n₂ := hp₂

/-- At the true odd squarefree sites, the canonical signed-parent relation
gives exactly minus mu(m) in every fixed-cofactor fiber. -/
theorem vf919EulerOddGpfFiber_mass
    (R m : ℕ) (hR : 2 ≤ R) :
    (∑ n ∈ vf919EulerOddGpfFiber R m, realMoebiusStep n) =
      -realMoebiusStep m * vf919EulerOddGpfPrimeCount R m := by
  have hsign : ∀ n ∈ vf919EulerOddGpfFiber R m,
      realMoebiusStep n = -realMoebiusStep m := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hcarrier, hm⟩
    rcases Finset.mem_filter.mp hcarrier with ⟨hnI, _hodd, hsq⟩
    have hnlo := (Finset.mem_Ico.mp hnI).1
    have hn1 : 1 < n := by nlinarith
    have hmu : ArithmeticFunction.moebius n =
        -(ArithmeticFunction.moebius m) := by
      rw [RHLean.Proof.canonicalSignedParent_moebius hsq hn1, hm]
    simpa [realMoebiusStep] using
      congrArg (fun z : ℤ => (z : ℝ)) hmu
  calc
    (∑ n ∈ vf919EulerOddGpfFiber R m, realMoebiusStep n) =
      ∑ _n ∈ vf919EulerOddGpfFiber R m, -realMoebiusStep m := by
        exact Finset.sum_congr rfl hsign
    _ = -realMoebiusStep m * vf919EulerOddGpfPrimeCount R m := by
      simp [vf919EulerOddGpfPrimeCount, mul_comm]

/-- The odd squarefree support is literally the odd Möbius shell mass. -/
theorem vf919EulerOddSquarefreeCarrier_mass
    (R : ℕ) :
    vf919EulerOddBlockS R ((R + 1) ^ 2) =
      ∑ n ∈ vf919EulerOddSquarefreeCarrier R, realMoebiusStep n := by
  unfold vf919EulerOddBlockS vf919EulerOddSquarefreeCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hodd : Odd n
  · by_cases hsq : Squarefree n
    · simp [hodd, hsq]
    · have hzero : realMoebiusStep n = 0 := by
        have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        simp [realMoebiusStep, hz]
      simp [hodd, hsq, hzero]
  · simp [hodd]

/-- COMPLETE finite canonical-prime Fubini: each odd squarefree shell site
belongs to one and only one canonical cofactor m and the sign flips there.
This is the exact arithmetic m-fiber representation of T_R-Q_R. -/
theorem vf919EulerOddShell_gpfFiberDecomposition
    (R : ℕ) (hR : 2 ≤ R) :
    vf919EulerOddBlockS R ((R + 1) ^ 2) =
      -∑ m ∈ Finset.range ((R + 1) ^ 2),
        realMoebiusStep m * vf919EulerOddGpfPrimeCount R m := by
  let S := vf919EulerOddSquarefreeCarrier R
  let T := Finset.range ((R + 1) ^ 2)
  have hmaps : ∀ n ∈ S, RHLean.Proof.canonicalCofactor n ∈ T := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    have hnhi := (Finset.mem_Ico.mp hnI).2
    have hle : RHLean.Proof.canonicalCofactor n ≤ n := by
      unfold RHLean.Proof.canonicalCofactor
      exact Nat.div_le_self _ _
    exact Finset.mem_range.mpr (lt_of_le_of_lt hle hnhi)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := RHLean.Proof.canonicalCofactor)
    hmaps (fun n => realMoebiusStep n)
  calc
    vf919EulerOddBlockS R ((R + 1) ^ 2) =
      ∑ n ∈ S, realMoebiusStep n :=
        vf919EulerOddSquarefreeCarrier_mass R
    _ = ∑ m ∈ T, ∑ n ∈ S with
        RHLean.Proof.canonicalCofactor n = m, realMoebiusStep n :=
          hfiber.symm
    _ = ∑ m ∈ T,
        -realMoebiusStep m * vf919EulerOddGpfPrimeCount R m := by
          apply Finset.sum_congr rfl
          intro m _
          exact vf919EulerOddGpfFiber_mass R m hR
    _ = -(∑ m ∈ Finset.range ((R + 1) ^ 2),
        realMoebiusStep m * vf919EulerOddGpfPrimeCount R m) := by
          dsimp [T]
          simp only [neg_mul, Finset.sum_neg_distrib]

/-- Composite/prime cross term in *canonical prime/cofactor coordinates*.
The -Q² correction explicitly removes the prime-only m=1 source.
An additional theorem can identify that source with the ordinary Q_R. -/
theorem vf919EulerOddShell_compositePrime_viaGpf
    (R : ℕ) (hR : 2 ≤ R) :
    -(vf919EulerOddShellPrimes R *
        vf919EulerOddShellComposite R) =
      vf919EulerOddShellPrimes R *
        ((∑ m ∈ Finset.range ((R + 1) ^ 2),
            realMoebiusStep m * vf919EulerOddGpfPrimeCount R m) -
          vf919EulerOddShellPrimes R) := by
  have hsource := vf919EulerOddBlock_source_partition R ((R + 1) ^ 2)
  have hfiber := vf919EulerOddShell_gpfFiberDecomposition R hR
  dsimp [vf919EulerOddShellPrimes, vf919EulerOddShellComposite]
  dsimp [vf919EulerOddShellPrimes, vf919EulerOddShellComposite] at *
  nlinarith

#print axioms vf919EulerOddDyadic_centeredEnergy_exact
#print axioms vf919EulerOddDyadic_crossEnergy_rankOne
#print axioms vf919EulerOddDyadic_squareDifference_centered
#print axioms vf919EulerOddGpfFiber_prime_owner
#print axioms vf919EulerOddGpfFiber_unique_prime
#print axioms vf919EulerOddGpfFiber_mass
#print axioms vf919EulerOddSquarefreeCarrier_mass
#print axioms vf919EulerOddShell_gpfFiberDecomposition
#print axioms vf919EulerOddShell_compositePrime_viaGpf

end RHLean.Analysis
