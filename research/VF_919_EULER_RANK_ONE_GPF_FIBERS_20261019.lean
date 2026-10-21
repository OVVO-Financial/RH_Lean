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
    simpa [realMoebiusStep] using!
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
  have hT : vf919EulerOddShellComposite R =
      vf919EulerOddShellPrimes R -
        (∑ m ∈ Finset.range ((R + 1) ^ 2),
          realMoebiusStep m * vf919EulerOddGpfPrimeCount R m) := by
    dsimp [vf919EulerOddShellPrimes, vf919EulerOddShellComposite]
    linarith [hsource, hfiber]
  rw [hT]
  ring

#print axioms vf919EulerOddDyadic_centeredEnergy_exact
#print axioms vf919EulerOddDyadic_crossEnergy_rankOne
#print axioms vf919EulerOddDyadic_squareDifference_centered
#print axioms vf919EulerOddGpfFiber_prime_owner
#print axioms vf919EulerOddGpfFiber_unique_prime
#print axioms vf919EulerOddGpfFiber_mass
#print axioms vf919EulerOddSquarefreeCarrier_mass
#print axioms vf919EulerOddShell_gpfFiberDecomposition
#print axioms vf919EulerOddShell_compositePrime_viaGpf


/-! ## m = 1 is precisely the actual prime shell -/

/-- The largest-prime-factor-one fiber contains exactly the primes in the
true square shell. The prime 2 is absent for R >= 2. -/
theorem gpf_one_fiber_eq_prime_count (R : ℕ) (hR : 2 ≤ R) :
    vf919EulerOddGpfPrimeCount R 1 = vf919EulerOddShellPrimes R := by
  classical
  have hfiber :
      vf919EulerOddGpfFiber R 1 =
        (Finset.Ico (R ^ 2) ((R + 1) ^ 2)).filter Nat.Prime := by
    ext n
    constructor
    · intro hn
      rcases vf919EulerOddGpfFiber_prime_owner hR hn with
        ⟨q, hq, _hrough, hprod, hlo, hhi⟩
      have hnq : n = q := by simpa using! hprod.symm
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hnq.symm ▸ hq⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnI, hprime⟩
      have hlo := (Finset.mem_Ico.mp hnI).1
      have hn2 : n ≠ 2 := by nlinarith
      have hnodd : Odd n := hprime.odd_of_ne_two hn2
      have hqprime : (RHLean.Proof.canonicalLargestPrimeFactor n).Prime :=
        RHLean.Proof.canonicalLargestPrimeFactor_prime hprime.one_lt
      have hqdvd : RHLean.Proof.canonicalLargestPrimeFactor n ∣ n :=
        RHLean.Proof.canonicalLargestPrimeFactor_dvd hprime.one_lt
      have hq : RHLean.Proof.canonicalLargestPrimeFactor n = n :=
        (Nat.prime_dvd_prime_iff_eq hqprime hprime).mp hqdvd
      have hcofactor : RHLean.Proof.canonicalCofactor n = 1 := by
        unfold RHLean.Proof.canonicalCofactor
        rw [hq]
        exact Nat.div_self hprime.pos
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hnI, hnodd, hprime.squarefree⟩,
          hcofactor⟩
  unfold vf919EulerOddGpfPrimeCount vf919EulerOddShellPrimes
    vf919EulerOddBlockQ
  rw [hfiber]
  calc
    (((Finset.Ico (R ^ 2) ((R + 1) ^ 2)).filter Nat.Prime).card : ℝ) =
      ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
        if n.Prime then (1 : ℝ) else 0 := by
          rw [Finset.sum_boole]
    _ = ∑ n ∈ Finset.Ico (R ^ 2) ((R + 1) ^ 2),
          if Odd n then vf919EulerPrimeIndicator n else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hp : n.Prime
          · have hnlow := (Finset.mem_Ico.mp hn).1
            have hn2 : n ≠ 2 := by nlinarith
            have ho : Odd n := hp.odd_of_ne_two hn2
            simp [hp, ho, vf919EulerPrimeIndicator]
          · simp [hp, vf919EulerPrimeIndicator]

/-! ## Signed finite double-difference kernel: no moment estimate inserted -/

/-- Exact dyadic fiber collision kernel for the true greatest-prime carrier. -/
def vf919EulerGpfKernel (H m n : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    vf919EulerOddGpfPrimeCount R m * vf919EulerOddGpfPrimeCount R n

/-- Fluctuation of the canonical m-fiber relative to the m=1 prime shell.
The reference alpha need not be positive or an asymptotic prime-density model. -/
def vf919EulerGpfDelta (R m : ℕ) (alpha : ℕ → ℝ) : ℝ :=
  vf919EulerOddGpfPrimeCount R m -
    alpha m * vf919EulerOddGpfPrimeCount R 1

/-- Double-difference kernel: two independent fiber-coordinate subtractions
inside the product, before any absolute values are used. -/
def vf919EulerGpfDeltaKernel (H m n : ℕ) (alpha : ℕ → ℝ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    vf919EulerGpfDelta R m alpha * vf919EulerGpfDelta R n alpha

/-- Finite signed density defect. Setting this equal to zero is a separate
explicit hypothesis, not an unconditional Euler-product theorem. -/
def vf919EulerGpfDefect (M : Finset ℕ) (alpha : ℕ → ℝ) : ℝ :=
  ∑ m ∈ M, realMoebiusStep m * alpha m

def vf919EulerGpfWeightedResponse (M : Finset ℕ) (R : ℕ) : ℝ :=
  ∑ m ∈ M, realMoebiusStep m * vf919EulerOddGpfPrimeCount R m

def vf919EulerGpfCenteredResponse
    (M : Finset ℕ) (alpha : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ m ∈ M, realMoebiusStep m * vf919EulerGpfDelta R m alpha

/-- The exact vector decomposition whose square gives the drift, the
mixed covariance, and the fully compensated signed quadratic form. -/
theorem vf919EulerGpf_weightedResponse_eq_delta_add_defect
    (M : Finset ℕ) (alpha : ℕ → ℝ) (R : ℕ) :
    vf919EulerGpfWeightedResponse M R =
      vf919EulerGpfCenteredResponse M alpha R +
        vf919EulerGpfDefect M alpha *
          vf919EulerOddGpfPrimeCount R 1 := by
  unfold vf919EulerGpfWeightedResponse
    vf919EulerGpfCenteredResponse vf919EulerGpfDefect
  calc
    (∑ m ∈ M, realMoebiusStep m * vf919EulerOddGpfPrimeCount R m) =
      ∑ m ∈ M,
        (realMoebiusStep m * vf919EulerGpfDelta R m alpha +
          (realMoebiusStep m * alpha m) *
            vf919EulerOddGpfPrimeCount R 1) := by
            apply Finset.sum_congr rfl
            intro m _
            unfold vf919EulerGpfDelta
            ring
    _ = (∑ m ∈ M, realMoebiusStep m * vf919EulerGpfDelta R m alpha) +
        (∑ m ∈ M, (realMoebiusStep m * alpha m) *
          vf919EulerOddGpfPrimeCount R 1) := by
            rw [Finset.sum_add_distrib]
    _ = _ := by rw [← Finset.sum_mul]

/-- Purely finite Fubini/Gram identity; applies to any real fiber field.
No PNT, variance, or square-root cancellation hypothesis is present. -/
private theorem vf919EulerGpf_finiteKernel_quad
    (H : ℕ) (M : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ m ∈ M, ∑ n ∈ M,
      realMoebiusStep m * realMoebiusStep n *
        (∑ R ∈ Finset.Ico H (2 * H), F R m * F R n)) =
      ∑ R ∈ Finset.Ico H (2 * H),
        (∑ m ∈ M, realMoebiusStep m * F R m) ^ 2 := by
  calc
    (∑ m ∈ M, ∑ n ∈ M,
      realMoebiusStep m * realMoebiusStep n *
        (∑ R ∈ Finset.Ico H (2 * H), F R m * F R n)) =
        ∑ m ∈ M, ∑ n ∈ M, ∑ R ∈ Finset.Ico H (2 * H),
          (realMoebiusStep m * F R m) * (realMoebiusStep n * F R n) := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro R _
            ring
    _ = ∑ m ∈ M, ∑ R ∈ Finset.Ico H (2 * H), ∑ n ∈ M,
          (realMoebiusStep m * F R m) * (realMoebiusStep n * F R n) := by
            apply Finset.sum_congr rfl
            intro m _
            exact Finset.sum_comm
    _ = ∑ R ∈ Finset.Ico H (2 * H), ∑ m ∈ M, ∑ n ∈ M,
          (realMoebiusStep m * F R m) * (realMoebiusStep n * F R n) :=
            Finset.sum_comm
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          (∑ m ∈ M, realMoebiusStep m * F R m) ^ 2 := by
            apply Finset.sum_congr rfl
            intro R _
            rw [pow_two, Finset.sum_mul_sum]

theorem vf919EulerGpfKernel_quadratic
    (H : ℕ) (M : Finset ℕ) :
    (∑ m ∈ M, ∑ n ∈ M,
      realMoebiusStep m * realMoebiusStep n *
        vf919EulerGpfKernel H m n) =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerGpfWeightedResponse M R) ^ 2 := by
  simpa [vf919EulerGpfKernel, vf919EulerGpfWeightedResponse] using!
    vf919EulerGpf_finiteKernel_quad H M
      (fun R m => vf919EulerOddGpfPrimeCount R m)

theorem vf919EulerGpfDeltaKernel_quadratic
    (H : ℕ) (M : Finset ℕ) (alpha : ℕ → ℝ) :
    (∑ m ∈ M, ∑ n ∈ M,
      realMoebiusStep m * realMoebiusStep n *
        vf919EulerGpfDeltaKernel H m n alpha) =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerGpfCenteredResponse M alpha R) ^ 2 := by
  simpa [vf919EulerGpfDeltaKernel, vf919EulerGpfCenteredResponse] using!
    vf919EulerGpf_finiteKernel_quad H M
      (fun R m => vf919EulerGpfDelta R m alpha)

/-- Exact compensated kernel decomposition. In particular, killing the
rank-one term inside each K^Delta(m,n) does NOT remove the scalar defect
or the signed mixed term unless additional hypotheses are supplied. -/
theorem dyadic_kernel_double_difference_eq
    (H : ℕ) (M : Finset ℕ) (alpha : ℕ → ℝ) :
    (∑ m ∈ M, ∑ n ∈ M,
        realMoebiusStep m * realMoebiusStep n *
          vf919EulerGpfKernel H m n) =
      (∑ m ∈ M, ∑ n ∈ M,
        realMoebiusStep m * realMoebiusStep n *
          vf919EulerGpfDeltaKernel H m n alpha) +
      2 * vf919EulerGpfDefect M alpha *
        (∑ R ∈ Finset.Ico H (2 * H),
          vf919EulerOddGpfPrimeCount R 1 *
            vf919EulerGpfCenteredResponse M alpha R) +
      vf919EulerGpfDefect M alpha ^ 2 *
        (∑ R ∈ Finset.Ico H (2 * H),
          vf919EulerOddGpfPrimeCount R 1 ^ 2) := by
  rw [vf919EulerGpfKernel_quadratic,
    vf919EulerGpfDeltaKernel_quadratic]
  calc
    (∑ R ∈ Finset.Ico H (2 * H),
        vf919EulerGpfWeightedResponse M R ^ 2) =
      ∑ R ∈ Finset.Ico H (2 * H),
        (vf919EulerGpfCenteredResponse M alpha R +
          vf919EulerGpfDefect M alpha *
            vf919EulerOddGpfPrimeCount R 1) ^ 2 := by
            apply Finset.sum_congr rfl
            intro R _
            rw [vf919EulerGpf_weightedResponse_eq_delta_add_defect]
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro R _
      ring

/-- The normalized base coordinate has identically zero compensated row
and column, even before summing over R. -/
theorem vf919EulerGpfDeltaKernel_one_zero
    (H : ℕ) (alpha : ℕ → ℝ) (hbase : alpha 1 = 1) (m : ℕ) :
    vf919EulerGpfDeltaKernel H 1 m alpha = 0 ∧
      vf919EulerGpfDeltaKernel H m 1 alpha = 0 := by
  simp [vf919EulerGpfDeltaKernel, vf919EulerGpfDelta, hbase]

/-- If (and only if explicitly assumed) the finite density defect vanishes,
the entire signed covariance becomes the pure compensated kernel. -/
theorem dyadic_kernel_double_difference_of_zero_defect
    (H : ℕ) (M : Finset ℕ) (alpha : ℕ → ℝ)
    (hzero : vf919EulerGpfDefect M alpha = 0) :
    (∑ m ∈ M, ∑ n ∈ M,
        realMoebiusStep m * realMoebiusStep n *
          vf919EulerGpfKernel H m n) =
      ∑ m ∈ M, ∑ n ∈ M,
        realMoebiusStep m * realMoebiusStep n *
          vf919EulerGpfDeltaKernel H m n alpha := by
  rw [dyadic_kernel_double_difference_eq H M alpha]
  simp [hzero]

/-! ## Genuine greatest-prime preserving local parent/child compensation -/

/-- Multiplying a positive cofactor d by a prime p below its GREATEST
prime factor does not alter the greatest prime factor. No false condition
d < p is used. This statement remains true if p divides d, although the
Möbius sign reversal requires the additional fresh-prime condition. -/
theorem gpf_mul_prime_of_lt_gpf
    {d p : ℕ} (hd : 1 < d) (hp : p.Prime)
    (hplt : p < RHLean.Proof.canonicalLargestPrimeFactor d) :
    RHLean.Proof.canonicalLargestPrimeFactor (p * d) =
      RHLean.Proof.canonicalLargestPrimeFactor d := by
  let q := RHLean.Proof.canonicalLargestPrimeFactor d
  have hqprime : q.Prime := RHLean.Proof.canonicalLargestPrimeFactor_prime hd
  have hqdvd : q ∣ d := RHLean.Proof.canonicalLargestPrimeFactor_dvd hd
  have hdne : d ≠ 0 := by omega
  have hprodne : p * d ≠ 0 := Nat.mul_ne_zero hp.ne_zero hdne
  have hprodgt : 1 < p * d := by nlinarith [hp.two_le]
  have hqprod : q ∣ p * d := by
    rcases hqdvd with ⟨k, hk⟩
    refine ⟨p * k, ?_⟩
    rw [hk]
    ring
  have hqmem : q ∈ (p * d).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hqprod, hprodne⟩
  have hmax_d : ∀ r ∈ d.primeFactors, r ≤ q := by
    intro r hr
    dsimp [q]
    unfold RHLean.Proof.canonicalLargestPrimeFactor
    rw [dite_eq_left hd]
    exact Finset.le_max' d.primeFactors r hr
  have hmax_prod : ∀ r ∈ (p * d).primeFactors, r ≤ q := by
    intro r hr
    have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdiv : r ∣ p * d := Nat.dvd_of_mem_primeFactors hr
    rcases hrprime.dvd_mul.mp hrdiv with hrp | hrd
    · have heq : r = p := (Nat.prime_dvd_prime_iff_eq hrprime hp).mp hrp
      exact heq.le.trans hplt.le
    · exact hmax_d r (Nat.mem_primeFactors.mpr ⟨hrprime, hrd, hdne⟩)
  have hres : RHLean.Proof.canonicalLargestPrimeFactor (p * d) = q := by
    unfold RHLean.Proof.canonicalLargestPrimeFactor
    rw [dite_eq_left hprodgt]
    exact ((p * d).primeFactors.max'_eq_iff
      (Nat.nonempty_primeFactors.mpr hprodgt) q).2
        ⟨hqmem, hmax_prod⟩
  exact hres

/-- Both the parent d and child p*d use exactly the same strict admissibility
threshold q > P+(d) in every prime window and every shell. -/
theorem vf919EulerGpfDipole_commonThreshold
    {d p : ℕ} (hd : 1 < d) (hp : p.Prime)
    (hplt : p < RHLean.Proof.canonicalLargestPrimeFactor d) (q : ℕ) :
    RHLean.Proof.canonicalLargestPrimeFactor (p * d) < q ↔
      RHLean.Proof.canonicalLargestPrimeFactor d < q := by
  rw [gpf_mul_prime_of_lt_gpf hd hp hplt]

/-- The local signs reverse ONLY when p is fresh in d. Without this
hypothesis p*d is nonsquarefree and its Möbius weight is zero. -/
theorem vf919EulerGpfDipole_moebius
    {d p : ℕ} (hp : p.Prime) (hfresh : ¬ p ∣ d) :
    realMoebiusStep (p * d) = -realMoebiusStep d := by
  have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hfresh
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  unfold realMoebiusStep
  rw [hmu, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- The cutoff-matched local relative fiber fluctuation. It has no
asserted pointwise/squared cancellation estimate. -/
def vf919EulerGpfLocalDipole
    (R d p : ℕ) (beta : ℝ) : ℝ :=
  vf919EulerOddGpfPrimeCount R (p * d) -
    beta * vf919EulerOddGpfPrimeCount R d

#print axioms gpf_one_fiber_eq_prime_count
#print axioms vf919EulerGpf_weightedResponse_eq_delta_add_defect
#print axioms vf919EulerGpfKernel_quadratic
#print axioms vf919EulerGpfDeltaKernel_quadratic
#print axioms dyadic_kernel_double_difference_eq
#print axioms vf919EulerGpfDeltaKernel_one_zero
#print axioms dyadic_kernel_double_difference_of_zero_defect
#print axioms gpf_mul_prime_of_lt_gpf
#print axioms vf919EulerGpfDipole_commonThreshold
#print axioms vf919EulerGpfDipole_moebius

end RHLean.Analysis
